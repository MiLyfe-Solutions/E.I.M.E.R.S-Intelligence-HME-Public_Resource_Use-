import V185TrunkScan22Chunk306

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2739026 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_2739026 : Nat := 118140960795 + 2739026 * 2 ^ 59
def prefixEnd_2739026 : Nat := 4983230072969 + 3 ^ 40 * 2739026 * 2
def baseEnd_2739026 : Nat := 937624575441270521252303

theorem tailTrace_2739026 : CollatzResearch.WordTrace tailWord_2739026 prefixEnd_2739026 937624575441270521252303 := by
  unfold tailWord_2739026
  simp only [CollatzResearch.WordTrace]
  refine ⟨24975121343746016310843233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66600323583322710162248621 24975121343746016310843233)
  ·
    refine ⟨18731341007809512233132425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24975121343746016310843233 18731341007809512233132425)
    ·
      refine ⟨14048505755857134174849319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18731341007809512233132425 14048505755857134174849319)
      ·
        refine ⟨21072758633785701262273979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14048505755857134174849319 21072758633785701262273979)
        ·
          refine ⟨31609137950678551893410969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21072758633785701262273979 31609137950678551893410969)
          ·
            refine ⟨23706853463008913920058227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31609137950678551893410969 23706853463008913920058227)
            ·
              refine ⟨35560280194513370880087341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23706853463008913920058227 35560280194513370880087341)
              ·
                refine ⟨13335105072942514080032753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35560280194513370880087341 13335105072942514080032753)
                ·
                  refine ⟨10001328804706885560024565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13335105072942514080032753 10001328804706885560024565)
                  ·
                    refine ⟨937624575441270521252303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10001328804706885560024565 937624575441270521252303)
                    ·
                      rfl

theorem cell22_2739026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_2739026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739026 prefixEnd_2739026 := by exact prefixLift 2739026
  have htrace : WordTrace (prefixWord ++ tailWord_2739026) baseStart_2739026 baseEnd_2739026 := by
    simpa [prefixWord, tailWord_2739026, baseEnd_2739026] using wordTrace_append hprefix tailTrace_2739026
  have hstable : (prefixWord ++ tailWord_2739026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739026).length < 2 ^ (prefixWord ++ tailWord_2739026).sum := by decide
  have hdescent : baseEnd_2739026 < baseStart_2739026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739058 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_2739058 : Nat := 118140960795 + 2739058 * 2 ^ 59
def prefixEnd_2739058 : Nat := 4983230072969 + 3 ^ 40 * 2739058 * 2
def baseEnd_2739058 : Nat := 937635529695233104452205

theorem tailTrace_2739058 : CollatzResearch.WordTrace tailWord_2739058 prefixEnd_2739058 937635529695233104452205 := by
  unfold tailWord_2739058
  simp only [CollatzResearch.WordTrace]
  refine ⟨24975413127717033677134457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66601101673912089805691885 24975413127717033677134457)
  ·
    refine ⟨18731559845787775257850843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24975413127717033677134457 18731559845787775257850843)
    ·
      refine ⟨28097339768681662886776265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18731559845787775257850843 28097339768681662886776265)
      ·
        refine ⟨21073004826511247165082199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28097339768681662886776265 21073004826511247165082199)
        ·
          refine ⟨31609507239766870747623299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21073004826511247165082199 31609507239766870747623299)
          ·
            refine ⟨47414260859650306121434949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31609507239766870747623299 47414260859650306121434949)
            ·
              refine ⟨8890173911184432397769053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47414260859650306121434949 8890173911184432397769053)
              ·
                refine ⟨3333815216694162149163395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8890173911184432397769053 3333815216694162149163395)
                ·
                  refine ⟨5000722825041243223745093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333815216694162149163395 5000722825041243223745093)
                  ·
                    refine ⟨937635529695233104452205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5000722825041243223745093 937635529695233104452205)
                    ·
                      rfl

theorem cell22_2739058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_2739058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739058 prefixEnd_2739058 := by exact prefixLift 2739058
  have htrace : WordTrace (prefixWord ++ tailWord_2739058) baseStart_2739058 baseEnd_2739058 := by
    simpa [prefixWord, tailWord_2739058, baseEnd_2739058] using wordTrace_append hprefix tailTrace_2739058
  have hstable : (prefixWord ++ tailWord_2739058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739058).length < 2 ^ (prefixWord ++ tailWord_2739058).sum := by decide
  have hdescent : baseEnd_2739058 < baseStart_2739058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739101 : List Nat := [1, 4, 2, 1, 2, 1, 1, 10]
def baseStart_2739101 : Nat := 118140960795 + 2739101 * 2 ^ 59
def prefixEnd_2739101 : Nat := 4983230072969 + 3 ^ 40 * 2739101 * 2
def baseEnd_2739101 : Nat := 104183361052666147291897

theorem tailTrace_2739101 : CollatzResearch.WordTrace tailWord_2739101 prefixEnd_2739101 104183361052666147291897 := by
  unfold tailWord_2739101
  simp only [CollatzResearch.WordTrace]
  refine ⟨99903220849712353052353157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66602147233141568701568771 99903220849712353052353157)
  ·
    refine ⟨18731853909321066197316217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99903220849712353052353157 18731853909321066197316217)
    ·
      refine ⟨14048890431990799647987163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18731853909321066197316217 14048890431990799647987163)
      ·
        refine ⟨21073335647986199471980745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14048890431990799647987163 21073335647986199471980745)
        ·
          refine ⟨15805001735989649603985559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21073335647986199471980745 15805001735989649603985559)
          ·
            refine ⟨23707502603984474405978339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15805001735989649603985559 23707502603984474405978339)
            ·
              refine ⟨35561253905976711608967509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23707502603984474405978339 35561253905976711608967509)
              ·
                refine ⟨104183361052666147291897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35561253905976711608967509 104183361052666147291897)
                ·
                  rfl

theorem cell22_2739101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 10].length) (baseStart_2739101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739101 prefixEnd_2739101 := by exact prefixLift 2739101
  have htrace : WordTrace (prefixWord ++ tailWord_2739101) baseStart_2739101 baseEnd_2739101 := by
    simpa [prefixWord, tailWord_2739101, baseEnd_2739101] using wordTrace_append hprefix tailTrace_2739101
  have hstable : (prefixWord ++ tailWord_2739101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739101).length < 2 ^ (prefixWord ++ tailWord_2739101).sum := by decide
  have hdescent : baseEnd_2739101 < baseStart_2739101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739103 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 2, 4]
def baseStart_2739103 : Nat := 118140960795 + 2739103 * 2 ^ 59
def prefixEnd_2739103 : Nat := 4983230072969 + 3 ^ 40 * 2739103 * 2
def baseEnd_2739103 : Nat := 937650934114867987077067

theorem tailTrace_2739103 : CollatzResearch.WordTrace tailWord_2739103 prefixEnd_2739103 937650934114867987077067 := by
  unfold tailWord_2739103
  simp only [CollatzResearch.WordTrace]
  refine ⟨99903293795705107393925963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66602195863803404929283975 99903293795705107393925963)
  ·
    refine ⟨149854940693557661090888945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99903293795705107393925963 149854940693557661090888945)
    ·
      refine ⟨112391205520168245818166709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149854940693557661090888945 112391205520168245818166709)
      ·
        refine ⟨10536675517515773045453129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112391205520168245818166709 10536675517515773045453129)
        ·
          refine ⟨7902506638136829784089847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10536675517515773045453129 7902506638136829784089847)
          ·
            refine ⟨11853759957205244676134771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7902506638136829784089847 11853759957205244676134771)
            ·
              refine ⟨17780639935807867014202157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11853759957205244676134771 17780639935807867014202157)
              ·
                refine ⟨6667739975927950130325809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17780639935807867014202157 6667739975927950130325809)
                ·
                  refine ⟨5000804981945962597744357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6667739975927950130325809 5000804981945962597744357)
                  ·
                    refine ⟨937650934114867987077067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5000804981945962597744357 937650934114867987077067)
                    ·
                      rfl

theorem cell22_2739103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_2739103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739103 prefixEnd_2739103 := by exact prefixLift 2739103
  have htrace : WordTrace (prefixWord ++ tailWord_2739103) baseStart_2739103 baseEnd_2739103 := by
    simpa [prefixWord, tailWord_2739103, baseEnd_2739103] using wordTrace_append hprefix tailTrace_2739103
  have hstable : (prefixWord ++ tailWord_2739103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739103).length < 2 ^ (prefixWord ++ tailWord_2739103).sum := by decide
  have hdescent : baseEnd_2739103 < baseStart_2739103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739118 : List Nat := [4, 1, 5, 12]
def baseStart_2739118 : Nat := 118140960795 + 2739118 * 2 ^ 59
def prefixEnd_2739118 : Nat := 4983230072969 + 3 ^ 40 * 2739118 * 2
def baseEnd_2739118 : Nat := 1286222316764626814749

theorem tailTrace_2739118 : CollatzResearch.WordTrace tailWord_2739118 prefixEnd_2739118 1286222316764626814749 := by
  unfold tailWord_2739118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12487980111331345619465251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66602560593767176637148005 12487980111331345619465251)
  ·
    refine ⟨18731970166997018429197877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12487980111331345619465251 18731970166997018429197877)
    ·
      refine ⟨1756122203155970477737301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18731970166997018429197877 1756122203155970477737301)
      ·
        refine ⟨1286222316764626814749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1756122203155970477737301 1286222316764626814749)
        ·
          rfl

theorem cell22_2739118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 12].length) (baseStart_2739118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739118 prefixEnd_2739118 := by exact prefixLift 2739118
  have htrace : WordTrace (prefixWord ++ tailWord_2739118) baseStart_2739118 baseEnd_2739118 := by
    simpa [prefixWord, tailWord_2739118, baseEnd_2739118] using wordTrace_append hprefix tailTrace_2739118
  have hstable : (prefixWord ++ tailWord_2739118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739118).length < 2 ^ (prefixWord ++ tailWord_2739118).sum := by decide
  have hdescent : baseEnd_2739118 < baseStart_2739118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739124 : List Nat := [2, 5, 2, 1, 1, 1, 4, 2, 4]
def baseStart_2739124 : Nat := 118140960795 + 2739124 * 2 ^ 59
def prefixEnd_2739124 : Nat := 4983230072969 + 3 ^ 40 * 2739124 * 2
def baseEnd_2739124 : Nat := 312552707614676977434001

theorem tailTrace_2739124 : CollatzResearch.WordTrace tailWord_2739124 prefixEnd_2739124 312552707614676977434001 := by
  unfold tailWord_2739124
  simp only [CollatzResearch.WordTrace]
  refine ⟨49952029864314513990220213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66602706485752685320293617 49952029864314513990220213)
  ·
    refine ⟨4683002799779485686583145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49952029864314513990220213 4683002799779485686583145)
    ·
      refine ⟨3512252099834614264937359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4683002799779485686583145 3512252099834614264937359)
      ·
        refine ⟨5268378149751921397406039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512252099834614264937359 5268378149751921397406039)
        ·
          refine ⟨7902567224627882096109059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5268378149751921397406039 7902567224627882096109059)
          ·
            refine ⟨11853850836941823144163589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7902567224627882096109059 11853850836941823144163589)
            ·
              refine ⟨2222597031926591839530673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11853850836941823144163589 2222597031926591839530673)
              ·
                refine ⟨1666947773944943879648005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222597031926591839530673 1666947773944943879648005)
                ·
                  refine ⟨312552707614676977434001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1666947773944943879648005 312552707614676977434001)
                  ·
                    rfl

theorem cell22_2739124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_2739124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739124 prefixEnd_2739124 := by exact prefixLift 2739124
  have htrace : WordTrace (prefixWord ++ tailWord_2739124) baseStart_2739124 baseEnd_2739124 := by
    simpa [prefixWord, tailWord_2739124, baseEnd_2739124] using wordTrace_append hprefix tailTrace_2739124
  have hstable : (prefixWord ++ tailWord_2739124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739124).length < 2 ^ (prefixWord ++ tailWord_2739124).sum := by decide
  have hdescent : baseEnd_2739124 < baseStart_2739124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739146 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_2739146 : Nat := 118140960795 + 2739146 * 2 ^ 59
def prefixEnd_2739146 : Nat := 4983230072969 + 3 ^ 40 * 2739146 * 2
def baseEnd_2739146 : Nat := 312555217964543402750645

theorem tailTrace_2739146 : CollatzResearch.WordTrace tailWord_2739146 prefixEnd_2739146 312555217964543402750645 := by
  unfold tailWord_2739146
  simp only [CollatzResearch.WordTrace]
  refine ⟨24976215533637331434435323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66603241423032883825160861 24976215533637331434435323)
  ·
    refine ⟨37464323300455997151652985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24976215533637331434435323 37464323300455997151652985)
    ·
      refine ⟨28098242475341997863739739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37464323300455997151652985 28098242475341997863739739)
      ·
        refine ⟨42147363713012996795609609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28098242475341997863739739 42147363713012996795609609)
        ·
          refine ⟨31610522784759747596707207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42147363713012996795609609 31610522784759747596707207)
          ·
            refine ⟨47415784177139621395060811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31610522784759747596707207 47415784177139621395060811)
            ·
              refine ⟨71123676265709432092591217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47415784177139621395060811 71123676265709432092591217)
              ·
                refine ⟨53342757199282074069443413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71123676265709432092591217 53342757199282074069443413)
                ·
                  refine ⟨312555217964543402750645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53342757199282074069443413 312555217964543402750645)
                  ·
                    rfl

theorem cell22_2739146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_2739146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739146 prefixEnd_2739146 := by exact prefixLift 2739146
  have htrace : WordTrace (prefixWord ++ tailWord_2739146) baseStart_2739146 baseEnd_2739146 := by
    simpa [prefixWord, tailWord_2739146, baseEnd_2739146] using wordTrace_append hprefix tailTrace_2739146
  have hstable : (prefixWord ++ tailWord_2739146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739146).length < 2 ^ (prefixWord ++ tailWord_2739146).sum := by decide
  have hdescent : baseEnd_2739146 < baseStart_2739146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739150 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_2739150 : Nat := 118140960795 + 2739150 * 2 ^ 59
def prefixEnd_2739150 : Nat := 4983230072969 + 3 ^ 40 * 2739150 * 2
def baseEnd_2739150 : Nat := 937667023175375531151923

theorem tailTrace_2739150 : CollatzResearch.WordTrace tailWord_2739150 prefixEnd_2739150 937667023175375531151923 := by
  unfold tailWord_2739150
  simp only [CollatzResearch.WordTrace]
  refine ⟨12488126003316854302610863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66603338684356556280591269 12488126003316854302610863)
  ·
    refine ⟨18732189004975281453916295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12488126003316854302610863 18732189004975281453916295)
    ·
      refine ⟨28098283507462922180874443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18732189004975281453916295 28098283507462922180874443)
      ·
        refine ⟨42147425261194383271311665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28098283507462922180874443 42147425261194383271311665)
        ·
          refine ⟨31610568945895787453483749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42147425261194383271311665 31610568945895787453483749)
          ·
            refine ⟨5926981677355460147528203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31610568945895787453483749 5926981677355460147528203)
            ·
              refine ⟨8890472516033190221292305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5926981677355460147528203 8890472516033190221292305)
              ·
                refine ⟨6667854387024892665969229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8890472516033190221292305 6667854387024892665969229)
                ·
                  refine ⟨2500445395134334749738461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6667854387024892665969229 2500445395134334749738461)
                  ·
                    refine ⟨937667023175375531151923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2500445395134334749738461 937667023175375531151923)
                    ·
                      rfl

theorem cell22_2739150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_2739150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739150 prefixEnd_2739150 := by exact prefixLift 2739150
  have htrace : WordTrace (prefixWord ++ tailWord_2739150) baseStart_2739150 baseEnd_2739150 := by
    simpa [prefixWord, tailWord_2739150, baseEnd_2739150] using wordTrace_append hprefix tailTrace_2739150
  have hstable : (prefixWord ++ tailWord_2739150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739150).length < 2 ^ (prefixWord ++ tailWord_2739150).sum := by decide
  have hdescent : baseEnd_2739150 < baseStart_2739150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739178 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_2739178 : Nat := 118140960795 + 2739178 * 2 ^ 59
def prefixEnd_2739178 : Nat := 4983230072969 + 3 ^ 40 * 2739178 * 2
def baseEnd_2739178 : Nat := 937676608147592791451837

theorem tailTrace_2739178 : CollatzResearch.WordTrace tailWord_2739178 prefixEnd_2739178 937676608147592791451837 := by
  unfold tailWord_2739178
  simp only [CollatzResearch.WordTrace]
  refine ⟨24976507317608348800726547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66604019513622263468604125 24976507317608348800726547)
  ·
    refine ⟨37464760976412523201089821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24976507317608348800726547 37464760976412523201089821)
    ·
      refine ⟨14049285366154696200408683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37464760976412523201089821 14049285366154696200408683)
      ·
        refine ⟨21073928049232044300613025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14049285366154696200408683 21073928049232044300613025)
        ·
          refine ⟨15805446036924033225459769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21073928049232044300613025 15805446036924033225459769)
          ·
            refine ⟨11854084527693024919094827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15805446036924033225459769 11854084527693024919094827)
            ·
              refine ⟨17781126791539537378642241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11854084527693024919094827 17781126791539537378642241)
              ·
                refine ⟨13335845093654653033981681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17781126791539537378642241 13335845093654653033981681)
                ·
                  refine ⟨10001883820240989775486261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13335845093654653033981681 10001883820240989775486261)
                  ·
                    refine ⟨937676608147592791451837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10001883820240989775486261 937676608147592791451837)
                    ·
                      rfl

theorem cell22_2739178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_2739178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739178 prefixEnd_2739178 := by exact prefixLift 2739178
  have htrace : WordTrace (prefixWord ++ tailWord_2739178) baseStart_2739178 baseEnd_2739178 := by
    simpa [prefixWord, tailWord_2739178, baseEnd_2739178] using wordTrace_append hprefix tailTrace_2739178
  have hstable : (prefixWord ++ tailWord_2739178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739178).length < 2 ^ (prefixWord ++ tailWord_2739178).sum := by decide
  have hdescent : baseEnd_2739178 < baseStart_2739178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739208 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 6]
def baseStart_2739208 : Nat := 118140960795 + 2739208 * 2 ^ 59
def prefixEnd_2739208 : Nat := 4983230072969 + 3 ^ 40 * 2739208 * 2
def baseEnd_2739208 : Nat := 312562292586894237733915

theorem tailTrace_2739208 : CollatzResearch.WordTrace tailWord_2739208 prefixEnd_2739208 312562292586894237733915 := by
  unfold tailWord_2739208
  simp only [CollatzResearch.WordTrace]
  refine ⟨49953561730162355163249139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66604748973549806884332185 49953561730162355163249139)
  ·
    refine ⟨74930342595243532744873709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49953561730162355163249139 74930342595243532744873709)
    ·
      refine ⟨28098878473216324779327641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74930342595243532744873709 28098878473216324779327641)
      ·
        refine ⟨21074158854912243584495731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28098878473216324779327641 21074158854912243584495731)
        ·
          refine ⟨31611238282368365376743597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21074158854912243584495731 31611238282368365376743597)
          ·
            refine ⟨11854214355888137016278849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31611238282368365376743597 11854214355888137016278849)
            ·
              refine ⟨8890660766916102762209137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11854214355888137016278849 8890660766916102762209137)
              ·
                refine ⟨6667995575187077071656853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8890660766916102762209137 6667995575187077071656853)
                ·
                  refine ⟨312562292586894237733915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6667995575187077071656853 312562292586894237733915)
                  ·
                    rfl

theorem cell22_2739208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_2739208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739208 prefixEnd_2739208 := by exact prefixLift 2739208
  have htrace : WordTrace (prefixWord ++ tailWord_2739208) baseStart_2739208 baseEnd_2739208 := by
    simpa [prefixWord, tailWord_2739208, baseEnd_2739208] using wordTrace_append hprefix tailTrace_2739208
  have hstable : (prefixWord ++ tailWord_2739208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739208).length < 2 ^ (prefixWord ++ tailWord_2739208).sum := by decide
  have hdescent : baseEnd_2739208 < baseStart_2739208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739210 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_2739210 : Nat := 118140960795 + 2739210 * 2 ^ 59
def prefixEnd_2739210 : Nat := 4983230072969 + 3 ^ 40 * 2739210 * 2
def baseEnd_2739210 : Nat := 937687562401555374651739

theorem tailTrace_2739210 : CollatzResearch.WordTrace tailWord_2739210 prefixEnd_2739210 937687562401555374651739 := by
  unfold tailWord_2739210
  simp only [CollatzResearch.WordTrace]
  refine ⟨24976799101579366167017771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66604797604211643112047389 24976799101579366167017771)
  ·
    refine ⟨37465198652369049250526657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24976799101579366167017771 37465198652369049250526657)
    ·
      refine ⟨28098898989276786937894993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37465198652369049250526657 28098898989276786937894993)
      ·
        refine ⟨21074174241957590203421245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28098898989276786937894993 21074174241957590203421245)
        ·
          refine ⟨7902815340734096326282967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21074174241957590203421245 7902815340734096326282967)
          ·
            refine ⟨11854223011101144489424451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7902815340734096326282967 11854223011101144489424451)
            ·
              refine ⟨17781334516651716734136677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11854223011101144489424451 17781334516651716734136677)
              ·
                refine ⟨3334000221872196887650627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17781334516651716734136677 3334000221872196887650627)
                ·
                  refine ⟨5001000332808295331475941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334000221872196887650627 5001000332808295331475941)
                  ·
                    refine ⟨937687562401555374651739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5001000332808295331475941 937687562401555374651739)
                    ·
                      rfl

theorem cell22_2739210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_2739210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739210 prefixEnd_2739210 := by exact prefixLift 2739210
  have htrace : WordTrace (prefixWord ++ tailWord_2739210) baseStart_2739210 baseEnd_2739210 := by
    simpa [prefixWord, tailWord_2739210, baseEnd_2739210] using wordTrace_append hprefix tailTrace_2739210
  have hstable : (prefixWord ++ tailWord_2739210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739210).length < 2 ^ (prefixWord ++ tailWord_2739210).sum := by decide
  have hdescent : baseEnd_2739210 < baseStart_2739210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739225 : List Nat := [1, 2, 1, 2, 1, 1, 7, 3, 4]
def baseStart_2739225 : Nat := 118140960795 + 2739225 * 2 ^ 59
def prefixEnd_2739225 : Nat := 4983230072969 + 3 ^ 40 * 2739225 * 2
def baseEnd_2739225 : Nat := 312564232402700111842231

theorem tailTrace_2739225 : CollatzResearch.WordTrace tailWord_2739225 prefixEnd_2739225 312564232402700111842231 := by
  unfold tailWord_2739225
  simp only [CollatzResearch.WordTrace]
  refine ⟨99907743501263122229867129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66605162334175414819911419 99907743501263122229867129)
  ·
    refine ⟨74930807625947341672400347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99907743501263122229867129 74930807625947341672400347)
    ·
      refine ⟨112396211438921012508600521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74930807625947341672400347 112396211438921012508600521)
      ·
        refine ⟨84297158579190759381450391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112396211438921012508600521 84297158579190759381450391)
        ·
          refine ⟨126445737868786139072175587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84297158579190759381450391 126445737868786139072175587)
          ·
            refine ⟨189668606803179208608263381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126445737868786139072175587 189668606803179208608263381)
            ·
              refine ⟨4445357971949512701756173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 189668606803179208608263381 4445357971949512701756173)
              ·
                refine ⟨1667009239481067263158565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4445357971949512701756173 1667009239481067263158565)
                ·
                  refine ⟨312564232402700111842231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1667009239481067263158565 312564232402700111842231)
                  ·
                    rfl

theorem cell22_2739225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 4].length) (baseStart_2739225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739225 prefixEnd_2739225 := by exact prefixLift 2739225
  have htrace : WordTrace (prefixWord ++ tailWord_2739225) baseStart_2739225 baseEnd_2739225 := by
    simpa [prefixWord, tailWord_2739225, baseEnd_2739225] using wordTrace_append hprefix tailTrace_2739225
  have hstable : (prefixWord ++ tailWord_2739225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739225).length < 2 ^ (prefixWord ++ tailWord_2739225).sum := by decide
  have hdescent : baseEnd_2739225 < baseStart_2739225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739242 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 6]
def baseStart_2739242 : Nat := 118140960795 + 2739242 * 2 ^ 59
def prefixEnd_2739242 : Nat := 4983230072969 + 3 ^ 40 * 2739242 * 2
def baseEnd_2739242 : Nat := 312566172218505985950547

theorem tailTrace_2739242 : CollatzResearch.WordTrace tailWord_2739242 prefixEnd_2739242 312566172218505985950547 := by
  unfold tailWord_2739242
  simp only [CollatzResearch.WordTrace]
  refine ⟨24977090885550383533308995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66605575694801022755490653 24977090885550383533308995)
  ·
    refine ⟨37465636328325575299963493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24977090885550383533308995 37465636328325575299963493)
    ·
      refine ⟨7024806811561045368743155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37465636328325575299963493 7024806811561045368743155)
      ·
        refine ⟨10537210217341568053114733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7024806811561045368743155 10537210217341568053114733)
        ·
          refine ⟨3951453831503088019918025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10537210217341568053114733 3951453831503088019918025)
          ·
            refine ⟨2963590373627316014938519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3951453831503088019918025 2963590373627316014938519)
            ·
              refine ⟨4445385560440974022407779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963590373627316014938519 4445385560440974022407779)
              ·
                refine ⟨6668078340661461033611669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445385560440974022407779 6668078340661461033611669)
                ·
                  refine ⟨312566172218505985950547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6668078340661461033611669 312566172218505985950547)
                  ·
                    rfl

theorem cell22_2739242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_2739242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739242 prefixEnd_2739242 := by exact prefixLift 2739242
  have htrace : WordTrace (prefixWord ++ tailWord_2739242) baseStart_2739242 baseEnd_2739242 := by
    simpa [prefixWord, tailWord_2739242, baseEnd_2739242] using wordTrace_append hprefix tailTrace_2739242
  have hstable : (prefixWord ++ tailWord_2739242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739242).length < 2 ^ (prefixWord ++ tailWord_2739242).sum := by decide
  have hdescent : baseEnd_2739242 < baseStart_2739242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739257 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 2, 3]
def baseStart_2739257 : Nat := 118140960795 + 2739257 * 2 ^ 59
def prefixEnd_2739257 : Nat := 4983230072969 + 3 ^ 40 * 2739257 * 2
def baseEnd_2739257 : Nat := 937703651462062918726595

theorem tailTrace_2739257 : CollatzResearch.WordTrace tailWord_2739257 prefixEnd_2739257 937703651462062918726595 := by
  unfold tailWord_2739257
  simp only [CollatzResearch.WordTrace]
  refine ⟨99908910637147191695032025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66605940424764794463354683 99908910637147191695032025)
  ·
    refine ⟨74931682977860393771274019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99908910637147191695032025 74931682977860393771274019)
    ·
      refine ⟨112397524466790590656911029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74931682977860393771274019 112397524466790590656911029)
      ·
        refine ⟨10537267918761617874085409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112397524466790590656911029 10537267918761617874085409)
        ·
          refine ⟨7902950939071213405564057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10537267918761617874085409 7902950939071213405564057)
          ·
            refine ⟨5927213204303410054173043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7902950939071213405564057 5927213204303410054173043)
            ·
              refine ⟨8890819806455115081259565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5927213204303410054173043 8890819806455115081259565)
              ·
                refine ⟨3334057427420668155472337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8890819806455115081259565 3334057427420668155472337)
                ·
                  refine ⟨2500543070565501116604253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3334057427420668155472337 2500543070565501116604253)
                  ·
                    refine ⟨937703651462062918726595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2500543070565501116604253 937703651462062918726595)
                    ·
                      rfl

theorem cell22_2739257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 3].length) (baseStart_2739257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739257 prefixEnd_2739257 := by exact prefixLift 2739257
  have htrace : WordTrace (prefixWord ++ tailWord_2739257) baseStart_2739257 baseEnd_2739257 := by
    simpa [prefixWord, tailWord_2739257, baseEnd_2739257] using wordTrace_append hprefix tailTrace_2739257
  have hstable : (prefixWord ++ tailWord_2739257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739257).length < 2 ^ (prefixWord ++ tailWord_2739257).sum := by decide
  have hdescent : baseEnd_2739257 < baseStart_2739257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739293 : List Nat := [1, 4, 4, 1, 3, 1, 2, 2, 4]
def baseStart_2739293 : Nat := 118140960795 + 2739293 * 2 ^ 59
def prefixEnd_2739293 : Nat := 4983230072969 + 3 ^ 40 * 2739293 * 2
def baseEnd_2739293 : Nat := 312571991665923608275495

theorem tailTrace_2739293 : CollatzResearch.WordTrace tailWord_2739293 prefixEnd_2739293 312571991665923608275495 := by
  unfold tailWord_2739293
  simp only [CollatzResearch.WordTrace]
  refine ⟨99910223665016769843342533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66606815776677846562228355 99910223665016769843342533)
  ·
    refine ⟨18733166937190644345626725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99910223665016769843342533 18733166937190644345626725)
    ·
      refine ⟨3512468800723245814805011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18733166937190644345626725 3512468800723245814805011)
      ·
        refine ⟨5268703201084868722207517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512468800723245814805011 5268703201084868722207517)
        ·
          refine ⟨1975763700406825770827819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5268703201084868722207517 1975763700406825770827819)
          ·
            refine ⟨2963645550610238656241729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975763700406825770827819 2963645550610238656241729)
            ·
              refine ⟨2222734162957678992181297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2963645550610238656241729 2222734162957678992181297)
              ·
                refine ⟨1667050622218259244135973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222734162957678992181297 1667050622218259244135973)
                ·
                  refine ⟨312571991665923608275495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1667050622218259244135973 312571991665923608275495)
                  ·
                    rfl

theorem cell22_2739293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_2739293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739293 prefixEnd_2739293 := by exact prefixLift 2739293
  have htrace : WordTrace (prefixWord ++ tailWord_2739293) baseStart_2739293 baseEnd_2739293 := by
    simpa [prefixWord, tailWord_2739293, baseEnd_2739293] using wordTrace_append hprefix tailTrace_2739293
  have hstable : (prefixWord ++ tailWord_2739293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739293).length < 2 ^ (prefixWord ++ tailWord_2739293).sum := by decide
  have hdescent : baseEnd_2739293 < baseStart_2739293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739304 : List Nat := [2, 1, 4, 4, 2, 1, 1, 7]
def baseStart_2739304 : Nat := 118140960795 + 2739304 * 2 ^ 59
def prefixEnd_2739304 : Nat := 4983230072969 + 3 ^ 40 * 2739304 * 2
def baseEnd_2739304 : Nat := 104191082280285606977939

theorem tailTrace_2739304 : CollatzResearch.WordTrace tailWord_2739304 prefixEnd_2739304 104191082280285606977939 := by
  unfold tailWord_2739304
  simp only [CollatzResearch.WordTrace]
  refine ⟨49955312433988459360996483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66607083245317945814661977 49955312433988459360996483)
  ·
    refine ⟨74932968650982689041494725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49955312433988459360996483 74932968650982689041494725)
    ·
      refine ⟨14049931622059254195280261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74932968650982689041494725 14049931622059254195280261)
      ·
        refine ⟨2634362179136110161615049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14049931622059254195280261 2634362179136110161615049)
        ·
          refine ⟨1975771634352082621211287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2634362179136110161615049 1975771634352082621211287)
          ·
            refine ⟨2963657451528123931816931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975771634352082621211287 2963657451528123931816931)
            ·
              refine ⟨4445486177292185897725397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963657451528123931816931 4445486177292185897725397)
              ·
                refine ⟨104191082280285606977939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4445486177292185897725397 104191082280285606977939)
                ·
                  rfl

theorem cell22_2739304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 7].length) (baseStart_2739304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739304 prefixEnd_2739304 := by exact prefixLift 2739304
  have htrace : WordTrace (prefixWord ++ tailWord_2739304) baseStart_2739304 baseEnd_2739304 := by
    simpa [prefixWord, tailWord_2739304, baseEnd_2739304] using wordTrace_append hprefix tailTrace_2739304
  have hstable : (prefixWord ++ tailWord_2739304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739304).length < 2 ^ (prefixWord ++ tailWord_2739304).sum := by decide
  have hdescent : baseEnd_2739304 < baseStart_2739304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739336 : List Nat := [2, 1, 3, 4, 2, 1, 2, 3, 1, 3]
def baseStart_2739336 : Nat := 118140960795 + 2739336 * 2 ^ 59
def prefixEnd_2739336 : Nat := 4983230072969 + 3 ^ 40 * 2739336 * 2
def baseEnd_2739336 : Nat := 937730694776533046001353

theorem tailTrace_2739336 : CollatzResearch.WordTrace tailWord_2739336 prefixEnd_2739336 937730694776533046001353 := by
  unfold tailWord_2739336
  simp only [CollatzResearch.WordTrace]
  refine ⟨49955896001930494093578931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66607861335907325458105241 49955896001930494093578931)
  ·
    refine ⟨74933844002895741140368397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49955896001930494093578931 74933844002895741140368397)
    ·
      refine ⟨28100191501085902927638149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74933844002895741140368397 28100191501085902927638149)
      ·
        refine ⟨5268785906453606798932153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28100191501085902927638149 5268785906453606798932153)
        ·
          refine ⟨3951589429840205099199115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5268785906453606798932153 3951589429840205099199115)
          ·
            refine ⟨5927384144760307648798673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3951589429840205099199115 5927384144760307648798673)
            ·
              refine ⟨4445538108570230736599005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5927384144760307648798673 4445538108570230736599005)
              ·
                refine ⟨1667076790713836526224627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4445538108570230736599005 1667076790713836526224627)
                ·
                  refine ⟨2500615186070754789336941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667076790713836526224627 2500615186070754789336941)
                  ·
                    refine ⟨937730694776533046001353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2500615186070754789336941 937730694776533046001353)
                    ·
                      rfl

theorem cell22_2739336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_2739336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739336 prefixEnd_2739336 := by exact prefixLift 2739336
  have htrace : WordTrace (prefixWord ++ tailWord_2739336) baseStart_2739336 baseEnd_2739336 := by
    simpa [prefixWord, tailWord_2739336, baseEnd_2739336] using wordTrace_append hprefix tailTrace_2739336
  have hstable : (prefixWord ++ tailWord_2739336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739336).length < 2 ^ (prefixWord ++ tailWord_2739336).sum := by decide
  have hdescent : baseEnd_2739336 < baseStart_2739336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739360 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 6]
def baseStart_2739360 : Nat := 118140960795 + 2739360 * 2 ^ 59
def prefixEnd_2739360 : Nat := 4983230072969 + 3 ^ 40 * 2739360 * 2
def baseEnd_2739360 : Nat := 312579636822334994467093

theorem tailTrace_2739360 : CollatzResearch.WordTrace tailWord_2739360 prefixEnd_2739360 312579636822334994467093 := by
  unfold tailWord_2739360
  simp only [CollatzResearch.WordTrace]
  refine ⟨49956333677887020143015767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66608444903849360190687689 49956333677887020143015767)
  ·
    refine ⟨74934500516830530214523651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49956333677887020143015767 74934500516830530214523651)
    ·
      refine ⟨112401750775245795321785477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74934500516830530214523651 112401750775245795321785477)
      ·
        refine ⟨21075328270358586622834777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112401750775245795321785477 21075328270358586622834777)
        ·
          refine ⟨15806496202768939967126083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21075328270358586622834777 15806496202768939967126083)
          ·
            refine ⟨23709744304153409950689125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15806496202768939967126083 23709744304153409950689125)
            ·
              refine ⟨4445577057028764365754211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23709744304153409950689125 4445577057028764365754211)
              ·
                refine ⟨6668365585543146548631317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445577057028764365754211 6668365585543146548631317)
                ·
                  refine ⟨312579636822334994467093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6668365585543146548631317 312579636822334994467093)
                  ·
                    rfl

theorem cell22_2739360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_2739360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739360 prefixEnd_2739360 := by exact prefixLift 2739360
  have htrace : WordTrace (prefixWord ++ tailWord_2739360) baseStart_2739360 baseEnd_2739360 := by
    simpa [prefixWord, tailWord_2739360, baseEnd_2739360] using wordTrace_append hprefix tailTrace_2739360
  have hstable : (prefixWord ++ tailWord_2739360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739360).length < 2 ^ (prefixWord ++ tailWord_2739360).sum := by decide
  have hdescent : baseEnd_2739360 < baseStart_2739360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739375 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 1, 5]
def baseStart_2739375 : Nat := 118140960795 + 2739375 * 2 ^ 59
def prefixEnd_2739375 : Nat := 4983230072969 + 3 ^ 40 * 2739375 * 2
def baseEnd_2739375 : Nat := 937744045273549944276233

theorem tailTrace_2739375 : CollatzResearch.WordTrace tailWord_2739375 prefixEnd_2739375 937744045273549944276233 := by
  unfold tailWord_2739375
  simp only [CollatzResearch.WordTrace]
  refine ⟨99913214450719697847827579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66608809633813131898551719 99913214450719697847827579)
  ·
    refine ⟨149869821676079546771741369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99913214450719697847827579 149869821676079546771741369)
    ·
      refine ⟨112402366257059660078806027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149869821676079546771741369 112402366257059660078806027)
      ·
        refine ⟨168603549385589490118209041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112402366257059660078806027 168603549385589490118209041)
        ·
          refine ⟨126452662039192117588656781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168603549385589490118209041 126452662039192117588656781)
          ·
            refine ⟨47419748264697044095746293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126452662039192117588656781 47419748264697044095746293)
            ·
              refine ⟨4445601399815347883976215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47419748264697044095746293 4445601399815347883976215)
              ·
                refine ⟨6668402099723021825964323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445601399815347883976215 6668402099723021825964323)
                ·
                  refine ⟨10002603149584532738946485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6668402099723021825964323 10002603149584532738946485)
                  ·
                    refine ⟨937744045273549944276233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10002603149584532738946485 937744045273549944276233)
                    ·
                      rfl

theorem cell22_2739375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_2739375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739375 prefixEnd_2739375 := by exact prefixLift 2739375
  have htrace : WordTrace (prefixWord ++ tailWord_2739375) baseStart_2739375 baseEnd_2739375 := by
    simpa [prefixWord, tailWord_2739375, baseEnd_2739375] using wordTrace_append hprefix tailTrace_2739375
  have hstable : (prefixWord ++ tailWord_2739375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739375).length < 2 ^ (prefixWord ++ tailWord_2739375).sum := by decide
  have hdescent : baseEnd_2739375 < baseStart_2739375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739465 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_2739465 : Nat := 118140960795 + 2739465 * 2 ^ 59
def prefixEnd_2739465 : Nat := 4983230072969 + 3 ^ 40 * 2739465 * 2
def baseEnd_2739465 : Nat := 937774854112819709525957

theorem tailTrace_2739465 : CollatzResearch.WordTrace tailWord_2739465 prefixEnd_2739465 937774854112819709525957 := by
  unfold tailWord_2739465
  simp only [CollatzResearch.WordTrace]
  refine ⟨99916497020393643218603849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66610998013595762145735899 99916497020393643218603849)
  ·
    refine ⟨74937372765295232413952887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99916497020393643218603849 74937372765295232413952887)
    ·
      refine ⟨112406059147942848620929331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74937372765295232413952887 112406059147942848620929331)
      ·
        refine ⟨168609088721914272931393997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112406059147942848620929331 168609088721914272931393997)
        ·
          refine ⟨63228408270717852349272749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168609088721914272931393997 63228408270717852349272749)
          ·
            refine ⟨23710653101519194630977281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63228408270717852349272749 23710653101519194630977281)
            ·
              refine ⟨17782989826139395973232961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23710653101519194630977281 17782989826139395973232961)
              ·
                refine ⟨13337242369604546979924721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17782989826139395973232961 13337242369604546979924721)
                ·
                  refine ⟨10002931777203410234943541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13337242369604546979924721 10002931777203410234943541)
                  ·
                    refine ⟨937774854112819709525957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10002931777203410234943541 937774854112819709525957)
                    ·
                      rfl

theorem cell22_2739465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_2739465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739465 prefixEnd_2739465 := by exact prefixLift 2739465
  have htrace : WordTrace (prefixWord ++ tailWord_2739465) baseStart_2739465 baseEnd_2739465 := by
    simpa [prefixWord, tailWord_2739465, baseEnd_2739465] using wordTrace_append hprefix tailTrace_2739465
  have hstable : (prefixWord ++ tailWord_2739465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739465).length < 2 ^ (prefixWord ++ tailWord_2739465).sum := by decide
  have hdescent : baseEnd_2739465 < baseStart_2739465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739467 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 5]
def baseStart_2739467 : Nat := 118140960795 + 2739467 * 2 ^ 59
def prefixEnd_2739467 : Nat := 4983230072969 + 3 ^ 40 * 2739467 * 2
def baseEnd_2739467 : Nat := 312591846251230790325317

theorem tailTrace_2739467 : CollatzResearch.WordTrace tailWord_2739467 prefixEnd_2739467 312591846251230790325317 := by
  unfold tailWord_2739467
  simp only [CollatzResearch.WordTrace]
  refine ⟨99916569966386397560176655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66611046644257598373451103 99916569966386397560176655)
  ·
    refine ⟨149874854949579596340264983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99916569966386397560176655 149874854949579596340264983)
    ·
      refine ⟨224812282424369394510397475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149874854949579596340264983 224812282424369394510397475)
      ·
        refine ⟨337218423636554091765596213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224812282424369394510397475 337218423636554091765596213)
        ·
          refine ⟨31614227215926946103024645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 337218423636554091765596213 31614227215926946103024645)
          ·
            refine ⟨5927667602986302394317121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31614227215926946103024645 5927667602986302394317121)
            ·
              refine ⟨4445750702239726795737841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5927667602986302394317121 4445750702239726795737841)
              ·
                refine ⟨3334313026679795096803381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4445750702239726795737841 3334313026679795096803381)
                ·
                  refine ⟨312591846251230790325317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3334313026679795096803381 312591846251230790325317)
                  ·
                    rfl

theorem cell22_2739467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 5].length) (baseStart_2739467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739467 prefixEnd_2739467 := by exact prefixLift 2739467
  have htrace : WordTrace (prefixWord ++ tailWord_2739467) baseStart_2739467 baseEnd_2739467 := by
    simpa [prefixWord, tailWord_2739467, baseEnd_2739467] using wordTrace_append hprefix tailTrace_2739467
  have hstable : (prefixWord ++ tailWord_2739467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739467).length < 2 ^ (prefixWord ++ tailWord_2739467).sum := by decide
  have hdescent : baseEnd_2739467 < baseStart_2739467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739482 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_2739482 : Nat := 118140960795 + 2739482 * 2 ^ 59
def prefixEnd_2739482 : Nat := 4983230072969 + 3 ^ 40 * 2739482 * 2
def baseEnd_2739482 : Nat := 937780673560237331850905

theorem tailTrace_2739482 : CollatzResearch.WordTrace tailWord_2739482 prefixEnd_2739482 937780673560237331850905 := by
  unfold tailWord_2739482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24979279265333013780493175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66611411374221370081315133 24979279265333013780493175)
  ·
    refine ⟨37468918897999520670739763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24979279265333013780493175 37468918897999520670739763)
    ·
      refine ⟨56203378346999281006109645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37468918897999520670739763 56203378346999281006109645)
      ·
        refine ⟨21076266880124730377291117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56203378346999281006109645 21076266880124730377291117)
        ·
          refine ⟨7903600080046773891484169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21076266880124730377291117 7903600080046773891484169)
          ·
            refine ⟨5927700060035080418613127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7903600080046773891484169 5927700060035080418613127)
            ·
              refine ⟨8891550090052620627919691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5927700060035080418613127 8891550090052620627919691)
              ·
                refine ⟨13337325135078930941879537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8891550090052620627919691 13337325135078930941879537)
                ·
                  refine ⟨10002993851309198206409653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13337325135078930941879537 10002993851309198206409653)
                  ·
                    refine ⟨937780673560237331850905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10002993851309198206409653 937780673560237331850905)
                    ·
                      rfl

theorem cell22_2739482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_2739482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739482 prefixEnd_2739482 := by exact prefixLift 2739482
  have htrace : WordTrace (prefixWord ++ tailWord_2739482) baseStart_2739482 baseEnd_2739482 := by
    simpa [prefixWord, tailWord_2739482, baseEnd_2739482] using wordTrace_append hprefix tailTrace_2739482
  have hstable : (prefixWord ++ tailWord_2739482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739482).length < 2 ^ (prefixWord ++ tailWord_2739482).sum := by decide
  have hdescent : baseEnd_2739482 < baseStart_2739482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739589 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 3, 3]
def baseStart_2739589 : Nat := 118140960795 + 2739589 * 2 ^ 59
def prefixEnd_2739589 : Nat := 4983230072969 + 3 ^ 40 * 2739589 * 2
def baseEnd_2739589 : Nat := 937817301846924719425577

theorem tailTrace_2739589 : CollatzResearch.WordTrace tailWord_2739589 prefixEnd_2739589 937817301846924719425577 := by
  unfold tailWord_2739589
  simp only [CollatzResearch.WordTrace]
  refine ⟨99921019671944412396117821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66614013114629608264078547 99921019671944412396117821)
  ·
    refine ⟨37470382376979154648544183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99921019671944412396117821 37470382376979154648544183)
    ·
      refine ⟨56205573565468731972816275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37470382376979154648544183 56205573565468731972816275)
      ·
        refine ⟨84308360348203097959224413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56205573565468731972816275 84308360348203097959224413)
        ·
          refine ⟨31615635130576161734709155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84308360348203097959224413 31615635130576161734709155)
          ·
            refine ⟨47423452695864242602063733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31615635130576161734709155 47423452695864242602063733)
            ·
              refine ⟨4445948690237272743943475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47423452695864242602063733 4445948690237272743943475)
              ·
                refine ⟨6668923035355909115915213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445948690237272743943475 6668923035355909115915213)
                ·
                  refine ⟨2500846138258465918468205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6668923035355909115915213 2500846138258465918468205)
                  ·
                    refine ⟨937817301846924719425577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2500846138258465918468205 937817301846924719425577)
                    ·
                      rfl

theorem cell22_2739589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_2739589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739589 prefixEnd_2739589 := by exact prefixLift 2739589
  have htrace : WordTrace (prefixWord ++ tailWord_2739589) baseStart_2739589 baseEnd_2739589 := by
    simpa [prefixWord, tailWord_2739589, baseEnd_2739589] using wordTrace_append hprefix tailTrace_2739589
  have hstable : (prefixWord ++ tailWord_2739589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739589).length < 2 ^ (prefixWord ++ tailWord_2739589).sum := by decide
  have hdescent : baseEnd_2739589 < baseStart_2739589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739679 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 4, 3]
def baseStart_2739679 : Nat := 118140960795 + 2739679 * 2 ^ 59
def prefixEnd_2739679 : Nat := 4983230072969 + 3 ^ 40 * 2739679 * 2
def baseEnd_2739679 : Nat := 937848110686194484675301

theorem tailTrace_2739679 : CollatzResearch.WordTrace tailWord_2739679 prefixEnd_2739679 937848110686194484675301 := by
  unfold tailWord_2739679
  simp only [CollatzResearch.WordTrace]
  refine ⟨99924302241618357766894091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66616201494412238511262727 99924302241618357766894091)
  ·
    refine ⟨149886453362427536650341137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99924302241618357766894091 149886453362427536650341137)
    ·
      refine ⟨112414840021820652487755853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149886453362427536650341137 112414840021820652487755853)
      ·
        refine ⟨42155565008182744682908445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112414840021820652487755853 42155565008182744682908445)
        ·
          refine ⟨15808336878068529256090667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42155565008182744682908445 15808336878068529256090667)
          ·
            refine ⟨23712505317102793884136001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15808336878068529256090667 23712505317102793884136001)
            ·
              refine ⟨17784378987827095413102001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23712505317102793884136001 17784378987827095413102001)
              ·
                refine ⟨13338284240870321559826501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17784378987827095413102001 13338284240870321559826501)
                ·
                  refine ⟨2500928295163185292467469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13338284240870321559826501 2500928295163185292467469)
                  ·
                    refine ⟨937848110686194484675301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2500928295163185292467469 937848110686194484675301)
                    ·
                      rfl

theorem cell22_2739679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 3].length) (baseStart_2739679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739679 prefixEnd_2739679 := by exact prefixLift 2739679
  have htrace : WordTrace (prefixWord ++ tailWord_2739679) baseStart_2739679 baseEnd_2739679 := by
    simpa [prefixWord, tailWord_2739679, baseEnd_2739679] using wordTrace_append hprefix tailTrace_2739679
  have hstable : (prefixWord ++ tailWord_2739679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739679).length < 2 ^ (prefixWord ++ tailWord_2739679).sum := by decide
  have hdescent : baseEnd_2739679 < baseStart_2739679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739681 : List Nat := [1, 2, 3, 1, 2, 4, 2, 3, 4]
def baseStart_2739681 : Nat := 118140960795 + 2739681 * 2 ^ 59
def prefixEnd_2739681 : Nat := 4983230072969 + 3 ^ 40 * 2739681 * 2
def baseEnd_2739681 : Nat := 312616265109022382041765

theorem tailTrace_2739681 : CollatzResearch.WordTrace tailWord_2739681 prefixEnd_2739681 312616265109022382041765 := by
  unfold tailWord_2739681
  simp only [CollatzResearch.WordTrace]
  refine ⟨99924375187611112108466897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66616250125074074738977931 99924375187611112108466897)
  ·
    refine ⟨74943281390708334081350173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99924375187611112108466897 74943281390708334081350173)
    ·
      refine ⟨28103730521515625280506315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74943281390708334081350173 28103730521515625280506315)
      ·
        refine ⟨42155595782273437920759473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28103730521515625280506315 42155595782273437920759473)
        ·
          refine ⟨31616696836705078440569605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42155595782273437920759473 31616696836705078440569605)
          ·
            refine ⟨5928130656882202207606801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31616696836705078440569605 5928130656882202207606801)
            ·
              refine ⟨4446097992661651655705101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5928130656882202207606801 4446097992661651655705101)
              ·
                refine ⟨1667286747248119370889413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4446097992661651655705101 1667286747248119370889413)
                ·
                  refine ⟨312616265109022382041765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1667286747248119370889413 312616265109022382041765)
                  ·
                    rfl

theorem cell22_2739681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 4].length) (baseStart_2739681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739681 prefixEnd_2739681 := by exact prefixLift 2739681
  have htrace : WordTrace (prefixWord ++ tailWord_2739681) baseStart_2739681 baseEnd_2739681 := by
    simpa [prefixWord, tailWord_2739681, baseEnd_2739681] using wordTrace_append hprefix tailTrace_2739681
  have hstable : (prefixWord ++ tailWord_2739681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739681).length < 2 ^ (prefixWord ++ tailWord_2739681).sum := by decide
  have hdescent : baseEnd_2739681 < baseStart_2739681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739683 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 1, 4]
def baseStart_2739683 : Nat := 118140960795 + 2739683 * 2 ^ 59
def prefixEnd_2739683 : Nat := 4983230072969 + 3 ^ 40 * 2739683 * 2
def baseEnd_2739683 : Nat := 937849479967939807575289

theorem tailTrace_2739683 : CollatzResearch.WordTrace tailWord_2739683 prefixEnd_2739683 937849479967939807575289 := by
  unfold tailWord_2739683
  simp only [CollatzResearch.WordTrace]
  refine ⟨99924448133603866450039703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66616298755735910966693135 99924448133603866450039703)
  ·
    refine ⟨149886672200405799675059555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99924448133603866450039703 149886672200405799675059555)
    ·
      refine ⟨224830008300608699512589333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149886672200405799675059555 224830008300608699512589333)
      ·
        refine ⟨10538906639091032789652625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 224830008300608699512589333 10538906639091032789652625)
        ·
          refine ⟨7904179979318274592239469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10538906639091032789652625 7904179979318274592239469)
          ·
            refine ⟨2964067492244352972089801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7904179979318274592239469 2964067492244352972089801)
            ·
              refine ⟨2223050619183264729067351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2964067492244352972089801 2223050619183264729067351)
              ·
                refine ⟨3334575928774897093601027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223050619183264729067351 3334575928774897093601027)
                ·
                  refine ⟨5001863893162345640401541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334575928774897093601027 5001863893162345640401541)
                  ·
                    refine ⟨937849479967939807575289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5001863893162345640401541 937849479967939807575289)
                    ·
                      rfl

theorem cell22_2739683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 4].length) (baseStart_2739683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739683 prefixEnd_2739683 := by exact prefixLift 2739683
  have htrace : WordTrace (prefixWord ++ tailWord_2739683) baseStart_2739683 baseEnd_2739683 := by
    simpa [prefixWord, tailWord_2739683, baseEnd_2739683] using wordTrace_append hprefix tailTrace_2739683
  have hstable : (prefixWord ++ tailWord_2739683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739683).length < 2 ^ (prefixWord ++ tailWord_2739683).sum := by decide
  have hdescent : baseEnd_2739683 < baseStart_2739683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739694 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2739694 : Nat := 118140960795 + 2739694 * 2 ^ 59
def prefixEnd_2739694 : Nat := 4983230072969 + 3 ^ 40 * 2739694 * 2
def baseEnd_2739694 : Nat := 937853245492739445550255

theorem tailTrace_2739694 : CollatzResearch.WordTrace tailWord_2739694 prefixEnd_2739694 937853245492739445550255 := by
  unfold tailWord_2739694
  simp only [CollatzResearch.WordTrace]
  refine ⟨12490606167070501916086267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66616566224376010219126757 12490606167070501916086267)
  ·
    refine ⟨18735909250605752874129401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12490606167070501916086267 18735909250605752874129401)
    ·
      refine ⟨14051931937954314655597051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18735909250605752874129401 14051931937954314655597051)
      ·
        refine ⟨21077897906931471983395577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14051931937954314655597051 21077897906931471983395577)
        ·
          refine ⟨15808423430198603987546683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21077897906931471983395577 15808423430198603987546683)
          ·
            refine ⟨23712635145297905981320025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15808423430198603987546683 23712635145297905981320025)
            ·
              refine ⟨17784476358973429485990019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23712635145297905981320025 17784476358973429485990019)
              ·
                refine ⟨26676714538460144228985029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17784476358973429485990019 26676714538460144228985029)
                ·
                  refine ⟨5001883975961277042934693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26676714538460144228985029 5001883975961277042934693)
                  ·
                    refine ⟨937853245492739445550255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5001883975961277042934693 937853245492739445550255)
                    ·
                      rfl

theorem cell22_2739694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2739694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739694 prefixEnd_2739694 := by exact prefixLift 2739694
  have htrace : WordTrace (prefixWord ++ tailWord_2739694) baseStart_2739694 baseEnd_2739694 := by
    simpa [prefixWord, tailWord_2739694, baseEnd_2739694] using wordTrace_append hprefix tailTrace_2739694
  have hstable : (prefixWord ++ tailWord_2739694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739694).length < 2 ^ (prefixWord ++ tailWord_2739694).sum := by decide
  have hdescent : baseEnd_2739694 < baseStart_2739694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739696 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 2, 3]
def baseStart_2739696 : Nat := 118140960795 + 2739696 * 2 ^ 59
def prefixEnd_2739696 : Nat := 4983230072969 + 3 ^ 40 * 2739696 * 2
def baseEnd_2739696 : Nat := 937853930133612107000249

theorem tailTrace_2739696 : CollatzResearch.WordTrace tailWord_2739696 prefixEnd_2739696 937853930133612107000249 := by
  unfold tailWord_2739696
  simp only [CollatzResearch.WordTrace]
  refine ⟨49962461141278384835131471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66616614855037846446841961 49962461141278384835131471)
  ·
    refine ⟨74943691711917577252697207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49962461141278384835131471 74943691711917577252697207)
    ·
      refine ⟨112415537567876365879045811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74943691711917577252697207 112415537567876365879045811)
      ·
        refine ⟨168623306351814548818568717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112415537567876365879045811 168623306351814548818568717)
        ·
          refine ⟨63233739881930455806963269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168623306351814548818568717 63233739881930455806963269)
          ·
            refine ⟨11856326227861960463805613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63233739881930455806963269 11856326227861960463805613)
            ·
              refine ⟨4446122335448235173927105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11856326227861960463805613 4446122335448235173927105)
              ·
                refine ⟨3334591751586176380445329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4446122335448235173927105 3334591751586176380445329)
                ·
                  refine ⟨2500943813689632285333997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3334591751586176380445329 2500943813689632285333997)
                  ·
                    refine ⟨937853930133612107000249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2500943813689632285333997 937853930133612107000249)
                    ·
                      rfl

theorem cell22_2739696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2, 3].length) (baseStart_2739696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739696 prefixEnd_2739696 := by exact prefixLift 2739696
  have htrace : WordTrace (prefixWord ++ tailWord_2739696) baseStart_2739696 baseEnd_2739696 := by
    simpa [prefixWord, tailWord_2739696, baseEnd_2739696] using wordTrace_append hprefix tailTrace_2739696
  have hstable : (prefixWord ++ tailWord_2739696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739696).length < 2 ^ (prefixWord ++ tailWord_2739696).sum := by decide
  have hdescent : baseEnd_2739696 < baseStart_2739696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739713 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 1, 5]
def baseStart_2739713 : Nat := 118140960795 + 2739713 * 2 ^ 59
def prefixEnd_2739713 : Nat := 4983230072969 + 3 ^ 40 * 2739713 * 2
def baseEnd_2739713 : Nat := 937859749581029729325197

theorem tailTrace_2739713 : CollatzResearch.WordTrace tailWord_2739713 prefixEnd_2739713 937859749581029729325197 := by
  unfold tailWord_2739713
  simp only [CollatzResearch.WordTrace]
  refine ⟨99925542323495181573631793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66617028215663454382421195 99925542323495181573631793)
  ·
    refine ⟨74944156742621386180223845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99925542323495181573631793 74944156742621386180223845)
    ·
      refine ⟨14052029389241509908791971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74944156742621386180223845 14052029389241509908791971)
      ·
        refine ⟨21078044083862264863187957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14052029389241509908791971 21078044083862264863187957)
        ·
          refine ⟨1976066632862087330923871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21078044083862264863187957 1976066632862087330923871)
          ·
            refine ⟨2964099949293130996385807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976066632862087330923871 2964099949293130996385807)
            ·
              refine ⟨4446149923939696494578711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964099949293130996385807 4446149923939696494578711)
              ·
                refine ⟨6669224885909544741868067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4446149923939696494578711 6669224885909544741868067)
                ·
                  refine ⟨10003837328864317112802101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6669224885909544741868067 10003837328864317112802101)
                  ·
                    refine ⟨937859749581029729325197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10003837328864317112802101 937859749581029729325197)
                    ·
                      rfl

theorem cell22_2739713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_2739713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739713 prefixEnd_2739713 := by exact prefixLift 2739713
  have htrace : WordTrace (prefixWord ++ tailWord_2739713) baseStart_2739713 baseEnd_2739713 := by
    simpa [prefixWord, tailWord_2739713, baseEnd_2739713] using wordTrace_append hprefix tailTrace_2739713
  have hstable : (prefixWord ++ tailWord_2739713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739713).length < 2 ^ (prefixWord ++ tailWord_2739713).sum := by decide
  have hdescent : baseEnd_2739713 < baseStart_2739713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739732 : List Nat := [2, 4, 3, 1, 3, 1, 1, 3, 4]
def baseStart_2739732 : Nat := 118140960795 + 2739732 * 2 ^ 59
def prefixEnd_2739732 : Nat := 4983230072969 + 3 ^ 40 * 2739732 * 2
def baseEnd_2739732 : Nat := 312622084556440004366713

theorem tailTrace_2739732 : CollatzResearch.WordTrace tailWord_2739732 prefixEnd_2739732 312622084556440004366713 := by
  unfold tailWord_2739732
  simp only [CollatzResearch.WordTrace]
  refine ⟨49963117655213173909286725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66617490206950898545715633 49963117655213173909286725)
  ·
    refine ⟨9368084560352470107991261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49963117655213173909286725 9368084560352470107991261)
    ·
      refine ⟨3513031710132176290496723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9368084560352470107991261 3513031710132176290496723)
      ·
        refine ⟨5269547565198264435745085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3513031710132176290496723 5269547565198264435745085)
        ·
          refine ⟨1976080336949349163404407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5269547565198264435745085 1976080336949349163404407)
          ·
            refine ⟨2964120505424023745106611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976080336949349163404407 2964120505424023745106611)
            ·
              refine ⟨4446180758136035617659917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964120505424023745106611 4446180758136035617659917)
              ·
                refine ⟨1667317784301013356622469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4446180758136035617659917 1667317784301013356622469)
                ·
                  refine ⟨312622084556440004366713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1667317784301013356622469 312622084556440004366713)
                  ·
                    rfl

theorem cell22_2739732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_2739732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739732 prefixEnd_2739732 := by exact prefixLift 2739732
  have htrace : WordTrace (prefixWord ++ tailWord_2739732) baseStart_2739732 baseEnd_2739732 := by
    simpa [prefixWord, tailWord_2739732, baseEnd_2739732] using wordTrace_append hprefix tailTrace_2739732
  have hstable : (prefixWord ++ tailWord_2739732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739732).length < 2 ^ (prefixWord ++ tailWord_2739732).sum := by decide
  have hdescent : baseEnd_2739732 < baseStart_2739732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739754 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_2739754 : Nat := 118140960795 + 2739754 * 2 ^ 59
def prefixEnd_2739754 : Nat := 4983230072969 + 3 ^ 40 * 2739754 * 2
def baseEnd_2739754 : Nat := 312624594906306429683357

theorem tailTrace_2739754 : CollatzResearch.WordTrace tailWord_2739754 prefixEnd_2739754 312624594906306429683357 := by
  unfold tailWord_2739754
  simp only [CollatzResearch.WordTrace]
  refine ⟨24981759429086661393968579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66618025144231097050582877 24981759429086661393968579)
  ·
    refine ⟨37472639143629992090952869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24981759429086661393968579 37472639143629992090952869)
    ·
      refine ⟨7026119839430623517053663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37472639143629992090952869 7026119839430623517053663)
      ·
        refine ⟨10539179759145935275580495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7026119839430623517053663 10539179759145935275580495)
        ·
          refine ⟨15808769638718902913370743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10539179759145935275580495 15808769638718902913370743)
          ·
            refine ⟨23713154458078354370056115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15808769638718902913370743 23713154458078354370056115)
            ·
              refine ⟨35569731687117531555084173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23713154458078354370056115 35569731687117531555084173)
              ·
                refine ⟨13338649382669074333156565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35569731687117531555084173 13338649382669074333156565)
                ·
                  refine ⟨312624594906306429683357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13338649382669074333156565 312624594906306429683357)
                  ·
                    rfl

theorem cell22_2739754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_2739754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739754 prefixEnd_2739754 := by exact prefixLift 2739754
  have htrace : WordTrace (prefixWord ++ tailWord_2739754) baseStart_2739754 baseEnd_2739754 := by
    simpa [prefixWord, tailWord_2739754, baseEnd_2739754] using wordTrace_append hprefix tailTrace_2739754
  have hstable : (prefixWord ++ tailWord_2739754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739754).length < 2 ^ (prefixWord ++ tailWord_2739754).sum := by decide
  have hdescent : baseEnd_2739754 < baseStart_2739754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739758 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2739758 : Nat := 118140960795 + 2739758 * 2 ^ 59
def prefixEnd_2739758 : Nat := 4983230072969 + 3 ^ 40 * 2739758 * 2
def baseEnd_2739758 : Nat := 937875154000664611950059

theorem tailTrace_2739758 : CollatzResearch.WordTrace tailWord_2739758 prefixEnd_2739758 937875154000664611950059 := by
  unfold tailWord_2739758
  simp only [CollatzResearch.WordTrace]
  refine ⟨12490897951041519282377491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66618122405554769506013285 12490897951041519282377491)
  ·
    refine ⟨18736346926562278923566237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12490897951041519282377491 18736346926562278923566237)
    ·
      refine ⟨7026130097460854596337339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18736346926562278923566237 7026130097460854596337339)
      ·
        refine ⟨10539195146191281894506009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7026130097460854596337339 10539195146191281894506009)
        ·
          refine ⟨7904396359643461420879507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10539195146191281894506009 7904396359643461420879507)
          ·
            refine ⟨11856594539465192131319261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7904396359643461420879507 11856594539465192131319261)
            ·
              refine ⟨4446222952299447049244723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11856594539465192131319261 4446222952299447049244723)
              ·
                refine ⟨6669334428449170573867085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4446222952299447049244723 6669334428449170573867085)
                ·
                  refine ⟨2501000410668438965200157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6669334428449170573867085 2501000410668438965200157)
                  ·
                    refine ⟨937875154000664611950059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2501000410668438965200157 937875154000664611950059)
                    ·
                      rfl

theorem cell22_2739758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2739758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739758 prefixEnd_2739758 := by exact prefixLift 2739758
  have htrace : WordTrace (prefixWord ++ tailWord_2739758) baseStart_2739758 baseEnd_2739758 := by
    simpa [prefixWord, tailWord_2739758, baseEnd_2739758] using wordTrace_append hprefix tailTrace_2739758
  have hstable : (prefixWord ++ tailWord_2739758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739758).length < 2 ^ (prefixWord ++ tailWord_2739758).sum := by decide
  have hdescent : baseEnd_2739758 < baseStart_2739758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739805 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 5]
def baseStart_2739805 : Nat := 118140960795 + 2739805 * 2 ^ 59
def prefixEnd_2739805 : Nat := 4983230072969 + 3 ^ 40 * 2739805 * 2
def baseEnd_2739805 : Nat := 312630414353724052008305

theorem tailTrace_2739805 : CollatzResearch.WordTrace tailWord_2739805 prefixEnd_2739805 312630414353724052008305 := by
  unfold tailWord_2739805
  simp only [CollatzResearch.WordTrace]
  refine ⟨99928897839161881285980869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66619265226107920857320579 99928897839161881285980869)
  ·
    refine ⟨18736668344842852741121413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99928897839161881285980869 18736668344842852741121413)
    ·
      refine ⟨3513125314658034888960265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18736668344842852741121413 3513125314658034888960265)
      ·
        refine ⟨2634843985993526166720199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3513125314658034888960265 2634843985993526166720199)
        ·
          refine ⟨3952265978990289250080299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2634843985993526166720199 3952265978990289250080299)
          ·
            refine ⟨5928398968485433875120449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952265978990289250080299 5928398968485433875120449)
            ·
              refine ⟨4446299226364075406340337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5928398968485433875120449 4446299226364075406340337)
              ·
                refine ⟨3334724419773056554755253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4446299226364075406340337 3334724419773056554755253)
                ·
                  refine ⟨312630414353724052008305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3334724419773056554755253 312630414353724052008305)
                  ·
                    rfl

theorem cell22_2739805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_2739805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739805 prefixEnd_2739805 := by exact prefixLift 2739805
  have htrace : WordTrace (prefixWord ++ tailWord_2739805) baseStart_2739805 baseEnd_2739805 := by
    simpa [prefixWord, tailWord_2739805, baseEnd_2739805] using wordTrace_append hprefix tailTrace_2739805
  have hstable : (prefixWord ++ tailWord_2739805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739805).length < 2 ^ (prefixWord ++ tailWord_2739805).sum := by decide
  have hdescent : baseEnd_2739805 < baseStart_2739805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2739953 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 1, 4]
def baseStart_2739953 : Nat := 118140960795 + 2739953 * 2 ^ 59
def prefixEnd_2739953 : Nat := 4983230072969 + 3 ^ 40 * 2739953 * 2
def baseEnd_2739953 : Nat := 937941906485749103324461

theorem tailTrace_2739953 : CollatzResearch.WordTrace tailWord_2739953 prefixEnd_2739953 937941906485749103324461 := by
  unfold tailWord_2739953
  simp only [CollatzResearch.WordTrace]
  refine ⟨99934295842625702562368513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66622863895083801708245675 99934295842625702562368513)
  ·
    refine ⟨74950721881969276921776385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99934295842625702562368513 74950721881969276921776385)
    ·
      refine ⟨56213041411476957691332289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74950721881969276921776385 56213041411476957691332289)
      ·
        refine ⟨42159781058607718268499217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56213041411476957691332289 42159781058607718268499217)
        ·
          refine ⟨31619835793955788701374413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42159781058607718268499217 31619835793955788701374413)
          ·
            refine ⟨11857438422733420763015405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31619835793955788701374413 11857438422733420763015405)
            ·
              refine ⟨4446539408525032786130777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11857438422733420763015405 4446539408525032786130777)
              ·
                refine ⟨3334904556393774589598083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4446539408525032786130777 3334904556393774589598083)
                ·
                  refine ⟨5002356834590661884397125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334904556393774589598083 5002356834590661884397125)
                  ·
                    refine ⟨937941906485749103324461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5002356834590661884397125 937941906485749103324461)
                    ·
                      rfl

theorem cell22_2739953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_2739953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2739953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2739953 prefixEnd_2739953 := by exact prefixLift 2739953
  have htrace : WordTrace (prefixWord ++ tailWord_2739953) baseStart_2739953 baseEnd_2739953 := by
    simpa [prefixWord, tailWord_2739953, baseEnd_2739953] using wordTrace_append hprefix tailTrace_2739953
  have hstable : (prefixWord ++ tailWord_2739953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2739953).length < 2 ^ (prefixWord ++ tailWord_2739953).sum := by decide
  have hdescent : baseEnd_2739953 < baseStart_2739953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2739953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740041 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 7]
def baseStart_2740041 : Nat := 118140960795 + 2740041 * 2 ^ 59
def prefixEnd_2740041 : Nat := 4983230072969 + 3 ^ 40 * 2740041 * 2
def baseEnd_2740041 : Nat := 312657343561382069041397

theorem tailTrace_2740041 : CollatzResearch.WordTrace tailWord_2740041 prefixEnd_2740041 312657343561382069041397 := by
  unfold tailWord_2740041
  simp only [CollatzResearch.WordTrace]
  refine ⟨99937505466306893591571977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66625003644204595727714651 99937505466306893591571977)
  ·
    refine ⟨74953129099730170193678983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99937505466306893591571977 74953129099730170193678983)
    ·
      refine ⟨112429693649595255290518475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74953129099730170193678983 112429693649595255290518475)
      ·
        refine ⟨168644540474392882935777713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112429693649595255290518475 168644540474392882935777713)
        ·
          refine ⟨126483405355794662201833285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168644540474392882935777713 126483405355794662201833285)
          ·
            refine ⟨23715638504211499162843741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126483405355794662201833285 23715638504211499162843741)
            ·
              refine ⟨8893364439079312186066403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23715638504211499162843741 8893364439079312186066403)
              ·
                refine ⟨13340046658618968279099605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8893364439079312186066403 13340046658618968279099605)
                ·
                  refine ⟨312657343561382069041397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13340046658618968279099605 312657343561382069041397)
                  ·
                    rfl

theorem cell22_2740041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_2740041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740041 prefixEnd_2740041 := by exact prefixLift 2740041
  have htrace : WordTrace (prefixWord ++ tailWord_2740041) baseStart_2740041 baseEnd_2740041 := by
    simpa [prefixWord, tailWord_2740041, baseEnd_2740041] using wordTrace_append hprefix tailTrace_2740041
  have hstable : (prefixWord ++ tailWord_2740041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740041).length < 2 ^ (prefixWord ++ tailWord_2740041).sum := by decide
  have hdescent : baseEnd_2740041 < baseStart_2740041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740122 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 1, 4]
def baseStart_2740122 : Nat := 118140960795 + 2740122 * 2 ^ 59
def prefixEnd_2740122 : Nat := 4983230072969 + 3 ^ 40 * 2740122 * 2
def baseEnd_2740122 : Nat := 937999758639488995848943

theorem tailTrace_2740122 : CollatzResearch.WordTrace tailWord_2740122 prefixEnd_2740122 937999758639488995848943 := by
  unfold tailWord_2740122
  simp only [CollatzResearch.WordTrace]
  refine ⟨24985114944753361106317655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66626973186008962950180413 24985114944753361106317655)
  ·
    refine ⟨37477672417130041659476483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24985114944753361106317655 37477672417130041659476483)
    ·
      refine ⟨56216508625695062489214725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37477672417130041659476483 56216508625695062489214725)
      ·
        refine ⟨10540595367317824216727761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56216508625695062489214725 10540595367317824216727761)
        ·
          refine ⟨7905446525488368162545821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10540595367317824216727761 7905446525488368162545821)
          ·
            refine ⟨2964542447058138060954683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7905446525488368162545821 2964542447058138060954683)
            ·
              refine ⟨4446813670587207091432025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964542447058138060954683 4446813670587207091432025)
              ·
                refine ⟨3335110252940405318574019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4446813670587207091432025 3335110252940405318574019)
                ·
                  refine ⟨5002665379410607977861029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335110252940405318574019 5002665379410607977861029)
                  ·
                    refine ⟨937999758639488995848943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5002665379410607977861029 937999758639488995848943)
                    ·
                      rfl

theorem cell22_2740122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_2740122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740122 prefixEnd_2740122 := by exact prefixLift 2740122
  have htrace : WordTrace (prefixWord ++ tailWord_2740122) baseStart_2740122 baseEnd_2740122 := by
    simpa [prefixWord, tailWord_2740122, baseEnd_2740122] using wordTrace_append hprefix tailTrace_2740122
  have hstable : (prefixWord ++ tailWord_2740122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740122).length < 2 ^ (prefixWord ++ tailWord_2740122).sum := by decide
  have hdescent : baseEnd_2740122 < baseStart_2740122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740135 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2740135 : Nat := 118140960795 + 2740135 * 2 ^ 59
def prefixEnd_2740135 : Nat := 4983230072969 + 3 ^ 40 * 2740135 * 2
def baseEnd_2740135 : Nat := 938004208805161295273903

theorem tailTrace_2740135 : CollatzResearch.WordTrace tailWord_2740135 prefixEnd_2740135 938004208805161295273903 := by
  unfold tailWord_2740135
  simp only [CollatzResearch.WordTrace]
  refine ⟨99940933927966347645493859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66627289285310898430329239 99940933927966347645493859)
  ·
    refine ⟨149911400891949521468240789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99940933927966347645493859 149911400891949521468240789)
    ·
      refine ⟨7027096916810133818823787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149911400891949521468240789 7027096916810133818823787)
      ·
        refine ⟨10540645375215200728235681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7027096916810133818823787 10540645375215200728235681)
        ·
          refine ⟨7905484031411400546176761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10540645375215200728235681 7905484031411400546176761)
          ·
            refine ⟨5929113023558550409632571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7905484031411400546176761 5929113023558550409632571)
            ·
              refine ⟨8893669535337825614448857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5929113023558550409632571 8893669535337825614448857)
              ·
                refine ⟨6670252151503369210836643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8893669535337825614448857 6670252151503369210836643)
                ·
                  refine ⟨10005378227255053816254965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6670252151503369210836643 10005378227255053816254965)
                  ·
                    refine ⟨938004208805161295273903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10005378227255053816254965 938004208805161295273903)
                    ·
                      rfl

theorem cell22_2740135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2740135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740135 prefixEnd_2740135 := by exact prefixLift 2740135
  have htrace : WordTrace (prefixWord ++ tailWord_2740135) baseStart_2740135 baseEnd_2740135 := by
    simpa [prefixWord, tailWord_2740135, baseEnd_2740135] using wordTrace_append hprefix tailTrace_2740135
  have hstable : (prefixWord ++ tailWord_2740135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740135).length < 2 ^ (prefixWord ++ tailWord_2740135).sum := by decide
  have hdescent : baseEnd_2740135 < baseStart_2740135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740208 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_2740208 : Nat := 118140960795 + 2740208 * 2 ^ 59
def prefixEnd_2740208 : Nat := 4983230072969 + 3 ^ 40 * 2740208 * 2
def baseEnd_2740208 : Nat := 938029198197013438198679

theorem tailTrace_2740208 : CollatzResearch.WordTrace tailWord_2740208 prefixEnd_2740208 938029198197013438198679 := by
  unfold tailWord_2740208
  simp only [CollatzResearch.WordTrace]
  refine ⟨49971798228350940556450639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66629064304467920741934185 49971798228350940556450639)
  ·
    refine ⟨74957697342526410834675959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49971798228350940556450639 74957697342526410834675959)
    ·
      refine ⟨112436546013789616252013939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74957697342526410834675959 112436546013789616252013939)
      ·
        refine ⟨168654819020684424378020909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112436546013789616252013939 168654819020684424378020909)
        ·
          refine ⟨63245557132756659141757841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168654819020684424378020909 63245557132756659141757841)
          ·
            refine ⟨47434167849567494356318381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63245557132756659141757841 47434167849567494356318381)
            ·
              refine ⟨17787812943587810383619393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47434167849567494356318381 17787812943587810383619393)
              ·
                refine ⟨13340859707690857787714545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17787812943587810383619393 13340859707690857787714545)
                ·
                  refine ⟨10005644780768143340785909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13340859707690857787714545 10005644780768143340785909)
                  ·
                    refine ⟨938029198197013438198679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10005644780768143340785909 938029198197013438198679)
                    ·
                      rfl

theorem cell22_2740208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_2740208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740208 prefixEnd_2740208 := by exact prefixLift 2740208
  have htrace : WordTrace (prefixWord ++ tailWord_2740208) baseStart_2740208 baseEnd_2740208 := by
    simpa [prefixWord, tailWord_2740208, baseEnd_2740208] using wordTrace_append hprefix tailTrace_2740208
  have hstable : (prefixWord ++ tailWord_2740208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740208).length < 2 ^ (prefixWord ++ tailWord_2740208).sum := by decide
  have hdescent : baseEnd_2740208 < baseStart_2740208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740214 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_2740214 : Nat := 118140960795 + 2740214 * 2 ^ 59
def prefixEnd_2740214 : Nat := 4983230072969 + 3 ^ 40 * 2740214 * 2
def baseEnd_2740214 : Nat := 938031252119631422548661

theorem tailTrace_2740214 : CollatzResearch.WordTrace tailWord_2740214 prefixEnd_2740214 938031252119631422548661 := by
  unfold tailWord_2740214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246488455917509008601231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66629210196453429425079797 6246488455917509008601231)
  ·
    refine ⟨9369732683876263512901847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6246488455917509008601231 9369732683876263512901847)
    ·
      refine ⟨14054599025814395269352771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9369732683876263512901847 14054599025814395269352771)
      ·
        refine ⟨21081898538721592904029157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14054599025814395269352771 21081898538721592904029157)
        ·
          refine ⟨3952855976010298669505467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21081898538721592904029157 3952855976010298669505467)
          ·
            refine ⟨5929283964015448004258201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952855976010298669505467 5929283964015448004258201)
            ·
              refine ⟨4446962973011586003193651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5929283964015448004258201 4446962973011586003193651)
              ·
                refine ⟨6670444459517379004790477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4446962973011586003193651 6670444459517379004790477)
                ·
                  refine ⟨2501416672319017126796429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6670444459517379004790477 2501416672319017126796429)
                  ·
                    refine ⟨938031252119631422548661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2501416672319017126796429 938031252119631422548661)
                    ·
                      rfl

theorem cell22_2740214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_2740214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740214 prefixEnd_2740214 := by exact prefixLift 2740214
  have htrace : WordTrace (prefixWord ++ tailWord_2740214) baseStart_2740214 baseEnd_2740214 := by
    simpa [prefixWord, tailWord_2740214, baseEnd_2740214] using wordTrace_append hprefix tailTrace_2740214
  have hstable : (prefixWord ++ tailWord_2740214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740214).length < 2 ^ (prefixWord ++ tailWord_2740214).sum := by decide
  have hdescent : baseEnd_2740214 < baseStart_2740214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740223 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 5, 4]
def baseStart_2740223 : Nat := 118140960795 + 2740223 * 2 ^ 59
def prefixEnd_2740223 : Nat := 4983230072969 + 3 ^ 40 * 2740223 * 2
def baseEnd_2740223 : Nat := 938034333003558399073633

theorem tailTrace_2740223 : CollatzResearch.WordTrace tailWord_2740223 prefixEnd_2740223 938034333003558399073633 := by
  unfold tailWord_2740223
  simp only [CollatzResearch.WordTrace]
  refine ⟨99944143551647538674697323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66629429034431692449798215 99944143551647538674697323)
  ·
    refine ⟨149916215327471308012045985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99944143551647538674697323 149916215327471308012045985)
    ·
      refine ⟨112437161495603481009034489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149916215327471308012045985 112437161495603481009034489)
      ·
        refine ⟨84327871121702610756775867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112437161495603481009034489 84327871121702610756775867)
        ·
          refine ⟨126491806682553916135163801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84327871121702610756775867 126491806682553916135163801)
          ·
            refine ⟨94868855011915437101372851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126491806682553916135163801 94868855011915437101372851)
            ·
              refine ⟨142303282517873155652059277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94868855011915437101372851 142303282517873155652059277)
              ·
                refine ⟨53363730944202433369522229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142303282517873155652059277 53363730944202433369522229)
                ·
                  refine ⟨5002849776018978128392709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53363730944202433369522229 5002849776018978128392709)
                  ·
                    refine ⟨938034333003558399073633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5002849776018978128392709 938034333003558399073633)
                    ·
                      rfl

theorem cell22_2740223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_2740223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740223 prefixEnd_2740223 := by exact prefixLift 2740223
  have htrace : WordTrace (prefixWord ++ tailWord_2740223) baseStart_2740223 baseEnd_2740223 := by
    simpa [prefixWord, tailWord_2740223, baseEnd_2740223] using wordTrace_append hprefix tailTrace_2740223
  have hstable : (prefixWord ++ tailWord_2740223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740223).length < 2 ^ (prefixWord ++ tailWord_2740223).sum := by decide
  have hdescent : baseEnd_2740223 < baseStart_2740223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740268 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_2740268 : Nat := 118140960795 + 2740268 * 2 ^ 59
def prefixEnd_2740268 : Nat := 4983230072969 + 3 ^ 40 * 2740268 * 2
def baseEnd_2740268 : Nat := 938049737423193281698495

theorem tailTrace_2740268 : CollatzResearch.WordTrace tailWord_2740268 prefixEnd_2740268 938049737423193281698495 := by
  unfold tailWord_2740268
  simp only [CollatzResearch.WordTrace]
  refine ⟨49972892418242255680042729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66630523224323007573390305 49972892418242255680042729)
  ·
    refine ⟨37479669313681691760032047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49972892418242255680042729 37479669313681691760032047)
    ·
      refine ⟨56219503970522537640048071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37479669313681691760032047 56219503970522537640048071)
      ·
        refine ⟨84329255955783806460072107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56219503970522537640048071 84329255955783806460072107)
        ·
          refine ⟨126493883933675709690108161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84329255955783806460072107 126493883933675709690108161)
          ·
            refine ⟨94870412950256782267581121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126493883933675709690108161 94870412950256782267581121)
            ·
              refine ⟨71152809712692586700685841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94870412950256782267581121 71152809712692586700685841)
              ·
                refine ⟨53364607284519440025514381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71152809712692586700685841 53364607284519440025514381)
                ·
                  refine ⟨20011727731694790009567893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53364607284519440025514381 20011727731694790009567893)
                  ·
                    refine ⟨938049737423193281698495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20011727731694790009567893 938049737423193281698495)
                    ·
                      rfl

theorem cell22_2740268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_2740268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740268 prefixEnd_2740268 := by exact prefixLift 2740268
  have htrace : WordTrace (prefixWord ++ tailWord_2740268) baseStart_2740268 baseEnd_2740268 := by
    simpa [prefixWord, tailWord_2740268, baseEnd_2740268] using wordTrace_append hprefix tailTrace_2740268
  have hstable : (prefixWord ++ tailWord_2740268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740268).length < 2 ^ (prefixWord ++ tailWord_2740268).sum := by decide
  have hdescent : baseEnd_2740268 < baseStart_2740268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740285 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_2740285 : Nat := 118140960795 + 2740285 * 2 ^ 59
def prefixEnd_2740285 : Nat := 4983230072969 + 3 ^ 40 * 2740285 * 2
def baseEnd_2740285 : Nat := 938055556870610904023443

theorem tailTrace_2740285 : CollatzResearch.WordTrace tailWord_2740285 prefixEnd_2740285 938055556870610904023443 := by
  unfold tailWord_2740285
  simp only [CollatzResearch.WordTrace]
  refine ⟨99946404877422923263454309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66630936584948615508969539 99946404877422923263454309)
  ·
    refine ⟨18739950914516798111897683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99946404877422923263454309 18739950914516798111897683)
    ·
      refine ⟨28109926371775197167846525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18739950914516798111897683 28109926371775197167846525)
      ·
        refine ⟨10541222389415698937942447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28109926371775197167846525 10541222389415698937942447)
        ·
          refine ⟨15811833584123548406913671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10541222389415698937942447 15811833584123548406913671)
          ·
            refine ⟨23717750376185322610370507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15811833584123548406913671 23717750376185322610370507)
            ·
              refine ⟨35576625564277983915555761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23717750376185322610370507 35576625564277983915555761)
              ·
                refine ⟨26682469173208487936666821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35576625564277983915555761 26682469173208487936666821)
                ·
                  refine ⟨5002962969976591488125029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26682469173208487936666821 5002962969976591488125029)
                  ·
                    refine ⟨938055556870610904023443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5002962969976591488125029 938055556870610904023443)
                    ·
                      rfl

theorem cell22_2740285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_2740285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740285 prefixEnd_2740285 := by exact prefixLift 2740285
  have htrace : WordTrace (prefixWord ++ tailWord_2740285) baseStart_2740285 baseEnd_2740285 := by
    simpa [prefixWord, tailWord_2740285, baseEnd_2740285] using wordTrace_append hprefix tailTrace_2740285
  have hstable : (prefixWord ++ tailWord_2740285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740285).length < 2 ^ (prefixWord ++ tailWord_2740285).sum := by decide
  have hdescent : baseEnd_2740285 < baseStart_2740285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740302 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_2740302 : Nat := 118140960795 + 2740302 * 2 ^ 59
def prefixEnd_2740302 : Nat := 4983230072969 + 3 ^ 40 * 2740302 * 2
def baseEnd_2740302 : Nat := 938061376318028526348391

theorem tailTrace_2740302 : CollatzResearch.WordTrace tailWord_2740302 prefixEnd_2740302 938061376318028526348391 := by
  unfold tailWord_2740302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12493378114795166895852895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66631349945574223444548773 12493378114795166895852895)
  ·
    refine ⟨18740067172192750343779343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12493378114795166895852895 18740067172192750343779343)
    ·
      refine ⟨28110100758289125515669015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18740067172192750343779343 28110100758289125515669015)
      ·
        refine ⟨42165151137433688273503523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28110100758289125515669015 42165151137433688273503523)
        ·
          refine ⟨63247726706150532410255285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42165151137433688273503523 63247726706150532410255285)
          ·
            refine ⟨5929474378701612413461433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63247726706150532410255285 5929474378701612413461433)
            ·
              refine ⟨4447105784026209310096075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5929474378701612413461433 4447105784026209310096075)
              ·
                refine ⟨6670658676039313965144113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4447105784026209310096075 6670658676039313965144113)
                ·
                  refine ⟨5002994007029485473858085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6670658676039313965144113 5002994007029485473858085)
                  ·
                    refine ⟨938061376318028526348391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5002994007029485473858085 938061376318028526348391)
                    ·
                      rfl

theorem cell22_2740302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_2740302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740302 prefixEnd_2740302 := by exact prefixLift 2740302
  have htrace : WordTrace (prefixWord ++ tailWord_2740302) baseStart_2740302 baseEnd_2740302 := by
    simpa [prefixWord, tailWord_2740302, baseEnd_2740302] using wordTrace_append hprefix tailTrace_2740302
  have hstable : (prefixWord ++ tailWord_2740302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740302).length < 2 ^ (prefixWord ++ tailWord_2740302).sum := by decide
  have hdescent : baseEnd_2740302 < baseStart_2740302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740456 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 2, 3]
def baseStart_2740456 : Nat := 118140960795 + 2740456 * 2 ^ 59
def prefixEnd_2740456 : Nat := 4983230072969 + 3 ^ 40 * 2740456 * 2
def baseEnd_2740456 : Nat := 938114093665223457997919

theorem tailTrace_2740456 : CollatzResearch.WordTrace tailWord_2740456 prefixEnd_2740456 938114093665223457997919 := by
  unfold tailWord_2740456
  simp only [CollatzResearch.WordTrace]
  refine ⟨49976320879901709733964611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66635094506535612978619481 49976320879901709733964611)
  ·
    refine ⟨74964481319852564600946917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49976320879901709733964611 74964481319852564600946917)
    ·
      refine ⟨14055840247472355862677547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74964481319852564600946917 14055840247472355862677547)
      ·
        refine ⟨21083760371208533794016321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14055840247472355862677547 21083760371208533794016321)
        ·
          refine ⟨15812820278406400345512241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21083760371208533794016321 15812820278406400345512241)
          ·
            refine ⟨11859615208804800259134181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15812820278406400345512241 11859615208804800259134181)
            ·
              refine ⟨2223677851650900048587659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11859615208804800259134181 2223677851650900048587659)
              ·
                refine ⟨3335516777476350072881489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223677851650900048587659 3335516777476350072881489)
                ·
                  refine ⟨2501637583107262554661117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3335516777476350072881489 2501637583107262554661117)
                  ·
                    refine ⟨938114093665223457997919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2501637583107262554661117 938114093665223457997919)
                    ·
                      rfl

theorem cell22_2740456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_2740456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740456 prefixEnd_2740456 := by exact prefixLift 2740456
  have htrace : WordTrace (prefixWord ++ tailWord_2740456) baseStart_2740456 baseEnd_2740456 := by
    simpa [prefixWord, tailWord_2740456, baseEnd_2740456] using wordTrace_append hprefix tailTrace_2740456
  have hstable : (prefixWord ++ tailWord_2740456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740456).length < 2 ^ (prefixWord ++ tailWord_2740456).sum := by decide
  have hdescent : baseEnd_2740456 < baseStart_2740456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740467 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 5, 3]
def baseStart_2740467 : Nat := 118140960795 + 2740467 * 2 ^ 59
def prefixEnd_2740467 : Nat := 4983230072969 + 3 ^ 40 * 2740467 * 2
def baseEnd_2740467 : Nat := 938117859190023095972885

theorem tailTrace_2740467 : CollatzResearch.WordTrace tailWord_2740467 prefixEnd_2740467 938117859190023095972885 := by
  unfold tailWord_2740467
  simp only [CollatzResearch.WordTrace]
  refine ⟨99953042962763568346579655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66635361975175712231053103 99953042962763568346579655)
  ·
    refine ⟨149929564444145352519869483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99953042962763568346579655 149929564444145352519869483)
    ·
      refine ⟨224894346666218028779804225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149929564444145352519869483 224894346666218028779804225)
      ·
        refine ⟨168670759999663521584853169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224894346666218028779804225 168670759999663521584853169)
        ·
          refine ⟨126503069999747641188639877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168670759999663521584853169 126503069999747641188639877)
          ·
            refine ⟨23719325624952682722869977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126503069999747641188639877 23719325624952682722869977)
            ·
              refine ⟨17789494218714512042152483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23719325624952682722869977 17789494218714512042152483)
              ·
                refine ⟨26684241328071768063228725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17789494218714512042152483 26684241328071768063228725)
                ·
                  refine ⟨2501647624506728255927693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26684241328071768063228725 2501647624506728255927693)
                  ·
                    refine ⟨938117859190023095972885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2501647624506728255927693 938117859190023095972885)
                    ·
                      rfl

theorem cell22_2740467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 3].length) (baseStart_2740467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740467 prefixEnd_2740467 := by exact prefixLift 2740467
  have htrace : WordTrace (prefixWord ++ tailWord_2740467) baseStart_2740467 baseEnd_2740467 := by
    simpa [prefixWord, tailWord_2740467, baseEnd_2740467] using wordTrace_append hprefix tailTrace_2740467
  have hstable : (prefixWord ++ tailWord_2740467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740467).length < 2 ^ (prefixWord ++ tailWord_2740467).sum := by decide
  have hdescent : baseEnd_2740467 < baseStart_2740467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740480 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 9]
def baseStart_2740480 : Nat := 118140960795 + 2740480 * 2 ^ 59
def prefixEnd_2740480 : Nat := 4983230072969 + 3 ^ 40 * 2740480 * 2
def baseEnd_2740480 : Nat := 312707436451898465132615

theorem tailTrace_2740480 : CollatzResearch.WordTrace tailWord_2740480 prefixEnd_2740480 312707436451898465132615 := by
  unfold tailWord_2740480
  simp only [CollatzResearch.WordTrace]
  refine ⟨49976758555858235783401447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66635678074477647711201929 49976758555858235783401447)
  ·
    refine ⟨74965137833787353675102171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49976758555858235783401447 74965137833787353675102171)
    ·
      refine ⟨112447706750681030512653257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74965137833787353675102171 112447706750681030512653257)
      ·
        refine ⟨84335780063010772884489943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112447706750681030512653257 84335780063010772884489943)
        ·
          refine ⟨126503670094516159326734915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84335780063010772884489943 126503670094516159326734915)
          ·
            refine ⟨189755505141774238990102373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126503670094516159326734915 189755505141774238990102373)
            ·
              refine ⟨35579157214082669810644195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189755505141774238990102373 35579157214082669810644195)
              ·
                refine ⟨53368735821124004715966293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35579157214082669810644195 53368735821124004715966293)
                ·
                  refine ⟨312707436451898465132615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53368735821124004715966293 312707436451898465132615)
                  ·
                    rfl

theorem cell22_2740480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_2740480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740480 prefixEnd_2740480 := by exact prefixLift 2740480
  have htrace : WordTrace (prefixWord ++ tailWord_2740480) baseStart_2740480 baseEnd_2740480 := by
    simpa [prefixWord, tailWord_2740480, baseEnd_2740480] using wordTrace_append hprefix tailTrace_2740480
  have hstable : (prefixWord ++ tailWord_2740480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740480).length < 2 ^ (prefixWord ++ tailWord_2740480).sum := by decide
  have hdescent : baseEnd_2740480 < baseStart_2740480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740495 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 3, 7]
def baseStart_2740495 : Nat := 118140960795 + 2740495 * 2 ^ 59
def prefixEnd_2740495 : Nat := 4983230072969 + 3 ^ 40 * 2740495 * 2
def baseEnd_2740495 : Nat := 938127444162240356272799

theorem tailTrace_2740495 : CollatzResearch.WordTrace tailWord_2740495 prefixEnd_2740495 938127444162240356272799 := by
  unfold tailWord_2740495
  simp only [CollatzResearch.WordTrace]
  refine ⟨99954064206662129128598939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66636042804441419419065959 99954064206662129128598939)
  ·
    refine ⟨149931096309993193692898409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99954064206662129128598939 149931096309993193692898409)
    ·
      refine ⟨112448322232494895269673807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149931096309993193692898409 112448322232494895269673807)
      ·
        refine ⟨168672483348742342904510711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112448322232494895269673807 168672483348742342904510711)
        ·
          refine ⟨253008725023113514356766067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168672483348742342904510711 253008725023113514356766067)
          ·
            refine ⟨379513087534670271535149101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253008725023113514356766067 379513087534670271535149101)
            ·
              refine ⟨142317407825501351825680913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379513087534670271535149101 142317407825501351825680913)
              ·
                refine ⟨106738055869126013869260685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142317407825501351825680913 106738055869126013869260685)
                ·
                  refine ⟨40026770950922255200972757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106738055869126013869260685 40026770950922255200972757)
                  ·
                    refine ⟨938127444162240356272799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40026770950922255200972757 938127444162240356272799)
                    ·
                      rfl

theorem cell22_2740495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_2740495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740495 prefixEnd_2740495 := by exact prefixLift 2740495
  have htrace : WordTrace (prefixWord ++ tailWord_2740495) baseStart_2740495 baseEnd_2740495 := by
    simpa [prefixWord, tailWord_2740495, baseEnd_2740495] using wordTrace_append hprefix tailTrace_2740495
  have hstable : (prefixWord ++ tailWord_2740495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740495).length < 2 ^ (prefixWord ++ tailWord_2740495).sum := by decide
  have hdescent : baseEnd_2740495 < baseStart_2740495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740497 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 5]
def baseStart_2740497 : Nat := 118140960795 + 2740497 * 2 ^ 59
def prefixEnd_2740497 : Nat := 4983230072969 + 3 ^ 40 * 2740497 * 2
def baseEnd_2740497 : Nat := 312709376267704339240931

theorem tailTrace_2740497 : CollatzResearch.WordTrace tailWord_2740497 prefixEnd_2740497 312709376267704339240931 := by
  unfold tailWord_2740497
  simp only [CollatzResearch.WordTrace]
  refine ⟨99954137152654883470171745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66636091435103255646781163 99954137152654883470171745)
  ·
    refine ⟨74965602864491162602628809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99954137152654883470171745 74965602864491162602628809)
    ·
      refine ⟨56224202148368371951971607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74965602864491162602628809 56224202148368371951971607)
      ·
        refine ⟨84336303222552557927957411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56224202148368371951971607 84336303222552557927957411)
        ·
          refine ⟨126504454833828836891936117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84336303222552557927957411 126504454833828836891936117)
          ·
            refine ⟨11859792640671453458619011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126504454833828836891936117 11859792640671453458619011)
            ·
              refine ⟨17789688961007180187928517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11859792640671453458619011 17789688961007180187928517)
              ·
                refine ⟨3335566680188846285236597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17789688961007180187928517 3335566680188846285236597)
                ·
                  refine ⟨312709376267704339240931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3335566680188846285236597 312709376267704339240931)
                  ·
                    rfl

theorem cell22_2740497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_2740497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740497 prefixEnd_2740497 := by exact prefixLift 2740497
  have htrace : WordTrace (prefixWord ++ tailWord_2740497) baseStart_2740497 baseEnd_2740497 := by
    simpa [prefixWord, tailWord_2740497, baseEnd_2740497] using wordTrace_append hprefix tailTrace_2740497
  have hstable : (prefixWord ++ tailWord_2740497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740497).length < 2 ^ (prefixWord ++ tailWord_2740497).sum := by decide
  have hdescent : baseEnd_2740497 < baseStart_2740497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740512 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 1, 7]
def baseStart_2740512 : Nat := 118140960795 + 2740512 * 2 ^ 59
def prefixEnd_2740512 : Nat := 4983230072969 + 3 ^ 40 * 2740512 * 2
def baseEnd_2740512 : Nat := 938133263609657978597747

theorem tailTrace_2740512 : CollatzResearch.WordTrace tailWord_2740512 prefixEnd_2740512 938133263609657978597747 := by
  unfold tailWord_2740512
  simp only [CollatzResearch.WordTrace]
  refine ⟨49977342123800270515983895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66636456165067027354645193 49977342123800270515983895)
  ·
    refine ⟨74966013185700405773975843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49977342123800270515983895 74966013185700405773975843)
    ·
      refine ⟨112449019778550608660963765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74966013185700405773975843 112449019778550608660963765)
      ·
        refine ⟨10542095604239119561965353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112449019778550608660963765 10542095604239119561965353)
        ·
          refine ⟨7906571703179339671474015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10542095604239119561965353 7906571703179339671474015)
          ·
            refine ⟨11859857554769009507211023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7906571703179339671474015 11859857554769009507211023)
            ·
              refine ⟨17789786332153514260816535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11859857554769009507211023 17789786332153514260816535)
              ·
                refine ⟨26684679498230271391224803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17789786332153514260816535 26684679498230271391224803)
                ·
                  refine ⟨40027019247345407086837205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26684679498230271391224803 40027019247345407086837205)
                  ·
                    refine ⟨938133263609657978597747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40027019247345407086837205 938133263609657978597747)
                    ·
                      rfl

theorem cell22_2740512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_2740512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740512 prefixEnd_2740512 := by exact prefixLift 2740512
  have htrace : WordTrace (prefixWord ++ tailWord_2740512) baseStart_2740512 baseEnd_2740512 := by
    simpa [prefixWord, tailWord_2740512, baseEnd_2740512] using wordTrace_append hprefix tailTrace_2740512
  have hstable : (prefixWord ++ tailWord_2740512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740512).length < 2 ^ (prefixWord ++ tailWord_2740512).sum := by decide
  have hdescent : baseEnd_2740512 < baseStart_2740512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740514 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_2740514 : Nat := 118140960795 + 2740514 * 2 ^ 59
def prefixEnd_2740514 : Nat := 4983230072969 + 3 ^ 40 * 2740514 * 2
def baseEnd_2740514 : Nat := 312711316083510213349247

theorem tailTrace_2740514 : CollatzResearch.WordTrace tailWord_2740514 prefixEnd_2740514 312711316083510213349247 := by
  unfold tailWord_2740514
  simp only [CollatzResearch.WordTrace]
  refine ⟨24988689298398323843385149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66636504795728863582360397 24988689298398323843385149)
  ·
    refine ⟨9370758486899371441269431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24988689298398323843385149 9370758486899371441269431)
    ·
      refine ⟨14056137730349057161904147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9370758486899371441269431 14056137730349057161904147)
      ·
        refine ⟨21084206595523585742856221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14056137730349057161904147 21084206595523585742856221)
        ·
          refine ⟨7906577473321344653571083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21084206595523585742856221 7906577473321344653571083)
          ·
            refine ⟨11859866209982016980356625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7906577473321344653571083 11859866209982016980356625)
            ·
              refine ⟨8894899657486512735267469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11859866209982016980356625 8894899657486512735267469)
              ·
                refine ⟨3335587371557442275725301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8894899657486512735267469 3335587371557442275725301)
                ·
                  refine ⟨312711316083510213349247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3335587371557442275725301 312711316083510213349247)
                  ·
                    rfl

theorem cell22_2740514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_2740514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740514 prefixEnd_2740514 := by exact prefixLift 2740514
  have htrace : WordTrace (prefixWord ++ tailWord_2740514) baseStart_2740514 baseEnd_2740514 := by
    simpa [prefixWord, tailWord_2740514, baseEnd_2740514] using wordTrace_append hprefix tailTrace_2740514
  have hstable : (prefixWord ++ tailWord_2740514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740514).length < 2 ^ (prefixWord ++ tailWord_2740514).sum := by decide
  have hdescent : baseEnd_2740514 < baseStart_2740514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740527 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 3, 4]
def baseStart_2740527 : Nat := 118140960795 + 2740527 * 2 ^ 59
def prefixEnd_2740527 : Nat := 4983230072969 + 3 ^ 40 * 2740527 * 2
def baseEnd_2740527 : Nat := 938138398416202939472701

theorem tailTrace_2740527 : CollatzResearch.WordTrace tailWord_2740527 prefixEnd_2740527 938138398416202939472701 := by
  unfold tailWord_2740527
  simp only [CollatzResearch.WordTrace]
  refine ⟨99955231342546198593763835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66636820895030799062509223 99955231342546198593763835)
  ·
    refine ⟨149932847013819297890645753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99955231342546198593763835 149932847013819297890645753)
    ·
      refine ⟨112449635260364473417984315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149932847013819297890645753 112449635260364473417984315)
      ·
        refine ⟨168674452890546710126976473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112449635260364473417984315 168674452890546710126976473)
        ·
          refine ⟨126505839667910032595232355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168674452890546710126976473 126505839667910032595232355)
          ·
            refine ⟨189758759501865048892848533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126505839667910032595232355 189758759501865048892848533)
            ·
              refine ⟨8894941851649924166852275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 189758759501865048892848533 8894941851649924166852275)
              ·
                refine ⟨13342412777474886250278413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8894941851649924166852275 13342412777474886250278413)
                ·
                  refine ⟨5003404791553082343854405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13342412777474886250278413 5003404791553082343854405)
                  ·
                    refine ⟨938138398416202939472701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5003404791553082343854405 938138398416202939472701)
                    ·
                      rfl

theorem cell22_2740527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_2740527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740527 prefixEnd_2740527 := by exact prefixLift 2740527
  have htrace : WordTrace (prefixWord ++ tailWord_2740527) baseStart_2740527 baseEnd_2740527 := by
    simpa [prefixWord, tailWord_2740527, baseEnd_2740527] using wordTrace_append hprefix tailTrace_2740527
  have hstable : (prefixWord ++ tailWord_2740527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740527).length < 2 ^ (prefixWord ++ tailWord_2740527).sum := by decide
  have hdescent : baseEnd_2740527 < baseStart_2740527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740548 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 5]
def baseStart_2740548 : Nat := 118140960795 + 2740548 * 2 ^ 59
def prefixEnd_2740548 : Nat := 4983230072969 + 3 ^ 40 * 2740548 * 2
def baseEnd_2740548 : Nat := 312715195715121961565879

theorem tailTrace_2740548 : CollatzResearch.WordTrace tailWord_2740548 prefixEnd_2740548 312715195715121961565879 := by
  unfold tailWord_2740548
  simp only [CollatzResearch.WordTrace]
  refine ⟨49977998637735059590139149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66637331516980079453518865 49977998637735059590139149)
  ·
    refine ⟨18741749489150647346302181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49977998637735059590139149 18741749489150647346302181)
    ·
      refine ⟨3514078029215746377431659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18741749489150647346302181 3514078029215746377431659)
      ·
        refine ⟨5271117043823619566147489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514078029215746377431659 5271117043823619566147489)
        ·
          refine ⟨3953337782867714674610617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5271117043823619566147489 3953337782867714674610617)
          ·
            refine ⟨2965003337150786005957963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3953337782867714674610617 2965003337150786005957963)
            ·
              refine ⟨4447505005726179008936945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965003337150786005957963 4447505005726179008936945)
              ·
                refine ⟨3335628754294634256702709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4447505005726179008936945 3335628754294634256702709)
                ·
                  refine ⟨312715195715121961565879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3335628754294634256702709 312715195715121961565879)
                  ·
                    rfl

theorem cell22_2740548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_2740548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740548 prefixEnd_2740548 := by exact prefixLift 2740548
  have htrace : WordTrace (prefixWord ++ tailWord_2740548) baseStart_2740548 baseEnd_2740548 := by
    simpa [prefixWord, tailWord_2740548, baseEnd_2740548] using wordTrace_append hprefix tailTrace_2740548
  have hstable : (prefixWord ++ tailWord_2740548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740548).length < 2 ^ (prefixWord ++ tailWord_2740548).sum := by decide
  have hdescent : baseEnd_2740548 < baseStart_2740548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740589 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_2740589 : Nat := 118140960795 + 2740589 * 2 ^ 59
def prefixEnd_2740589 : Nat := 4983230072969 + 3 ^ 40 * 2740589 * 2
def baseEnd_2740589 : Nat := 938159622283255444422511

theorem tailTrace_2740589 : CollatzResearch.WordTrace tailWord_2740589 prefixEnd_2740589 938159622283255444422511 := by
  unfold tailWord_2740589
  simp only [CollatzResearch.WordTrace]
  refine ⟨99957492668321583182520821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66638328445547722121680547 99957492668321583182520821)
  ·
    refine ⟨9371014937655148423361327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99957492668321583182520821 9371014937655148423361327)
    ·
      refine ⟨14056522406482722635041991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9371014937655148423361327 14056522406482722635041991)
      ·
        refine ⟨21084783609724083952562987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14056522406482722635041991 21084783609724083952562987)
        ·
          refine ⟨31627175414586125928844481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21084783609724083952562987 31627175414586125928844481)
          ·
            refine ⟨23720381560939594446633361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31627175414586125928844481 23720381560939594446633361)
            ·
              refine ⟨17790286170704695834975021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23720381560939594446633361 17790286170704695834975021)
              ·
                refine ⟨6671357314014260938115633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17790286170704695834975021 6671357314014260938115633)
                ·
                  refine ⟨5003517985510695703586725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6671357314014260938115633 5003517985510695703586725)
                  ·
                    refine ⟨938159622283255444422511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5003517985510695703586725 938159622283255444422511)
                    ·
                      rfl

theorem cell22_2740589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_2740589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740589 prefixEnd_2740589 := by exact prefixLift 2740589
  have htrace : WordTrace (prefixWord ++ tailWord_2740589) baseStart_2740589 baseEnd_2740589 := by
    simpa [prefixWord, tailWord_2740589, baseEnd_2740589] using wordTrace_append hprefix tailTrace_2740589
  have hstable : (prefixWord ++ tailWord_2740589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740589).length < 2 ^ (prefixWord ++ tailWord_2740589).sum := by decide
  have hdescent : baseEnd_2740589 < baseStart_2740589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740610 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 6]
def baseStart_2740610 : Nat := 118140960795 + 2740610 * 2 ^ 59
def prefixEnd_2740610 : Nat := 4983230072969 + 3 ^ 40 * 2740610 * 2
def baseEnd_2740610 : Nat := 312722270337472796549149

theorem tailTrace_2740610 : CollatzResearch.WordTrace tailWord_2740610 prefixEnd_2740610 312722270337472796549149 := by
  unfold tailWord_2740610
  simp only [CollatzResearch.WordTrace]
  refine ⟨24989564650311375942258821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66638839067497002512690189 24989564650311375942258821)
  ·
    refine ⟨4685543371933382989173529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24989564650311375942258821 4685543371933382989173529)
    ·
      refine ⟨3514157528950037241880147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4685543371933382989173529 3514157528950037241880147)
      ·
        refine ⟨5271236293425055862820221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514157528950037241880147 5271236293425055862820221)
        ·
          refine ⟨1976713610034395948557583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5271236293425055862820221 1976713610034395948557583)
          ·
            refine ⟨2965070415051593922836375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976713610034395948557583 2965070415051593922836375)
            ·
              refine ⟨4447605622577390884254563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965070415051593922836375 4447605622577390884254563)
              ·
                refine ⟨6671408433866086326381845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4447605622577390884254563 6671408433866086326381845)
                ·
                  refine ⟨312722270337472796549149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6671408433866086326381845 312722270337472796549149)
                  ·
                    rfl

theorem cell22_2740610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_2740610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740610 prefixEnd_2740610 := by exact prefixLift 2740610
  have htrace : WordTrace (prefixWord ++ tailWord_2740610) baseStart_2740610 baseEnd_2740610 := by
    simpa [prefixWord, tailWord_2740610, baseEnd_2740610] using wordTrace_append hprefix tailTrace_2740610
  have hstable : (prefixWord ++ tailWord_2740610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740610).length < 2 ^ (prefixWord ++ tailWord_2740610).sum := by decide
  have hdescent : baseEnd_2740610 < baseStart_2740610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740670 : List Nat := [4, 2, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2740670 : Nat := 118140960795 + 2740670 * 2 ^ 59
def prefixEnd_2740670 : Nat := 4983230072969 + 3 ^ 40 * 2740670 * 2
def baseEnd_2740670 : Nat := 938187350238598233147263

theorem tailTrace_2740670 : CollatzResearch.WordTrace tailWord_2740670 prefixEnd_2740670 938187350238598233147263 := by
  unfold tailWord_2740670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12495055872628516752027433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66640297987352089344146309 12495055872628516752027433)
  ·
    refine ⟨9371291904471387564020575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12495055872628516752027433 9371291904471387564020575)
    ·
      refine ⟨14056937856707081346030863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9371291904471387564020575 14056937856707081346030863)
      ·
        refine ⟨21085406785060622019046295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14056937856707081346030863 21085406785060622019046295)
        ·
          refine ⟨31628110177590933028569443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21085406785060622019046295 31628110177590933028569443)
          ·
            refine ⟨47442165266386399542854165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31628110177590933028569443 47442165266386399542854165)
            ·
              refine ⟨2223851496861862478571289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47442165266386399542854165 2223851496861862478571289)
              ·
                refine ⟨1667888622646396858928467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2223851496861862478571289 1667888622646396858928467)
                ·
                  refine ⟨2501832933969595288392701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667888622646396858928467 2501832933969595288392701)
                  ·
                    refine ⟨938187350238598233147263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2501832933969595288392701 938187350238598233147263)
                    ·
                      rfl

theorem cell22_2740670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2740670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740670 prefixEnd_2740670 := by exact prefixLift 2740670
  have htrace : WordTrace (prefixWord ++ tailWord_2740670) baseStart_2740670 baseEnd_2740670 := by
    simpa [prefixWord, tailWord_2740670, baseEnd_2740670] using wordTrace_append hprefix tailTrace_2740670
  have hstable : (prefixWord ++ tailWord_2740670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740670).length < 2 ^ (prefixWord ++ tailWord_2740670).sum := by decide
  have hdescent : baseEnd_2740670 < baseStart_2740670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740677 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 12]
def baseStart_2740677 : Nat := 118140960795 + 2740677 * 2 ^ 59
def prefixEnd_2740677 : Nat := 4983230072969 + 3 ^ 40 * 2740677 * 2
def baseEnd_2740677 : Nat := 312729915493884182740747

theorem tailTrace_2740677 : CollatzResearch.WordTrace tailWord_2740677 prefixEnd_2740677 312729915493884182740747 := by
  unfold tailWord_2740677
  simp only [CollatzResearch.WordTrace]
  refine ⟨99960702292002774211724285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66640468194668516141149523 99960702292002774211724285)
  ·
    refine ⟨37485263359501040329396607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99960702292002774211724285 37485263359501040329396607)
    ·
      refine ⟨56227895039251560494094911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37485263359501040329396607 56227895039251560494094911)
      ·
        refine ⟨84341842558877340741142367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56227895039251560494094911 84341842558877340741142367)
        ·
          refine ⟨126512763838316011111713551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84341842558877340741142367 126512763838316011111713551)
          ·
            refine ⟨189769145757474016667570327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126512763838316011111713551 189769145757474016667570327)
            ·
              refine ⟨284653718636211025001355491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189769145757474016667570327 284653718636211025001355491)
              ·
                refine ⟨426980577954316537502033237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284653718636211025001355491 426980577954316537502033237)
                ·
                  refine ⟨312729915493884182740747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 426980577954316537502033237 312729915493884182740747)
                  ·
                    rfl

theorem cell22_2740677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_2740677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740677 prefixEnd_2740677 := by exact prefixLift 2740677
  have htrace : WordTrace (prefixWord ++ tailWord_2740677) baseStart_2740677 baseEnd_2740677 := by
    simpa [prefixWord, tailWord_2740677, baseEnd_2740677] using wordTrace_append hprefix tailTrace_2740677
  have hstable : (prefixWord ++ tailWord_2740677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740677).length < 2 ^ (prefixWord ++ tailWord_2740677).sum := by decide
  have hdescent : baseEnd_2740677 < baseStart_2740677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740679 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 3, 4]
def baseStart_2740679 : Nat := 118140960795 + 2740679 * 2 ^ 59
def prefixEnd_2740679 : Nat := 4983230072969 + 3 ^ 40 * 2740679 * 2
def baseEnd_2740679 : Nat := 938190431122525209672235

theorem tailTrace_2740679 : CollatzResearch.WordTrace tailWord_2740679 prefixEnd_2740679 938190431122525209672235 := by
  unfold tailWord_2740679
  simp only [CollatzResearch.WordTrace]
  refine ⟨99960775237995528553297091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66640516825330352368864727 99960775237995528553297091)
  ·
    refine ⟨149941162856993292829945637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99960775237995528553297091 149941162856993292829945637)
    ·
      refine ⟨28113968035686242405614807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149941162856993292829945637 28113968035686242405614807)
      ·
        refine ⟨42170952053529363608422211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28113968035686242405614807 42170952053529363608422211)
        ·
          refine ⟨63256428080294045412633317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42170952053529363608422211 63256428080294045412633317)
          ·
            refine ⟨11860580265055133514868747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63256428080294045412633317 11860580265055133514868747)
            ·
              refine ⟨17790870397582700272303121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11860580265055133514868747 17790870397582700272303121)
              ·
                refine ⟨13343152798187025204227341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17790870397582700272303121 13343152798187025204227341)
                ·
                  refine ⟨5003682299320134451585253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13343152798187025204227341 5003682299320134451585253)
                  ·
                    refine ⟨938190431122525209672235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5003682299320134451585253 938190431122525209672235)
                    ·
                      rfl

theorem cell22_2740679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_2740679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740679 prefixEnd_2740679 := by exact prefixLift 2740679
  have htrace : WordTrace (prefixWord ++ tailWord_2740679) baseStart_2740679 baseEnd_2740679 := by
    simpa [prefixWord, tailWord_2740679, baseEnd_2740679] using wordTrace_append hprefix tailTrace_2740679
  have hstable : (prefixWord ++ tailWord_2740679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740679).length < 2 ^ (prefixWord ++ tailWord_2740679).sum := by decide
  have hdescent : baseEnd_2740679 < baseStart_2740679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740743 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 1, 5]
def baseStart_2740743 : Nat := 118140960795 + 2740743 * 2 ^ 59
def prefixEnd_2740743 : Nat := 4983230072969 + 3 ^ 40 * 2740743 * 2
def baseEnd_2740743 : Nat := 938212339630450376072039

theorem tailTrace_2740743 : CollatzResearch.WordTrace tailWord_2740743 prefixEnd_2740743 938212339630450376072039 := by
  unfold tailWord_2740743
  simp only [CollatzResearch.WordTrace]
  refine ⟨99963109509763667483626883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66642073006509111655751255 99963109509763667483626883)
  ·
    refine ⟨149944664264645501225440325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99963109509763667483626883 149944664264645501225440325)
    ·
      refine ⟨28114624549621031479770061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149944664264645501225440325 28114624549621031479770061)
      ·
        refine ⟨10542984206107886804913773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28114624549621031479770061 10542984206107886804913773)
        ·
          refine ⟨3953619077290457551842665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10542984206107886804913773 3953619077290457551842665)
          ·
            refine ⟨2965214307967843163881999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3953619077290457551842665 2965214307967843163881999)
            ·
              refine ⟨4447821461951764745822999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965214307967843163881999 4447821461951764745822999)
              ·
                refine ⟨6671732192927647118734499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4447821461951764745822999 6671732192927647118734499)
                ·
                  refine ⟨10007598289391470678101749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6671732192927647118734499 10007598289391470678101749)
                  ·
                    refine ⟨938212339630450376072039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10007598289391470678101749 938212339630450376072039)
                    ·
                      rfl

theorem cell22_2740743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_2740743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740743 prefixEnd_2740743 := by exact prefixLift 2740743
  have htrace : WordTrace (prefixWord ++ tailWord_2740743) baseStart_2740743 baseEnd_2740743 := by
    simpa [prefixWord, tailWord_2740743, baseEnd_2740743] using wordTrace_append hprefix tailTrace_2740743
  have hstable : (prefixWord ++ tailWord_2740743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740743).length < 2 ^ (prefixWord ++ tailWord_2740743).sum := by decide
  have hdescent : baseEnd_2740743 < baseStart_2740743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740775 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2740775 : Nat := 118140960795 + 2740775 * 2 ^ 59
def prefixEnd_2740775 : Nat := 4983230072969 + 3 ^ 40 * 2740775 * 2
def baseEnd_2740775 : Nat := 938223293884412959271941

theorem tailTrace_2740775 : CollatzResearch.WordTrace tailWord_2740775 prefixEnd_2740775 938223293884412959271941 := by
  unfold tailWord_2740775
  simp only [CollatzResearch.WordTrace]
  refine ⟨99964276645647736948791779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66642851097098491299194519 99964276645647736948791779)
  ·
    refine ⟨149946414968471605423187669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99964276645647736948791779 149946414968471605423187669)
    ·
      refine ⟨3514369100823553252105961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 149946414968471605423187669 3514369100823553252105961)
      ·
        refine ⟨2635776825617664939079471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3514369100823553252105961 2635776825617664939079471)
        ·
          refine ⟨3953665238426497408619207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2635776825617664939079471 3953665238426497408619207)
          ·
            refine ⟨5930497857639746112928811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3953665238426497408619207 5930497857639746112928811)
            ·
              refine ⟨8895746786459619169393217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5930497857639746112928811 8895746786459619169393217)
              ·
                refine ⟨6671810089844714377044913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8895746786459619169393217 6671810089844714377044913)
                ·
                  refine ⟨5003857567383535782783685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6671810089844714377044913 5003857567383535782783685)
                  ·
                    refine ⟨938223293884412959271941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5003857567383535782783685 938223293884412959271941)
                    ·
                      rfl

theorem cell22_2740775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2740775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740775 prefixEnd_2740775 := by exact prefixLift 2740775
  have htrace : WordTrace (prefixWord ++ tailWord_2740775) baseStart_2740775 baseEnd_2740775 := by
    simpa [prefixWord, tailWord_2740775, baseEnd_2740775] using wordTrace_append hprefix tailTrace_2740775
  have hstable : (prefixWord ++ tailWord_2740775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740775).length < 2 ^ (prefixWord ++ tailWord_2740775).sum := by decide
  have hdescent : baseEnd_2740775 < baseStart_2740775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740784 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 7]
def baseStart_2740784 : Nat := 118140960795 + 2740784 * 2 ^ 59
def prefixEnd_2740784 : Nat := 4983230072969 + 3 ^ 40 * 2740784 * 2
def baseEnd_2740784 : Nat := 312742124922779978598971

theorem tailTrace_2740784 : CollatzResearch.WordTrace tailWord_2740784 prefixEnd_2740784 312742124922779978598971 := by
  unfold tailWord_2740784
  simp only [CollatzResearch.WordTrace]
  refine ⟨49982302451307565742934703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66643069935076754323912937 49982302451307565742934703)
  ·
    refine ⟨74973453676961348614402055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49982302451307565742934703 74973453676961348614402055)
    ·
      refine ⟨112460180515442022921603083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74973453676961348614402055 112460180515442022921603083)
      ·
        refine ⟨168690270773163034382404625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112460180515442022921603083 168690270773163034382404625)
        ·
          refine ⟨126517703079872275786803469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168690270773163034382404625 126517703079872275786803469)
          ·
            refine ⟨47444138654952103420051301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126517703079872275786803469 47444138654952103420051301)
            ·
              refine ⟨8895775997803519391259619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47444138654952103420051301 8895775997803519391259619)
              ·
                refine ⟨13343663996705279086889429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8895775997803519391259619 13343663996705279086889429)
                ·
                  refine ⟨312742124922779978598971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13343663996705279086889429 312742124922779978598971)
                  ·
                    rfl

theorem cell22_2740784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_2740784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740784 prefixEnd_2740784 := by exact prefixLift 2740784
  have htrace : WordTrace (prefixWord ++ tailWord_2740784) baseStart_2740784 baseEnd_2740784 := by
    simpa [prefixWord, tailWord_2740784, baseEnd_2740784] using wordTrace_append hprefix tailTrace_2740784
  have hstable : (prefixWord ++ tailWord_2740784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740784).length < 2 ^ (prefixWord ++ tailWord_2740784).sum := by decide
  have hdescent : baseEnd_2740784 < baseStart_2740784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740799 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 1, 7]
def baseStart_2740799 : Nat := 118140960795 + 2740799 * 2 ^ 59
def prefixEnd_2740799 : Nat := 4983230072969 + 3 ^ 40 * 2740799 * 2
def baseEnd_2740799 : Nat := 938231509574884896671867

theorem tailTrace_2740799 : CollatzResearch.WordTrace tailWord_2740799 prefixEnd_2740799 938231509574884896671867 := by
  unfold tailWord_2740799
  simp only [CollatzResearch.WordTrace]
  refine ⟨99965151997560789047665451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66643434665040526031776967 99965151997560789047665451)
  ·
    refine ⟨149947727996341183571498177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99965151997560789047665451 149947727996341183571498177)
    ·
      refine ⟨112460795997255887678623633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149947727996341183571498177 112460795997255887678623633)
      ·
        refine ⟨84345596997941915758967725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112460795997255887678623633 84345596997941915758967725)
        ·
          refine ⟨31629598874228218409612897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84345596997941915758967725 31629598874228218409612897)
          ·
            refine ⟨23722199155671163807209673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31629598874228218409612897 23722199155671163807209673)
            ·
              refine ⟨17791649366753372855407255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23722199155671163807209673 17791649366753372855407255)
              ·
                refine ⟨26687474050130059283110883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17791649366753372855407255 26687474050130059283110883)
                ·
                  refine ⟨40031211075195088924666325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26687474050130059283110883 40031211075195088924666325)
                  ·
                    refine ⟨938231509574884896671867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40031211075195088924666325 938231509574884896671867)
                    ·
                      rfl

theorem cell22_2740799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_2740799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740799 prefixEnd_2740799 := by exact prefixLift 2740799
  have htrace : WordTrace (prefixWord ++ tailWord_2740799) baseStart_2740799 baseEnd_2740799 := by
    simpa [prefixWord, tailWord_2740799, baseEnd_2740799] using wordTrace_append hprefix tailTrace_2740799
  have hstable : (prefixWord ++ tailWord_2740799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740799).length < 2 ^ (prefixWord ++ tailWord_2740799).sum := by decide
  have hdescent : baseEnd_2740799 < baseStart_2740799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740831 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 1, 4]
def baseStart_2740831 : Nat := 118140960795 + 2740831 * 2 ^ 59
def prefixEnd_2740831 : Nat := 4983230072969 + 3 ^ 40 * 2740831 * 2
def baseEnd_2740831 : Nat := 938242463828847479871769

theorem tailTrace_2740831 : CollatzResearch.WordTrace tailWord_2740831 prefixEnd_2740831 938242463828847479871769 := by
  unfold tailWord_2740831
  simp only [CollatzResearch.WordTrace]
  refine ⟨99966319133444858512830347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66644212755629905675220231 99966319133444858512830347)
  ·
    refine ⟨149949478700167287769245521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99966319133444858512830347 149949478700167287769245521)
    ·
      refine ⟨112462109025125465826934141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149949478700167287769245521 112462109025125465826934141)
      ·
        refine ⟨42173290884422049685100303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112462109025125465826934141 42173290884422049685100303)
        ·
          refine ⟨63259936326633074527650455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42173290884422049685100303 63259936326633074527650455)
          ·
            refine ⟨94889904489949611791475683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63259936326633074527650455 94889904489949611791475683)
            ·
              refine ⟨142334856734924417687213525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94889904489949611791475683 142334856734924417687213525)
              ·
                refine ⟨3335973204724791039544067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 142334856734924417687213525 3335973204724791039544067)
                ·
                  refine ⟨5003959807087186559316101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335973204724791039544067 5003959807087186559316101)
                  ·
                    refine ⟨938242463828847479871769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5003959807087186559316101 938242463828847479871769)
                    ·
                      rfl

theorem cell22_2740831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_2740831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740831 prefixEnd_2740831 := by exact prefixLift 2740831
  have htrace : WordTrace (prefixWord ++ tailWord_2740831) baseStart_2740831 baseEnd_2740831 := by
    simpa [prefixWord, tailWord_2740831, baseEnd_2740831] using wordTrace_append hprefix tailTrace_2740831
  have hstable : (prefixWord ++ tailWord_2740831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740831).length < 2 ^ (prefixWord ++ tailWord_2740831).sum := by decide
  have hdescent : baseEnd_2740831 < baseStart_2740831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740876 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_2740876 : Nat := 118140960795 + 2740876 * 2 ^ 59
def prefixEnd_2740876 : Nat := 4983230072969 + 3 ^ 40 * 2740876 * 2
def baseEnd_2740876 : Nat := 938257868248482362496631

theorem tailTrace_2740876 : CollatzResearch.WordTrace tailWord_2740876 prefixEnd_2740876 938257868248482362496631 := by
  unfold tailWord_2740876
  simp only [CollatzResearch.WordTrace]
  refine ⟨49983980209140915599109241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66645306945521220798812321 49983980209140915599109241)
  ·
    refine ⟨37487985156855686699331931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49983980209140915599109241 37487985156855686699331931)
    ·
      refine ⟨56231977735283530048997897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37487985156855686699331931 56231977735283530048997897)
      ·
        refine ⟨42173983301462647536748423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56231977735283530048997897 42173983301462647536748423)
        ·
          refine ⟨63260974952193971305122635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42173983301462647536748423 63260974952193971305122635)
          ·
            refine ⟨94891462428290956957683953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63260974952193971305122635 94891462428290956957683953)
            ·
              refine ⟨71168596821218217718262965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94891462428290956957683953 71168596821218217718262965)
              ·
                refine ⟨6672055951989207911087153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71168596821218217718262965 6672055951989207911087153)
                ·
                  refine ⟨5004041963991905933315365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6672055951989207911087153 5004041963991905933315365)
                  ·
                    refine ⟨938257868248482362496631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5004041963991905933315365 938257868248482362496631)
                    ·
                      rfl

theorem cell22_2740876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_2740876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740876 prefixEnd_2740876 := by exact prefixLift 2740876
  have htrace : WordTrace (prefixWord ++ tailWord_2740876) baseStart_2740876 baseEnd_2740876 := by
    simpa [prefixWord, tailWord_2740876, baseEnd_2740876] using wordTrace_append hprefix tailTrace_2740876
  have hstable : (prefixWord ++ tailWord_2740876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740876).length < 2 ^ (prefixWord ++ tailWord_2740876).sum := by decide
  have hdescent : baseEnd_2740876 < baseStart_2740876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740878 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_2740878 : Nat := 118140960795 + 2740878 * 2 ^ 59
def prefixEnd_2740878 : Nat := 4983230072969 + 3 ^ 40 * 2740878 * 2
def baseEnd_2740878 : Nat := 938258552889355023946625

theorem tailTrace_2740878 : CollatzResearch.WordTrace tailWord_2740878 prefixEnd_2740878 938258552889355023946625 := by
  unfold tailWord_2740878
  simp only [CollatzResearch.WordTrace]
  refine ⟨12496004170534323192473911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66645355576183057026527525 12496004170534323192473911)
  ·
    refine ⟨18744006255801484788710867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12496004170534323192473911 18744006255801484788710867)
    ·
      refine ⟨28116009383702227183066301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18744006255801484788710867 28116009383702227183066301)
      ·
        refine ⟨10543503518888335193649863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28116009383702227183066301 10543503518888335193649863)
        ·
          refine ⟨15815255278332502790474795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10543503518888335193649863 15815255278332502790474795)
          ·
            refine ⟨23722882917498754185712193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15815255278332502790474795 23722882917498754185712193)
            ·
              refine ⟨17792162188124065639284145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23722882917498754185712193 17792162188124065639284145)
              ·
                refine ⟨13344121641093049229463109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17792162188124065639284145 13344121641093049229463109)
                ·
                  refine ⟨2502022807704946730524333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13344121641093049229463109 2502022807704946730524333)
                  ·
                    refine ⟨938258552889355023946625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2502022807704946730524333 938258552889355023946625)
                    ·
                      rfl

theorem cell22_2740878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_2740878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740878 prefixEnd_2740878 := by exact prefixLift 2740878
  have htrace : WordTrace (prefixWord ++ tailWord_2740878) baseStart_2740878 baseEnd_2740878 := by
    simpa [prefixWord, tailWord_2740878, baseEnd_2740878] using wordTrace_append hprefix tailTrace_2740878
  have hstable : (prefixWord ++ tailWord_2740878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740878).length < 2 ^ (prefixWord ++ tailWord_2740878).sum := by decide
  have hdescent : baseEnd_2740878 < baseStart_2740878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740882 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_2740882 : Nat := 118140960795 + 2740882 * 2 ^ 59
def prefixEnd_2740882 : Nat := 4983230072969 + 3 ^ 40 * 2740882 * 2
def baseEnd_2740882 : Nat := 938259922171100346846613

theorem tailTrace_2740882 : CollatzResearch.WordTrace tailWord_2740882 prefixEnd_2740882 938259922171100346846613 := by
  unfold tailWord_2740882
  simp only [CollatzResearch.WordTrace]
  refine ⟨24992044814065023555734225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66645452837506729481957933 24992044814065023555734225)
  ·
    refine ⟨18744033610548767666800669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24992044814065023555734225 18744033610548767666800669)
    ·
      refine ⟨7029012603955787875050251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18744033610548767666800669 7029012603955787875050251)
      ·
        refine ⟨10543518905933681812575377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7029012603955787875050251 10543518905933681812575377)
        ·
          refine ⟨7907639179450261359431533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10543518905933681812575377 7907639179450261359431533)
          ·
            refine ⟨2965364692293848009786825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7907639179450261359431533 2965364692293848009786825)
            ·
              refine ⟨2224023519220386007340119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2965364692293848009786825 2224023519220386007340119)
              ·
                refine ⟨3336035278830579011010179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224023519220386007340119 3336035278830579011010179)
                ·
                  refine ⟨5004052918245868516515269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336035278830579011010179 5004052918245868516515269)
                  ·
                    refine ⟨938259922171100346846613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5004052918245868516515269 938259922171100346846613)
                    ·
                      rfl

theorem cell22_2740882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_2740882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740882 prefixEnd_2740882 := by exact prefixLift 2740882
  have htrace : WordTrace (prefixWord ++ tailWord_2740882) baseStart_2740882 baseEnd_2740882 := by
    simpa [prefixWord, tailWord_2740882, baseEnd_2740882] using wordTrace_append hprefix tailTrace_2740882
  have hstable : (prefixWord ++ tailWord_2740882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740882).length < 2 ^ (prefixWord ++ tailWord_2740882).sum := by decide
  have hdescent : baseEnd_2740882 < baseStart_2740882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2740936 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 7]
def baseStart_2740936 : Nat := 118140960795 + 2740936 * 2 ^ 59
def prefixEnd_2740936 : Nat := 4983230072969 + 3 ^ 40 * 2740936 * 2
def baseEnd_2740936 : Nat := 312759469158220735332149

theorem tailTrace_2740936 : CollatzResearch.WordTrace tailWord_2740936 prefixEnd_2740936 312759469158220735332149 := by
  unfold tailWord_2740936
  simp only [CollatzResearch.WordTrace]
  refine ⟨49985074399032230722701331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66646765865376307630268441 49985074399032230722701331)
  ·
    refine ⟨74977611598548346084051997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49985074399032230722701331 74977611598548346084051997)
    ·
      refine ⟨28116604349455629781519499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74977611598548346084051997 28116604349455629781519499)
      ·
        refine ⟨42174906524183444672279249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28116604349455629781519499 42174906524183444672279249)
        ·
          refine ⟨31631179893137583504209437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42174906524183444672279249 31631179893137583504209437)
          ·
            refine ⟨11861692459926593814078539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31631179893137583504209437 11861692459926593814078539)
            ·
              refine ⟨17792538689889890721117809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11861692459926593814078539 17792538689889890721117809)
              ·
                refine ⟨13344404017417418040838357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17792538689889890721117809 13344404017417418040838357)
                ·
                  refine ⟨312759469158220735332149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13344404017417418040838357 312759469158220735332149)
                  ·
                    rfl

theorem cell22_2740936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_2740936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2740936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2740936 prefixEnd_2740936 := by exact prefixLift 2740936
  have htrace : WordTrace (prefixWord ++ tailWord_2740936) baseStart_2740936 baseEnd_2740936 := by
    simpa [prefixWord, tailWord_2740936, baseEnd_2740936] using wordTrace_append hprefix tailTrace_2740936
  have hstable : (prefixWord ++ tailWord_2740936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2740936).length < 2 ^ (prefixWord ++ tailWord_2740936).sum := by decide
  have hdescent : baseEnd_2740936 < baseStart_2740936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2740936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741045 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2741045 : Nat := 118140960795 + 2741045 * 2 ^ 59
def prefixEnd_2741045 : Nat := 4983230072969 + 3 ^ 40 * 2741045 * 2
def baseEnd_2741045 : Nat := 938315720402222255021113

theorem tailTrace_2741045 : CollatzResearch.WordTrace tailWord_2741045 prefixEnd_2741045 938315720402222255021113 := by
  unfold tailWord_2741045
  simp only [CollatzResearch.WordTrace]
  refine ⟨99974124354669573061120589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66649416236446382040747059 99974124354669573061120589)
  ·
    refine ⟨37490296633001089897920221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99974124354669573061120589 37490296633001089897920221)
    ·
      refine ⟨14058861237375408711720083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37490296633001089897920221 14058861237375408711720083)
      ·
        refine ⟨21088291856063113067580125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14058861237375408711720083 21088291856063113067580125)
        ·
          refine ⟨7908109446023667400342547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21088291856063113067580125 7908109446023667400342547)
          ·
            refine ⟨11862164169035501100513821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7908109446023667400342547 11862164169035501100513821)
            ·
              refine ⟨4448311563388312912692683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11862164169035501100513821 4448311563388312912692683)
              ·
                refine ⟨6672467345082469369039025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4448311563388312912692683 6672467345082469369039025)
                ·
                  refine ⟨5004350508811852026779269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6672467345082469369039025 5004350508811852026779269)
                  ·
                    refine ⟨938315720402222255021113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5004350508811852026779269 938315720402222255021113)
                    ·
                      rfl

theorem cell22_2741045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2741045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741045 prefixEnd_2741045 := by exact prefixLift 2741045
  have htrace : WordTrace (prefixWord ++ tailWord_2741045) baseStart_2741045 baseEnd_2741045 := by
    simpa [prefixWord, tailWord_2741045, baseEnd_2741045] using wordTrace_append hprefix tailTrace_2741045
  have hstable : (prefixWord ++ tailWord_2741045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741045).length < 2 ^ (prefixWord ++ tailWord_2741045).sum := by decide
  have hdescent : baseEnd_2741045 < baseStart_2741045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741109 : List Nat := [1, 3, 4, 1, 1, 2, 3, 3, 1, 3]
def baseStart_2741109 : Nat := 118140960795 + 2741109 * 2 ^ 59
def prefixEnd_2741109 : Nat := 4983230072969 + 3 ^ 40 * 2741109 * 2
def baseEnd_2741109 : Nat := 938337628910147421420917

theorem tailTrace_2741109 : CollatzResearch.WordTrace tailWord_2741109 prefixEnd_2741109 938337628910147421420917 := by
  unfold tailWord_2741109
  simp only [CollatzResearch.WordTrace]
  refine ⟨99976458626437711991450381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66650972417625141327633587 99976458626437711991450381)
  ·
    refine ⟨37491171984914141996793893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99976458626437711991450381 37491171984914141996793893)
    ·
      refine ⟨7029594747171401624398855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37491171984914141996793893 7029594747171401624398855)
      ·
        refine ⟨10544392120757102436598283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7029594747171401624398855 10544392120757102436598283)
        ·
          refine ⟨15816588181135653654897425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10544392120757102436598283 15816588181135653654897425)
          ·
            refine ⟨11862441135851740241173069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15816588181135653654897425 11862441135851740241173069)
            ·
              refine ⟨4448415425944402590439901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11862441135851740241173069 4448415425944402590439901)
              ·
                refine ⟨1668155784729150971414963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4448415425944402590439901 1668155784729150971414963)
                ·
                  refine ⟨2502233677093726457122445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668155784729150971414963 2502233677093726457122445)
                  ·
                    refine ⟨938337628910147421420917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2502233677093726457122445 938337628910147421420917)
                    ·
                      rfl

theorem cell22_2741109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_2741109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741109 prefixEnd_2741109 := by exact prefixLift 2741109
  have htrace : WordTrace (prefixWord ++ tailWord_2741109) baseStart_2741109 baseEnd_2741109 := by
    simpa [prefixWord, tailWord_2741109, baseEnd_2741109] using wordTrace_append hprefix tailTrace_2741109
  have hstable : (prefixWord ++ tailWord_2741109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741109).length < 2 ^ (prefixWord ++ tailWord_2741109).sum := by decide
  have hdescent : baseEnd_2741109 < baseStart_2741109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741163 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 6, 4]
def baseStart_2741163 : Nat := 118140960795 + 2741163 * 2 ^ 59
def prefixEnd_2741163 : Nat := 4983230072969 + 3 ^ 40 * 2741163 * 2
def baseEnd_2741163 : Nat := 938356114213709280570751

theorem tailTrace_2741163 : CollatzResearch.WordTrace tailWord_2741163 prefixEnd_2741163 938356114213709280570751 := by
  unfold tailWord_2741163
  simp only [CollatzResearch.WordTrace]
  refine ⟨99978428168242079213916143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66652285445494719475944095 99978428168242079213916143)
  ·
    refine ⟨149967642252363118820874215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99978428168242079213916143 149967642252363118820874215)
    ·
      refine ⟨224951463378544678231311323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149967642252363118820874215 224951463378544678231311323)
      ·
        refine ⟨337427195067817017346966985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224951463378544678231311323 337427195067817017346966985)
        ·
          refine ⟨253070396300862763010225239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337427195067817017346966985 253070396300862763010225239)
          ·
            refine ⟨379605594451294144515337859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253070396300862763010225239 379605594451294144515337859)
            ·
              refine ⟨569408391676941216773006789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379605594451294144515337859 569408391676941216773006789)
              ·
                refine ⟨106764073439426478144938773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 569408391676941216773006789 106764073439426478144938773)
                ·
                  refine ⟨5004565942473116163044005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106764073439426478144938773 5004565942473116163044005)
                  ·
                    refine ⟨938356114213709280570751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5004565942473116163044005 938356114213709280570751)
                    ·
                      rfl

theorem cell22_2741163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 4].length) (baseStart_2741163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741163 prefixEnd_2741163 := by exact prefixLift 2741163
  have htrace : WordTrace (prefixWord ++ tailWord_2741163) baseStart_2741163 baseEnd_2741163 := by
    simpa [prefixWord, tailWord_2741163, baseEnd_2741163] using wordTrace_append hprefix tailTrace_2741163
  have hstable : (prefixWord ++ tailWord_2741163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741163).length < 2 ^ (prefixWord ++ tailWord_2741163).sum := by decide
  have hdescent : baseEnd_2741163 < baseStart_2741163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741169 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 1, 4]
def baseStart_2741169 : Nat := 118140960795 + 2741169 * 2 ^ 59
def prefixEnd_2741169 : Nat := 4983230072969 + 3 ^ 40 * 2741169 * 2
def baseEnd_2741169 : Nat := 938358168136327264920733

theorem tailTrace_2741169 : CollatzResearch.WordTrace tailWord_2741169 prefixEnd_2741169 938358168136327264920733 := by
  unfold tailWord_2741169
  simp only [CollatzResearch.WordTrace]
  refine ⟨99978647006220342238634561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66652431337480228159089707 99978647006220342238634561)
  ·
    refine ⟨74983985254665256678975921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99978647006220342238634561 74983985254665256678975921)
    ·
      refine ⟨56237988940998942509231941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74983985254665256678975921 56237988940998942509231941)
      ·
        refine ⟨10544622926437301720480989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56237988940998942509231941 10544622926437301720480989)
        ·
          refine ⟨3954233597413988145180371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10544622926437301720480989 3954233597413988145180371)
          ·
            refine ⟨5931350396120982217770557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954233597413988145180371 5931350396120982217770557)
            ·
              refine ⟨2224256398545368331663959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5931350396120982217770557 2224256398545368331663959)
              ·
                refine ⟨3336384597818052497495939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224256398545368331663959 3336384597818052497495939)
                ·
                  refine ⟨5004576896727078746243909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336384597818052497495939 5004576896727078746243909)
                  ·
                    refine ⟨938358168136327264920733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5004576896727078746243909 938358168136327264920733)
                    ·
                      rfl

theorem cell22_2741169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_2741169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741169 prefixEnd_2741169 := by exact prefixLift 2741169
  have htrace : WordTrace (prefixWord ++ tailWord_2741169) baseStart_2741169 baseEnd_2741169 := by
    simpa [prefixWord, tailWord_2741169, baseEnd_2741169] using wordTrace_append hprefix tailTrace_2741169
  have hstable : (prefixWord ++ tailWord_2741169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741169).length < 2 ^ (prefixWord ++ tailWord_2741169).sum := by decide
  have hdescent : baseEnd_2741169 < baseStart_2741169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741184 : List Nat := [2, 1, 1, 2, 3, 5, 2, 2, 4]
def baseStart_2741184 : Nat := 118140960795 + 2741184 * 2 ^ 59
def prefixEnd_2741184 : Nat := 4983230072969 + 3 ^ 40 * 2741184 * 2
def baseEnd_2741184 : Nat := 312787767647624075265229

theorem tailTrace_2741184 : CollatzResearch.WordTrace tailWord_2741184 prefixEnd_2741184 312787767647624075265229 := by
  unfold tailWord_2741184
  simp only [CollatzResearch.WordTrace]
  refine ⟨49989597050582999900215303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66652796067443999866953737 49989597050582999900215303)
  ·
    refine ⟨74984395575874499850322955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49989597050582999900215303 74984395575874499850322955)
    ·
      refine ⟨112476593363811749775484433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74984395575874499850322955 112476593363811749775484433)
      ·
        refine ⟨84357445022858812331613325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112476593363811749775484433 84357445022858812331613325)
        ·
          refine ⟨31634041883572054624354997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84357445022858812331613325 31634041883572054624354997)
          ·
            refine ⟨2965691426584880121033281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31634041883572054624354997 2965691426584880121033281)
            ·
              refine ⟨2224268569938660090774961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2965691426584880121033281 2224268569938660090774961)
              ·
                refine ⟨1668201427453995068081221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224268569938660090774961 1668201427453995068081221)
                ·
                  refine ⟨312787767647624075265229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1668201427453995068081221 312787767647624075265229)
                  ·
                    rfl

theorem cell22_2741184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 4].length) (baseStart_2741184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741184 prefixEnd_2741184 := by exact prefixLift 2741184
  have htrace : WordTrace (prefixWord ++ tailWord_2741184) baseStart_2741184 baseEnd_2741184 := by
    simpa [prefixWord, tailWord_2741184, baseEnd_2741184] using wordTrace_append hprefix tailTrace_2741184
  have hstable : (prefixWord ++ tailWord_2741184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741184).length < 2 ^ (prefixWord ++ tailWord_2741184).sum := by decide
  have hdescent : baseEnd_2741184 < baseStart_2741184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741195 : List Nat := [1, 1, 1, 1, 3, 7, 1, 7]
def baseStart_2741195 : Nat := 118140960795 + 2741195 * 2 ^ 59
def prefixEnd_2741195 : Nat := 4983230072969 + 3 ^ 40 * 2741195 * 2
def baseEnd_2741195 : Nat := 104263007607519095974517

theorem tailTrace_2741195 : CollatzResearch.WordTrace tailWord_2741195 prefixEnd_2741195 104263007607519095974517 := by
  unfold tailWord_2741195
  simp only [CollatzResearch.WordTrace]
  refine ⟨99979595304126148679081039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66653063536084099119387359 99979595304126148679081039)
  ·
    refine ⟨149969392956189223018621559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99979595304126148679081039 149969392956189223018621559)
    ·
      refine ⟨224954089434283834527932339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149969392956189223018621559 224954089434283834527932339)
      ·
        refine ⟨337431134151425751791898509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224954089434283834527932339 337431134151425751791898509)
        ·
          refine ⟨126536675306784656921961941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337431134151425751791898509 126536675306784656921961941)
          ·
            refine ⟨2965703327502765396608483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 126536675306784656921961941 2965703327502765396608483)
            ·
              refine ⟨4448554991254148094912725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965703327502765396608483 4448554991254148094912725)
              ·
                refine ⟨104263007607519095974517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4448554991254148094912725 104263007607519095974517)
                ·
                  rfl

theorem cell22_2741195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 7].length) (baseStart_2741195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741195 prefixEnd_2741195 := by exact prefixLift 2741195
  have htrace : WordTrace (prefixWord ++ tailWord_2741195) baseStart_2741195 baseEnd_2741195 := by
    simpa [prefixWord, tailWord_2741195, baseEnd_2741195] using wordTrace_append hprefix tailTrace_2741195
  have hstable : (prefixWord ++ tailWord_2741195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741195).length < 2 ^ (prefixWord ++ tailWord_2741195).sum := by decide
  have hdescent : baseEnd_2741195 < baseStart_2741195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741244 : List Nat := [2, 2, 2, 1, 2, 3, 2, 4, 1, 3]
def baseStart_2741244 : Nat := 118140960795 + 2741244 * 2 ^ 59
def prefixEnd_2741244 : Nat := 4983230072969 + 3 ^ 40 * 2741244 * 2
def baseEnd_2741244 : Nat := 938383842169052069295503

theorem tailTrace_2741244 : CollatzResearch.WordTrace tailWord_2741244 prefixEnd_2741244 938383842169052069295503 := by
  unfold tailWord_2741244
  simp only [CollatzResearch.WordTrace]
  refine ⟨49990691240474315023807393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66654254987299086698409857 49990691240474315023807393)
  ·
    refine ⟨37493018430355736267855545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49990691240474315023807393 37493018430355736267855545)
    ·
      refine ⟨28119763822766802200891659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37493018430355736267855545 28119763822766802200891659)
      ·
        refine ⟨42179645734150203301337489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28119763822766802200891659 42179645734150203301337489)
        ·
          refine ⟨31634734300612652476003117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42179645734150203301337489 31634734300612652476003117)
          ·
            refine ⟨11863025362729744678501169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31634734300612652476003117 11863025362729744678501169)
            ·
              refine ⟨8897269022047308508875877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11863025362729744678501169 8897269022047308508875877)
              ·
                refine ⟨1668237941633870345414227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8897269022047308508875877 1668237941633870345414227)
                ·
                  refine ⟨2502356912450805518121341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668237941633870345414227 2502356912450805518121341)
                  ·
                    refine ⟨938383842169052069295503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2502356912450805518121341 938383842169052069295503)
                    ·
                      rfl

theorem cell22_2741244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_2741244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741244 prefixEnd_2741244 := by exact prefixLift 2741244
  have htrace : WordTrace (prefixWord ++ tailWord_2741244) baseStart_2741244 baseEnd_2741244 := by
    simpa [prefixWord, tailWord_2741244, baseEnd_2741244] using wordTrace_append hprefix tailTrace_2741244
  have hstable : (prefixWord ++ tailWord_2741244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741244).length < 2 ^ (prefixWord ++ tailWord_2741244).sum := by decide
  have hdescent : baseEnd_2741244 < baseStart_2741244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741255 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 2, 5]
def baseStart_2741255 : Nat := 118140960795 + 2741255 * 2 ^ 59
def prefixEnd_2741255 : Nat := 4983230072969 + 3 ^ 40 * 2741255 * 2
def baseEnd_2741255 : Nat := 938387607693851707270469

theorem tailTrace_2741255 : CollatzResearch.WordTrace tailWord_2741255 prefixEnd_2741255 938387607693851707270469 := by
  unfold tailWord_2741255
  simp only [CollatzResearch.WordTrace]
  refine ⟨99981783683908778926265219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66654522455939185950843479 99981783683908778926265219)
  ·
    refine ⟨149972675525863168389397829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99981783683908778926265219 149972675525863168389397829)
    ·
      refine ⟨28119876661099344073012093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149972675525863168389397829 28119876661099344073012093)
      ·
        refine ⟨10544953747912254027379535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28119876661099344073012093 10544953747912254027379535)
        ·
          refine ⟨15817430621868381041069303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10544953747912254027379535 15817430621868381041069303)
          ·
            refine ⟨23726145932802571561603955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15817430621868381041069303 23726145932802571561603955)
            ·
              refine ⟨35589218899203857342405933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23726145932802571561603955 35589218899203857342405933)
              ·
                refine ⟨13345957087201446503402225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35589218899203857342405933 13345957087201446503402225)
                ·
                  refine ⟨10009467815401084877551669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13345957087201446503402225 10009467815401084877551669)
                  ·
                    refine ⟨938387607693851707270469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10009467815401084877551669 938387607693851707270469)
                    ·
                      rfl

theorem cell22_2741255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_2741255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741255 prefixEnd_2741255 := by exact prefixLift 2741255
  have htrace : WordTrace (prefixWord ++ tailWord_2741255) baseStart_2741255 baseEnd_2741255 := by
    simpa [prefixWord, tailWord_2741255, baseEnd_2741255] using wordTrace_append hprefix tailTrace_2741255
  have hstable : (prefixWord ++ tailWord_2741255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741255).length < 2 ^ (prefixWord ++ tailWord_2741255).sum := by decide
  have hdescent : baseEnd_2741255 < baseStart_2741255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741315 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 4, 4]
def baseStart_2741315 : Nat := 118140960795 + 2741315 * 2 ^ 59
def prefixEnd_2741315 : Nat := 4983230072969 + 3 ^ 40 * 2741315 * 2
def baseEnd_2741315 : Nat := 938408146920031550770285

theorem tailTrace_2741315 : CollatzResearch.WordTrace tailWord_2741315 prefixEnd_2741315 938408146920031550770285 := by
  unfold tailWord_2741315
  simp only [CollatzResearch.WordTrace]
  refine ⟨99983972063691409173449399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66655981375794272782299599 99983972063691409173449399)
  ·
    refine ⟨149975958095537113760174099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99983972063691409173449399 149975958095537113760174099)
    ·
      refine ⟨224963937143305670640261149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149975958095537113760174099 224963937143305670640261149)
      ·
        refine ⟨84361476428739626490097931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224963937143305670640261149 84361476428739626490097931)
        ·
          refine ⟨126542214643109439735146897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84361476428739626490097931 126542214643109439735146897)
          ·
            refine ⟨94906660982332079801360173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126542214643109439735146897 94906660982332079801360173)
            ·
              refine ⟨35589997868374529925510065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94906660982332079801360173 35589997868374529925510065)
              ·
                refine ⟨26692498401280897444132549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35589997868374529925510065 26692498401280897444132549)
                ·
                  refine ⟨5004843450240168270774853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26692498401280897444132549 5004843450240168270774853)
                  ·
                    refine ⟨938408146920031550770285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5004843450240168270774853 938408146920031550770285)
                    ·
                      rfl

theorem cell22_2741315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 4].length) (baseStart_2741315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741315 prefixEnd_2741315 := by exact prefixLift 2741315
  have htrace : WordTrace (prefixWord ++ tailWord_2741315) baseStart_2741315 baseEnd_2741315 := by
    simpa [prefixWord, tailWord_2741315, baseEnd_2741315] using wordTrace_append hprefix tailTrace_2741315
  have hstable : (prefixWord ++ tailWord_2741315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741315).length < 2 ^ (prefixWord ++ tailWord_2741315).sum := by decide
  have hdescent : baseEnd_2741315 < baseStart_2741315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741332 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_2741332 : Nat := 118140960795 + 2741332 * 2 ^ 59
def prefixEnd_2741332 : Nat := 4983230072969 + 3 ^ 40 * 2741332 * 2
def baseEnd_2741332 : Nat := 938413966367449173095233

theorem tailTrace_2741332 : CollatzResearch.WordTrace tailWord_2741332 prefixEnd_2741332 938413966367449173095233 := by
  unfold tailWord_2741332
  simp only [CollatzResearch.WordTrace]
  refine ⟨49992296052314910538409125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66656394736419880717878833 49992296052314910538409125)
  ·
    refine ⟨9373555509809045725951711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49992296052314910538409125 9373555509809045725951711)
    ·
      refine ⟨14060333264713568588927567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9373555509809045725951711 14060333264713568588927567)
      ·
        refine ⟨21090499897070352883391351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14060333264713568588927567 21090499897070352883391351)
        ·
          refine ⟨31635749845605529325087027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21090499897070352883391351 31635749845605529325087027)
          ·
            refine ⟨47453624768408293987630541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31635749845605529325087027 47453624768408293987630541)
            ·
              refine ⟨17795109288153110245361453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47453624768408293987630541 17795109288153110245361453)
              ·
                refine ⟨6673165983057416342010545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17795109288153110245361453 6673165983057416342010545)
                ·
                  refine ⟨5004874487293062256507909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6673165983057416342010545 5004874487293062256507909)
                  ·
                    refine ⟨938413966367449173095233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5004874487293062256507909 938413966367449173095233)
                    ·
                      rfl

theorem cell22_2741332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_2741332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741332 prefixEnd_2741332 := by exact prefixLift 2741332
  have htrace : WordTrace (prefixWord ++ tailWord_2741332) baseStart_2741332 baseEnd_2741332 := by
    simpa [prefixWord, tailWord_2741332, baseEnd_2741332] using wordTrace_append hprefix tailTrace_2741332
  have hstable : (prefixWord ++ tailWord_2741332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741332).length < 2 ^ (prefixWord ++ tailWord_2741332).sum := by decide
  have hdescent : baseEnd_2741332 < baseStart_2741332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741360 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_2741360 : Nat := 118140960795 + 2741360 * 2 ^ 59
def prefixEnd_2741360 : Nat := 4983230072969 + 3 ^ 40 * 2741360 * 2
def baseEnd_2741360 : Nat := 938423551339666433395147

theorem tailTrace_2741360 : CollatzResearch.WordTrace tailWord_2741360 prefixEnd_2741360 938423551339666433395147 := by
  unfold tailWord_2741360
  simp only [CollatzResearch.WordTrace]
  refine ⟨49992806674264190929418767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66657075565685587905891689 49992806674264190929418767)
  ·
    refine ⟨74989210011396286394128151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49992806674264190929418767 74989210011396286394128151)
    ·
      refine ⟨112483815017094429591192227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74989210011396286394128151 112483815017094429591192227)
      ·
        refine ⟨168725722525641644386788341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112483815017094429591192227 168725722525641644386788341)
        ·
          refine ⟨15818036486778904161261407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168725722525641644386788341 15818036486778904161261407)
          ·
            refine ⟨23727054730168356241892111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15818036486778904161261407 23727054730168356241892111)
            ·
              refine ⟨35590582095252534362838167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23727054730168356241892111 35590582095252534362838167)
              ·
                refine ⟨53385873142878801544257251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35590582095252534362838167 53385873142878801544257251)
                ·
                  refine ⟨80078809714318202316385877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53385873142878801544257251 80078809714318202316385877)
                  ·
                    refine ⟨938423551339666433395147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80078809714318202316385877 938423551339666433395147)
                    ·
                      rfl

theorem cell22_2741360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_2741360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741360 prefixEnd_2741360 := by exact prefixLift 2741360
  have htrace : WordTrace (prefixWord ++ tailWord_2741360) baseStart_2741360 baseEnd_2741360 := by
    simpa [prefixWord, tailWord_2741360, baseEnd_2741360] using wordTrace_append hprefix tailTrace_2741360
  have hstable : (prefixWord ++ tailWord_2741360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741360).length < 2 ^ (prefixWord ++ tailWord_2741360).sum := by decide
  have hdescent : baseEnd_2741360 < baseStart_2741360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741437 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 6]
def baseStart_2741437 : Nat := 118140960795 + 2741437 * 2 ^ 59
def prefixEnd_2741437 : Nat := 4983230072969 + 3 ^ 40 * 2741437 * 2
def baseEnd_2741437 : Nat := 312816636671087966406637

theorem tailTrace_2741437 : CollatzResearch.WordTrace tailWord_2741437 prefixEnd_2741437 312816636671087966406637 := by
  unfold tailWord_2741437
  simp only [CollatzResearch.WordTrace]
  refine ⟨99988421769249424009390565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66658947846166282672927043 99988421769249424009390565)
  ·
    refine ⟨18747829081734267001760731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99988421769249424009390565 18747829081734267001760731)
    ·
      refine ⟨28121743622601400502641097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18747829081734267001760731 28121743622601400502641097)
      ·
        refine ⟨21091307716951050376980823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28121743622601400502641097 21091307716951050376980823)
        ·
          refine ⟨31636961575426575565471235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21091307716951050376980823 31636961575426575565471235)
          ·
            refine ⟨47455442363139863348206853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31636961575426575565471235 47455442363139863348206853)
            ·
              refine ⟨8897895443088724377788785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47455442363139863348206853 8897895443088724377788785)
              ·
                refine ⟨6673421582316543283341589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8897895443088724377788785 6673421582316543283341589)
                ·
                  refine ⟨312816636671087966406637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6673421582316543283341589 312816636671087966406637)
                  ·
                    rfl

theorem cell22_2741437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_2741437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741437 prefixEnd_2741437 := by exact prefixLift 2741437
  have htrace : WordTrace (prefixWord ++ tailWord_2741437) baseStart_2741437 baseEnd_2741437 := by
    simpa [prefixWord, tailWord_2741437, baseEnd_2741437] using wordTrace_append hprefix tailTrace_2741437
  have hstable : (prefixWord ++ tailWord_2741437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741437).length < 2 ^ (prefixWord ++ tailWord_2741437).sum := by decide
  have hdescent : baseEnd_2741437 < baseStart_2741437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741482 : List Nat := [3, 1, 3, 1, 1, 3, 1, 9]
def baseStart_2741482 : Nat := 118140960795 + 2741482 * 2 ^ 59
def prefixEnd_2741482 : Nat := 4983230072969 + 3 ^ 40 * 2741482 * 2
def baseEnd_2741482 : Nat := 104273923825877642427197

theorem tailTrace_2741482 : CollatzResearch.WordTrace tailWord_2741482 prefixEnd_2741482 104273923825877642427197 := by
  unfold tailWord_2741482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24997515763521599173694675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66660042036057597796519133 24997515763521599173694675)
  ·
    refine ⟨37496273645282398760542013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24997515763521599173694675 37496273645282398760542013)
    ·
      refine ⟨14061102616980899535203255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37496273645282398760542013 14061102616980899535203255)
      ·
        refine ⟨21091653925471349302804883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14061102616980899535203255 21091653925471349302804883)
        ·
          refine ⟨31637480888207023954207325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21091653925471349302804883 31637480888207023954207325)
          ·
            refine ⟨11864055333077633982827747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31637480888207023954207325 11864055333077633982827747)
            ·
              refine ⟨17796082999616450974241621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11864055333077633982827747 17796082999616450974241621)
              ·
                refine ⟨104273923825877642427197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17796082999616450974241621 104273923825877642427197)
                ·
                  rfl

theorem cell22_2741482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_2741482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741482 prefixEnd_2741482 := by exact prefixLift 2741482
  have htrace : WordTrace (prefixWord ++ tailWord_2741482) baseStart_2741482 baseEnd_2741482 := by
    simpa [prefixWord, tailWord_2741482, baseEnd_2741482] using wordTrace_append hprefix tailTrace_2741482
  have hstable : (prefixWord ++ tailWord_2741482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741482).length < 2 ^ (prefixWord ++ tailWord_2741482).sum := by decide
  have hdescent : baseEnd_2741482 < baseStart_2741482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741522 : List Nat := [3, 2, 4, 2, 1, 2, 2, 2, 4]
def baseStart_2741522 : Nat := 118140960795 + 2741522 * 2 ^ 59
def prefixEnd_2741522 : Nat := 4983230072969 + 3 ^ 40 * 2741522 * 2
def baseEnd_2741522 : Nat := 312826335750117336948217

theorem tailTrace_2741522 : CollatzResearch.WordTrace tailWord_2741522 prefixEnd_2741522 312826335750117336948217 := by
  unfold tailWord_2741522
  simp only [CollatzResearch.WordTrace]
  refine ⟨24997880493485370881558705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66661014649294322350823213 24997880493485370881558705)
  ·
    refine ⟨18748410370114028161169029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24997880493485370881558705 18748410370114028161169029)
    ·
      refine ⟨3515326944396380280219193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18748410370114028161169029 3515326944396380280219193)
      ·
        refine ⟨2636495208297285210164395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3515326944396380280219193 2636495208297285210164395)
        ·
          refine ⟨3954742812445927815246593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2636495208297285210164395 3954742812445927815246593)
          ·
            refine ⟨2966057109334445861434945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3954742812445927815246593 2966057109334445861434945)
            ·
              refine ⟨2224542832000834396076209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2966057109334445861434945 2224542832000834396076209)
              ·
                refine ⟨1668407124000625797057157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224542832000834396076209 1668407124000625797057157)
                ·
                  refine ⟨312826335750117336948217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1668407124000625797057157 312826335750117336948217)
                  ·
                    rfl

theorem cell22_2741522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_2741522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741522 prefixEnd_2741522 := by exact prefixLift 2741522
  have htrace : WordTrace (prefixWord ++ tailWord_2741522) baseStart_2741522 baseEnd_2741522 := by
    simpa [prefixWord, tailWord_2741522, baseEnd_2741522] using wordTrace_append hprefix tailTrace_2741522
  have hstable : (prefixWord ++ tailWord_2741522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741522).length < 2 ^ (prefixWord ++ tailWord_2741522).sum := by decide
  have hdescent : baseEnd_2741522 < baseStart_2741522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741589 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 6]
def baseStart_2741589 : Nat := 118140960795 + 2741589 * 2 ^ 59
def prefixEnd_2741589 : Nat := 4983230072969 + 3 ^ 40 * 2741589 * 2
def baseEnd_2741589 : Nat := 312833980906528723139815

theorem tailTrace_2741589 : CollatzResearch.WordTrace tailWord_2741589 prefixEnd_2741589 312833980906528723139815 := by
  unfold tailWord_2741589
  simp only [CollatzResearch.WordTrace]
  refine ⟨99993965664698753968923821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66662643776465835979282547 99993965664698753968923821)
  ·
    refine ⟨37497737124262032738346433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99993965664698753968923821 37497737124262032738346433)
    ·
      refine ⟨28123302843196524553759825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37497737124262032738346433 28123302843196524553759825)
      ·
        refine ⟨21092477132397393415319869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28123302843196524553759825 21092477132397393415319869)
        ·
          refine ⟨7909678924649022530744951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21092477132397393415319869 7909678924649022530744951)
          ·
            refine ⟨11864518386973533796117427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7909678924649022530744951 11864518386973533796117427)
            ·
              refine ⟨17796777580460300694176141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11864518386973533796117427 17796777580460300694176141)
              ·
                refine ⟨6673791592672612760316053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17796777580460300694176141 6673791592672612760316053)
                ·
                  refine ⟨312833980906528723139815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6673791592672612760316053 312833980906528723139815)
                  ·
                    rfl

theorem cell22_2741589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_2741589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741589 prefixEnd_2741589 := by exact prefixLift 2741589
  have htrace : WordTrace (prefixWord ++ tailWord_2741589) baseStart_2741589 baseEnd_2741589 := by
    simpa [prefixWord, tailWord_2741589, baseEnd_2741589] using wordTrace_append hprefix tailTrace_2741589
  have hstable : (prefixWord ++ tailWord_2741589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741589).length < 2 ^ (prefixWord ++ tailWord_2741589).sum := by decide
  have hdescent : baseEnd_2741589 < baseStart_2741589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741608 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 1, 4]
def baseStart_2741608 : Nat := 118140960795 + 2741608 * 2 ^ 59
def prefixEnd_2741608 : Nat := 4983230072969 + 3 ^ 40 * 2741608 * 2
def baseEnd_2741608 : Nat := 938508446807876453194387

theorem tailTrace_2741608 : CollatzResearch.WordTrace tailWord_2741608 prefixEnd_2741608 938508446807876453194387 := by
  unfold tailWord_2741608
  simp only [CollatzResearch.WordTrace]
  refine ⟨49997329325814960106932739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66663105767753280142576985 49997329325814960106932739)
  ·
    refine ⟨74995993988722440160399109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49997329325814960106932739 74995993988722440160399109)
    ·
      refine ⟨14061748872885457530074833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74995993988722440160399109 14061748872885457530074833)
      ·
        refine ⟨10546311654664093147556125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14061748872885457530074833 10546311654664093147556125)
        ·
          refine ⟨3954866870499034930333547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10546311654664093147556125 3954866870499034930333547)
          ·
            refine ⟨5932300305748552395500321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954866870499034930333547 5932300305748552395500321)
            ·
              refine ⟨4449225229311414296625241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5932300305748552395500321 4449225229311414296625241)
              ·
                refine ⟨3336918921983560722468931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4449225229311414296625241 3336918921983560722468931)
                ·
                  refine ⟨5005378382975341083703397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336918921983560722468931 5005378382975341083703397)
                  ·
                    refine ⟨938508446807876453194387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5005378382975341083703397 938508446807876453194387)
                    ·
                      rfl

theorem cell22_2741608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_2741608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741608 prefixEnd_2741608 := by exact prefixLift 2741608
  have htrace : WordTrace (prefixWord ++ tailWord_2741608) baseStart_2741608 baseEnd_2741608 := by
    simpa [prefixWord, tailWord_2741608, baseEnd_2741608] using wordTrace_append hprefix tailTrace_2741608
  have hstable : (prefixWord ++ tailWord_2741608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741608).length < 2 ^ (prefixWord ++ tailWord_2741608).sum := by decide
  have hdescent : baseEnd_2741608 < baseStart_2741608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741636 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_2741636 : Nat := 118140960795 + 2741636 * 2 ^ 59
def prefixEnd_2741636 : Nat := 4983230072969 + 3 ^ 40 * 2741636 * 2
def baseEnd_2741636 : Nat := 938518031780093713494301

theorem tailTrace_2741636 : CollatzResearch.WordTrace tailWord_2741636 prefixEnd_2741636 938518031780093713494301 := by
  unfold tailWord_2741636
  simp only [CollatzResearch.WordTrace]
  refine ⟨49997839947764240497942381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66663786597018987330589841 49997839947764240497942381)
  ·
    refine ⟨18749189980411590186728393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49997839947764240497942381 18749189980411590186728393)
    ·
      refine ⟨14061892485308692640046295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18749189980411590186728393 14061892485308692640046295)
      ·
        refine ⟨21092838727963038960069443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14061892485308692640046295 21092838727963038960069443)
        ·
          refine ⟨31639258091944558440104165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21092838727963038960069443 31639258091944558440104165)
          ·
            refine ⟨5932360892239604707519531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31639258091944558440104165 5932360892239604707519531)
            ·
              refine ⟨8898541338359407061279297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5932360892239604707519531 8898541338359407061279297)
              ·
                refine ⟨6673906003769555295959473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8898541338359407061279297 6673906003769555295959473)
                ·
                  refine ⟨5005429502827166471969605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6673906003769555295959473 5005429502827166471969605)
                  ·
                    refine ⟨938518031780093713494301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5005429502827166471969605 938518031780093713494301)
                    ·
                      rfl

theorem cell22_2741636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_2741636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741636 prefixEnd_2741636 := by exact prefixLift 2741636
  have htrace : WordTrace (prefixWord ++ tailWord_2741636) baseStart_2741636 baseEnd_2741636 := by
    simpa [prefixWord, tailWord_2741636, baseEnd_2741636] using wordTrace_append hprefix tailTrace_2741636
  have hstable : (prefixWord ++ tailWord_2741636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741636).length < 2 ^ (prefixWord ++ tailWord_2741636).sum := by decide
  have hdescent : baseEnd_2741636 < baseStart_2741636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741739 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 3, 5]
def baseStart_2741739 : Nat := 118140960795 + 2741739 * 2 ^ 59
def prefixEnd_2741739 : Nat := 4983230072969 + 3 ^ 40 * 2741739 * 2
def baseEnd_2741739 : Nat := 938553290785035778168985

theorem tailTrace_2741739 : CollatzResearch.WordTrace tailWord_2741739 prefixEnd_2741739 938553290785035778168985 := by
  unfold tailWord_2741739
  simp only [CollatzResearch.WordTrace]
  refine ⟨99999436614155329586884271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66666291076103553057922847 99999436614155329586884271)
  ·
    refine ⟨149999154921232994380326407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99999436614155329586884271 149999154921232994380326407)
    ·
      refine ⟨224998732381849491570489611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149999154921232994380326407 224998732381849491570489611)
      ·
        refine ⟨337498098572774237355734417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224998732381849491570489611 337498098572774237355734417)
        ·
          refine ⟨253123573929580678016800813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337498098572774237355734417 253123573929580678016800813)
          ·
            refine ⟨94921340223592754256300305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253123573929580678016800813 94921340223592754256300305)
            ·
              refine ⟨71191005167694565692225229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94921340223592754256300305 71191005167694565692225229)
              ·
                refine ⟨26696626937885462134584461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71191005167694565692225229 26696626937885462134584461)
                ·
                  refine ⟨10011235101707048300469173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26696626937885462134584461 10011235101707048300469173)
                  ·
                    refine ⟨938553290785035778168985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10011235101707048300469173 938553290785035778168985)
                    ·
                      rfl

theorem cell22_2741739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_2741739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741739 prefixEnd_2741739 := by exact prefixLift 2741739
  have htrace : WordTrace (prefixWord ++ tailWord_2741739) baseStart_2741739 baseEnd_2741739 := by
    simpa [prefixWord, tailWord_2741739, baseEnd_2741739] using wordTrace_append hprefix tailTrace_2741739
  have hstable : (prefixWord ++ tailWord_2741739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741739).length < 2 ^ (prefixWord ++ tailWord_2741739).sum := by decide
  have hdescent : baseEnd_2741739 < baseStart_2741739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741743 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 1, 4]
def baseStart_2741743 : Nat := 118140960795 + 2741743 * 2 ^ 59
def prefixEnd_2741743 : Nat := 4983230072969 + 3 ^ 40 * 2741743 * 2
def baseEnd_2741743 : Nat := 938554660066781101068973

theorem tailTrace_2741743 : CollatzResearch.WordTrace tailWord_2741743 prefixEnd_2741743 938554660066781101068973 := by
  unfold tailWord_2741743
  simp only [CollatzResearch.WordTrace]
  refine ⟨99999582506140838270029883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66666388337427225513353255 99999582506140838270029883)
  ·
    refine ⟨149999373759211257405044825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99999582506140838270029883 149999373759211257405044825)
    ·
      refine ⟨112499530319408443053783619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149999373759211257405044825 112499530319408443053783619)
      ·
        refine ⟨168749295479112664580675429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112499530319408443053783619 168749295479112664580675429)
        ·
          refine ⟨31640492902333624608876643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168749295479112664580675429 31640492902333624608876643)
          ·
            refine ⟨47460739353500436913314965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31640492902333624608876643 47460739353500436913314965)
            ·
              refine ⟨2224722157195332980311639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47460739353500436913314965 2224722157195332980311639)
              ·
                refine ⟨3337083235792999470467459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224722157195332980311639 3337083235792999470467459)
                ·
                  refine ⟨5005624853689499205701189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337083235792999470467459 5005624853689499205701189)
                  ·
                    refine ⟨938554660066781101068973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5005624853689499205701189 938554660066781101068973)
                    ·
                      rfl

theorem cell22_2741743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 4].length) (baseStart_2741743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741743 prefixEnd_2741743 := by exact prefixLift 2741743
  have htrace : WordTrace (prefixWord ++ tailWord_2741743) baseStart_2741743 baseEnd_2741743 := by
    simpa [prefixWord, tailWord_2741743, baseEnd_2741743] using wordTrace_append hprefix tailTrace_2741743
  have hstable : (prefixWord ++ tailWord_2741743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741743).length < 2 ^ (prefixWord ++ tailWord_2741743).sum := by decide
  have hdescent : baseEnd_2741743 < baseStart_2741743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741769 : List Nat := [1, 2, 1, 1, 3, 1, 4, 9]
def baseStart_2741769 : Nat := 118140960795 + 2741769 * 2 ^ 59
def prefixEnd_2741769 : Nat := 4983230072969 + 3 ^ 40 * 2741769 * 2
def baseEnd_2741769 : Nat := 104284840044236188879877

theorem tailTrace_2741769 : CollatzResearch.WordTrace tailWord_2741769 prefixEnd_2741769 104284840044236188879877 := by
  unfold tailWord_2741769
  simp only [CollatzResearch.WordTrace]
  refine ⟨100000530804046644710476361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66667020536031096473650907 100000530804046644710476361)
  ·
    refine ⟨75000398103034983532857271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100000530804046644710476361 75000398103034983532857271)
    ·
      refine ⟨112500597154552475299285907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75000398103034983532857271 112500597154552475299285907)
      ·
        refine ⟨168750895731828712948928861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112500597154552475299285907 168750895731828712948928861)
        ·
          refine ⟨63281585899435767355848323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168750895731828712948928861 63281585899435767355848323)
          ·
            refine ⟨94922378849153651033772485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63281585899435767355848323 94922378849153651033772485)
            ·
              refine ⟨17797946034216309568832341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94922378849153651033772485 17797946034216309568832341)
              ·
                refine ⟨104284840044236188879877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17797946034216309568832341 104284840044236188879877)
                ·
                  rfl

theorem cell22_2741769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 9].length) (baseStart_2741769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741769 prefixEnd_2741769 := by exact prefixLift 2741769
  have htrace : WordTrace (prefixWord ++ tailWord_2741769) baseStart_2741769 baseEnd_2741769 := by
    simpa [prefixWord, tailWord_2741769, baseEnd_2741769] using wordTrace_append hprefix tailTrace_2741769
  have hstable : (prefixWord ++ tailWord_2741769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741769).length < 2 ^ (prefixWord ++ tailWord_2741769).sum := by decide
  have hdescent : baseEnd_2741769 < baseStart_2741769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741912 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 1, 4]
def baseStart_2741912 : Nat := 118140960795 + 2741912 * 2 ^ 59
def prefixEnd_2741912 : Nat := 4983230072969 + 3 ^ 40 * 2741912 * 2
def baseEnd_2741912 : Nat := 938612512220520993593455

theorem tailTrace_2741912 : CollatzResearch.WordTrace tailWord_2741912 prefixEnd_2741912 938612512220520993593455 := by
  unfold tailWord_2741912
  simp only [CollatzResearch.WordTrace]
  refine ⟨50002873221264290066465995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66670497628352386755287993 50002873221264290066465995)
  ·
    refine ⟨75004309831896435099698993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50002873221264290066465995 75004309831896435099698993)
    ·
      refine ⟨56253232373922326324774245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75004309831896435099698993 56253232373922326324774245)
      ·
        refine ⟨10547481070110436185895171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56253232373922326324774245 10547481070110436185895171)
        ·
          refine ⟨15821221605165654278842757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10547481070110436185895171 15821221605165654278842757)
          ·
            refine ⟨2966479050968560177283017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15821221605165654278842757 2966479050968560177283017)
            ·
              refine ⟨2224859288226420132962263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2966479050968560177283017 2224859288226420132962263)
              ·
                refine ⟨3337288932339630199443395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224859288226420132962263 3337288932339630199443395)
                ·
                  refine ⟨5005933398509445299165093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337288932339630199443395 5005933398509445299165093)
                  ·
                    refine ⟨938612512220520993593455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5005933398509445299165093 938612512220520993593455)
                    ·
                      rfl

theorem cell22_2741912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_2741912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741912 prefixEnd_2741912 := by exact prefixLift 2741912
  have htrace : WordTrace (prefixWord ++ tailWord_2741912) baseStart_2741912 baseEnd_2741912 := by
    simpa [prefixWord, tailWord_2741912, baseEnd_2741912] using wordTrace_append hprefix tailTrace_2741912
  have hstable : (prefixWord ++ tailWord_2741912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741912).length < 2 ^ (prefixWord ++ tailWord_2741912).sum := by decide
  have hdescent : baseEnd_2741912 < baseStart_2741912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741925 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 2, 3]
def baseStart_2741925 : Nat := 118140960795 + 2741925 * 2 ^ 59
def prefixEnd_2741925 : Nat := 4983230072969 + 3 ^ 40 * 2741925 * 2
def baseEnd_2741925 : Nat := 938616962386193293018415

theorem tailTrace_2741925 : CollatzResearch.WordTrace tailWord_2741925 prefixEnd_2741925 938616962386193293018415 := by
  unfold tailWord_2741925
  simp only [CollatzResearch.WordTrace]
  refine ⟨100006220591481483353155229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66670813727654322235436819 100006220591481483353155229)
  ·
    refine ⟨37502332721805556257433211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100006220591481483353155229 37502332721805556257433211)
    ·
      refine ⟨56253499082708334386149817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37502332721805556257433211 56253499082708334386149817)
      ·
        refine ⟨42190124312031250789612363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56253499082708334386149817 42190124312031250789612363)
        ·
          refine ⟨63285186468046876184418545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42190124312031250789612363 63285186468046876184418545)
          ·
            refine ⟨47463889851035157138313909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63285186468046876184418545 47463889851035157138313909)
            ·
              refine ⟨4449739673534545981716929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47463889851035157138313909 4449739673534545981716929)
              ·
                refine ⟨3337304755150909486287697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4449739673534545981716929 3337304755150909486287697)
                ·
                  refine ⟨2502978566363182114715773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3337304755150909486287697 2502978566363182114715773)
                  ·
                    refine ⟨938616962386193293018415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2502978566363182114715773 938616962386193293018415)
                    ·
                      rfl

theorem cell22_2741925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_2741925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741925 prefixEnd_2741925 := by exact prefixLift 2741925
  have htrace : WordTrace (prefixWord ++ tailWord_2741925) baseStart_2741925 baseEnd_2741925 := by
    simpa [prefixWord, tailWord_2741925, baseEnd_2741925] using wordTrace_append hprefix tailTrace_2741925
  have hstable : (prefixWord ++ tailWord_2741925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741925).length < 2 ^ (prefixWord ++ tailWord_2741925).sum := by decide
  have hdescent : baseEnd_2741925 < baseStart_2741925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741942 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2741942 : Nat := 118140960795 + 2741942 * 2 ^ 59
def prefixEnd_2741942 : Nat := 4983230072969 + 3 ^ 40 * 2741942 * 2
def baseEnd_2741942 : Nat := 938622781833610915343363

theorem tailTrace_2741942 : CollatzResearch.WordTrace tailWord_2741942 prefixEnd_2741942 938622781833610915343363 := by
  unfold tailWord_2741942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6250427539526243453532755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66671227088279930171016053 6250427539526243453532755)
  ·
    refine ⟨9375641309289365180299133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6250427539526243453532755 9375641309289365180299133)
    ·
      refine ⟨3515865490983511942612175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9375641309289365180299133 3515865490983511942612175)
      ·
        refine ⟨5273798236475267913918263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3515865490983511942612175 5273798236475267913918263)
        ·
          refine ⟨7910697354712901870877395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5273798236475267913918263 7910697354712901870877395)
          ·
            refine ⟨11866046032069352806316093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7910697354712901870877395 11866046032069352806316093)
            ·
              refine ⟨4449767262026007302368535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11866046032069352806316093 4449767262026007302368535)
              ·
                refine ⟨6674650893039010953552803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4449767262026007302368535 6674650893039010953552803)
                ·
                  refine ⟨10011976339558516430329205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6674650893039010953552803 10011976339558516430329205)
                  ·
                    refine ⟨938622781833610915343363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10011976339558516430329205 938622781833610915343363)
                    ·
                      rfl

theorem cell22_2741942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2741942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741942 prefixEnd_2741942 := by exact prefixLift 2741942
  have htrace : WordTrace (prefixWord ++ tailWord_2741942) baseStart_2741942 baseEnd_2741942 := by
    simpa [prefixWord, tailWord_2741942, baseEnd_2741942] using wordTrace_append hprefix tailTrace_2741942
  have hstable : (prefixWord ++ tailWord_2741942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741942).length < 2 ^ (prefixWord ++ tailWord_2741942).sum := by decide
  have hdescent : baseEnd_2741942 < baseStart_2741942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741974 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_2741974 : Nat := 118140960795 + 2741974 * 2 ^ 59
def prefixEnd_2741974 : Nat := 4983230072969 + 3 ^ 40 * 2741974 * 2
def baseEnd_2741974 : Nat := 938633736087573498543265

theorem tailTrace_2741974 : CollatzResearch.WordTrace tailWord_2741974 prefixEnd_2741974 938633736087573498543265 := by
  unfold tailWord_2741974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6250500485518997795105561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66672005178869309814459317 6250500485518997795105561)
  ·
    refine ⟨4687875364139248346329171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6250500485518997795105561 4687875364139248346329171)
    ·
      refine ⟨7031813046208872519493757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4687875364139248346329171 7031813046208872519493757)
      ·
        refine ⟨2636929892328327194810159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7031813046208872519493757 2636929892328327194810159)
        ·
          refine ⟨3955394838492490792215239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2636929892328327194810159 3955394838492490792215239)
          ·
            refine ⟨5933092257738736188322859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3955394838492490792215239 5933092257738736188322859)
            ·
              refine ⟨8899638386608104282484289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5933092257738736188322859 8899638386608104282484289)
              ·
                refine ⟨6674728789956078211863217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8899638386608104282484289 6674728789956078211863217)
                ·
                  refine ⟨5006046592467058658897413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6674728789956078211863217 5006046592467058658897413)
                  ·
                    refine ⟨938633736087573498543265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5006046592467058658897413 938633736087573498543265)
                    ·
                      rfl

theorem cell22_2741974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_2741974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741974 prefixEnd_2741974 := by exact prefixLift 2741974
  have htrace : WordTrace (prefixWord ++ tailWord_2741974) baseStart_2741974 baseEnd_2741974 := by
    simpa [prefixWord, tailWord_2741974, baseEnd_2741974] using wordTrace_append hprefix tailTrace_2741974
  have hstable : (prefixWord ++ tailWord_2741974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741974).length < 2 ^ (prefixWord ++ tailWord_2741974).sum := by decide
  have hdescent : baseEnd_2741974 < baseStart_2741974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741983 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 5]
def baseStart_2741983 : Nat := 118140960795 + 2741983 * 2 ^ 59
def prefixEnd_2741983 : Nat := 4983230072969 + 3 ^ 40 * 2741983 * 2
def baseEnd_2741983 : Nat := 312878938990500158356079

theorem tailTrace_2741983 : CollatzResearch.WordTrace tailWord_2741983 prefixEnd_2741983 312878938990500158356079 := by
  unfold tailWord_2741983
  simp only [CollatzResearch.WordTrace]
  refine ⟨100008336025271359258766603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66672224016847572839177735 100008336025271359258766603)
  ·
    refine ⟨150012504037907038888149905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100008336025271359258766603 150012504037907038888149905)
    ·
      refine ⟨112509378028430279166112429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150012504037907038888149905 112509378028430279166112429)
      ·
        refine ⟨42191016760661354687292161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112509378028430279166112429 42191016760661354687292161)
        ·
          refine ⟨31643262570496016015469121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42191016760661354687292161 31643262570496016015469121)
          ·
            refine ⟨23732446927872012011601841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31643262570496016015469121 23732446927872012011601841)
            ·
              refine ⟨17799335195904009008701381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23732446927872012011601841 17799335195904009008701381)
              ·
                refine ⟨3337375349232001689131509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17799335195904009008701381 3337375349232001689131509)
                ·
                  refine ⟨312878938990500158356079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3337375349232001689131509 312878938990500158356079)
                  ·
                    rfl

theorem cell22_2741983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 5].length) (baseStart_2741983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741983 prefixEnd_2741983 := by exact prefixLift 2741983
  have htrace : WordTrace (prefixWord ++ tailWord_2741983) baseStart_2741983 baseEnd_2741983 := by
    simpa [prefixWord, tailWord_2741983, baseEnd_2741983] using wordTrace_append hprefix tailTrace_2741983
  have hstable : (prefixWord ++ tailWord_2741983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741983).length < 2 ^ (prefixWord ++ tailWord_2741983).sum := by decide
  have hdescent : baseEnd_2741983 < baseStart_2741983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2741998 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2741998 : Nat := 118140960795 + 2741998 * 2 ^ 59
def prefixEnd_2741998 : Nat := 4983230072969 + 3 ^ 40 * 2741998 * 2
def baseEnd_2741998 : Nat := 938641951778045435943191

theorem tailTrace_2741998 : CollatzResearch.WordTrace tailWord_2741998 prefixEnd_2741998 938641951778045435943191 := by
  unfold tailWord_2741998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12501110390027127102570331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66672588746811344547041765 12501110390027127102570331)
  ·
    refine ⟨18751665585040690653855497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12501110390027127102570331 18751665585040690653855497)
    ·
      refine ⟨14063749188780517990391623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18751665585040690653855497 14063749188780517990391623)
      ·
        refine ⟨21095623783170776985587435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14063749188780517990391623 21095623783170776985587435)
        ·
          refine ⟨31643435674756165478381153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21095623783170776985587435 31643435674756165478381153)
          ·
            refine ⟨23732576756067124108785865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31643435674756165478381153 23732576756067124108785865)
            ·
              refine ⟨17799432567050343081589399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23732576756067124108785865 17799432567050343081589399)
              ·
                refine ⟨26699148850575514622384099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17799432567050343081589399 26699148850575514622384099)
                ·
                  refine ⟨40048723275863271933576149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26699148850575514622384099 40048723275863271933576149)
                  ·
                    refine ⟨938641951778045435943191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40048723275863271933576149 938641951778045435943191)
                    ·
                      rfl

theorem cell22_2741998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2741998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2741998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2741998 prefixEnd_2741998 := by exact prefixLift 2741998
  have htrace : WordTrace (prefixWord ++ tailWord_2741998) baseStart_2741998 baseEnd_2741998 := by
    simpa [prefixWord, tailWord_2741998, baseEnd_2741998] using wordTrace_append hprefix tailTrace_2741998
  have hstable : (prefixWord ++ tailWord_2741998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2741998).length < 2 ^ (prefixWord ++ tailWord_2741998).sum := by decide
  have hdescent : baseEnd_2741998 < baseStart_2741998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2741998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742030 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_2742030 : Nat := 118140960795 + 2742030 * 2 ^ 59
def prefixEnd_2742030 : Nat := 4983230072969 + 3 ^ 40 * 2742030 * 2
def baseEnd_2742030 : Nat := 938652906032008019143093

theorem tailTrace_2742030 : CollatzResearch.WordTrace tailWord_2742030 prefixEnd_2742030 938652906032008019143093 := by
  unfold tailWord_2742030
  simp only [CollatzResearch.WordTrace]
  refine ⟨12501256282012635785715943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66673366837400724190485029 12501256282012635785715943)
  ·
    refine ⟨18751884423018953678573915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12501256282012635785715943 18751884423018953678573915)
    ·
      refine ⟨28127826634528430517860873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18751884423018953678573915 28127826634528430517860873)
      ·
        refine ⟨21095869975896322888395655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28127826634528430517860873 21095869975896322888395655)
        ·
          refine ⟨31643804963844484332593483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21095869975896322888395655 31643804963844484332593483)
          ·
            refine ⟨47465707445766726498890225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31643804963844484332593483 47465707445766726498890225)
            ·
              refine ⟨35599280584325044874167669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47465707445766726498890225 35599280584325044874167669)
              ·
                refine ⟨3337432554780472956953219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35599280584325044874167669 3337432554780472956953219)
                ·
                  refine ⟨5006148832170709435429829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337432554780472956953219 5006148832170709435429829)
                  ·
                    refine ⟨938652906032008019143093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5006148832170709435429829 938652906032008019143093)
                    ·
                      rfl

theorem cell22_2742030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_2742030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742030 prefixEnd_2742030 := by exact prefixLift 2742030
  have htrace : WordTrace (prefixWord ++ tailWord_2742030) baseStart_2742030 baseEnd_2742030 := by
    simpa [prefixWord, tailWord_2742030, baseEnd_2742030] using wordTrace_append hprefix tailTrace_2742030
  have hstable : (prefixWord ++ tailWord_2742030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742030).length < 2 ^ (prefixWord ++ tailWord_2742030).sum := by decide
  have hdescent : baseEnd_2742030 < baseStart_2742030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742060 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_2742060 : Nat := 118140960795 + 2742060 * 2 ^ 59
def prefixEnd_2742060 : Nat := 4983230072969 + 3 ^ 40 * 2742060 * 2
def baseEnd_2742060 : Nat := 938663175645097940893001

theorem tailTrace_2742060 : CollatzResearch.WordTrace tailWord_2742060 prefixEnd_2742060 938663175645097940893001 := by
  unfold tailWord_2742060
  simp only [CollatzResearch.WordTrace]
  refine ⟨50005572222996200704659817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66674096297328267606213089 50005572222996200704659817)
  ·
    refine ⟨37504179167247150528494863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50005572222996200704659817 37504179167247150528494863)
    ·
      refine ⟨56256268750870725792742295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37504179167247150528494863 56256268750870725792742295)
      ·
        refine ⟨84384403126306088689113443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56256268750870725792742295 84384403126306088689113443)
        ·
          refine ⟨126576604689459133033670165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84384403126306088689113443 126576604689459133033670165)
          ·
            refine ⟨5933278344818396860953289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126576604689459133033670165 5933278344818396860953289)
            ·
              refine ⟨4449958758613797645714967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5933278344818396860953289 4449958758613797645714967)
              ·
                refine ⟨6674938137920696468572451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4449958758613797645714967 6674938137920696468572451)
                ·
                  refine ⟨10012407206881044702858677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6674938137920696468572451 10012407206881044702858677)
                  ·
                    refine ⟨938663175645097940893001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10012407206881044702858677 938663175645097940893001)
                    ·
                      rfl

theorem cell22_2742060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_2742060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742060 prefixEnd_2742060 := by exact prefixLift 2742060
  have htrace : WordTrace (prefixWord ++ tailWord_2742060) baseStart_2742060 baseEnd_2742060 := by
    simpa [prefixWord, tailWord_2742060, baseEnd_2742060] using wordTrace_append hprefix tailTrace_2742060
  have hstable : (prefixWord ++ tailWord_2742060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742060).length < 2 ^ (prefixWord ++ tailWord_2742060).sum := by decide
  have hdescent : baseEnd_2742060 < baseStart_2742060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742062 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_2742062 : Nat := 118140960795 + 2742062 * 2 ^ 59
def prefixEnd_2742062 : Nat := 4983230072969 + 3 ^ 40 * 2742062 * 2
def baseEnd_2742062 : Nat := 312887953428656867447665

theorem tailTrace_2742062 : CollatzResearch.WordTrace tailWord_2742062 prefixEnd_2742062 312887953428656867447665 := by
  unfold tailWord_2742062
  simp only [CollatzResearch.WordTrace]
  refine ⟨12501402173998144468861555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66674144927990103833928293 12501402173998144468861555)
  ·
    refine ⟨18752103260997216703292333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12501402173998144468861555 18752103260997216703292333)
    ·
      refine ⟨7032038722873956263734625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18752103260997216703292333 7032038722873956263734625)
      ·
        refine ⟨5274029042155467197800969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7032038722873956263734625 5274029042155467197800969)
        ·
          refine ⟨3955521781616600398350727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5274029042155467197800969 3955521781616600398350727)
          ·
            refine ⟨5933282672424900597526091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3955521781616600398350727 5933282672424900597526091)
            ·
              refine ⟨8899924008637350896289137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5933282672424900597526091 8899924008637350896289137)
              ·
                refine ⟨6674943006478013172216853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8899924008637350896289137 6674943006478013172216853)
                ·
                  refine ⟨312887953428656867447665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6674943006478013172216853 312887953428656867447665)
                  ·
                    rfl

theorem cell22_2742062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_2742062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742062 prefixEnd_2742062 := by exact prefixLift 2742062
  have htrace : WordTrace (prefixWord ++ tailWord_2742062) baseStart_2742062 baseEnd_2742062 := by
    simpa [prefixWord, tailWord_2742062, baseEnd_2742062] using wordTrace_append hprefix tailTrace_2742062
  have hstable : (prefixWord ++ tailWord_2742062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742062).length < 2 ^ (prefixWord ++ tailWord_2742062).sum := by decide
  have hdescent : baseEnd_2742062 < baseStart_2742062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742165 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_2742165 : Nat := 118140960795 + 2742165 * 2 ^ 59
def prefixEnd_2742165 : Nat := 4983230072969 + 3 ^ 40 * 2742165 * 2
def baseEnd_2742165 : Nat := 938699119290912667017679

theorem tailTrace_2742165 : CollatzResearch.WordTrace tailWord_2742165 prefixEnd_2742165 938699119290912667017679 := by
  unfold tailWord_2742165
  simp only [CollatzResearch.WordTrace]
  refine ⟨100014974110612004341891949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66676649407074669561261299 100014974110612004341891949)
  ·
    refine ⟨37505615291479501628209481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100014974110612004341891949 37505615291479501628209481)
    ·
      refine ⟨28129211468609626221157111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37505615291479501628209481 28129211468609626221157111)
      ·
        refine ⟨42193817202914439331735667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28129211468609626221157111 42193817202914439331735667)
        ·
          refine ⟨63290725804371658997603501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42193817202914439331735667 63290725804371658997603501)
          ·
            refine ⟨23734022176639372124101313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63290725804371658997603501 23734022176639372124101313)
            ·
              refine ⟨17800516632479529093075985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23734022176639372124101313 17800516632479529093075985)
              ·
                refine ⟨13350387474359646819806989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17800516632479529093075985 13350387474359646819806989)
                ·
                  refine ⟨5006395302884867557427621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13350387474359646819806989 5006395302884867557427621)
                  ·
                    refine ⟨938699119290912667017679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5006395302884867557427621 938699119290912667017679)
                    ·
                      rfl

theorem cell22_2742165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_2742165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742165 prefixEnd_2742165 := by exact prefixLift 2742165
  have htrace : WordTrace (prefixWord ++ tailWord_2742165) baseStart_2742165 baseEnd_2742165 := by
    simpa [prefixWord, tailWord_2742165, baseEnd_2742165] using wordTrace_append hprefix tailTrace_2742165
  have hstable : (prefixWord ++ tailWord_2742165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742165).length < 2 ^ (prefixWord ++ tailWord_2742165).sum := by decide
  have hdescent : baseEnd_2742165 < baseStart_2742165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742195 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 1, 5]
def baseStart_2742195 : Nat := 118140960795 + 2742195 * 2 ^ 59
def prefixEnd_2742195 : Nat := 4983230072969 + 3 ^ 40 * 2742195 * 2
def baseEnd_2742195 : Nat := 938709388904002588767587

theorem tailTrace_2742195 : CollatzResearch.WordTrace tailWord_2742195 prefixEnd_2742195 938709388904002588767587 := by
  unfold tailWord_2742195
  simp only [CollatzResearch.WordTrace]
  refine ⟨100016068300503319465484039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66677378867002212976989359 100016068300503319465484039)
  ·
    refine ⟨150024102450754979198226059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100016068300503319465484039 150024102450754979198226059)
    ·
      refine ⟨225036153676132468797339089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150024102450754979198226059 225036153676132468797339089)
      ·
        refine ⟨168777115257099351598004317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225036153676132468797339089 168777115257099351598004317)
        ·
          refine ⟨63291418221412256849251619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168777115257099351598004317 63291418221412256849251619)
          ·
            refine ⟨94937127332118385273877429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63291418221412256849251619 94937127332118385273877429)
            ·
              refine ⟨8900355687386098619426009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94937127332118385273877429 8900355687386098619426009)
              ·
                refine ⟨6675266765539573964569507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8900355687386098619426009 6675266765539573964569507)
                ·
                  refine ⟨10012900148309360946854261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6675266765539573964569507 10012900148309360946854261)
                  ·
                    refine ⟨938709388904002588767587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10012900148309360946854261 938709388904002588767587)
                    ·
                      rfl

theorem cell22_2742195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 5].length) (baseStart_2742195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742195 prefixEnd_2742195 := by exact prefixLift 2742195
  have htrace : WordTrace (prefixWord ++ tailWord_2742195) baseStart_2742195 baseEnd_2742195 := by
    simpa [prefixWord, tailWord_2742195, baseEnd_2742195] using wordTrace_append hprefix tailTrace_2742195
  have hstable : (prefixWord ++ tailWord_2742195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742195).length < 2 ^ (prefixWord ++ tailWord_2742195).sum := by decide
  have hdescent : baseEnd_2742195 < baseStart_2742195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742229 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 2, 3]
def baseStart_2742229 : Nat := 118140960795 + 2742229 * 2 ^ 59
def prefixEnd_2742229 : Nat := 4983230072969 + 3 ^ 40 * 2742229 * 2
def baseEnd_2742229 : Nat := 938721027798837833417483

theorem tailTrace_2742229 : CollatzResearch.WordTrace tailWord_2742229 prefixEnd_2742229 938721027798837833417483 := by
  unfold tailWord_2742229
  simp only [CollatzResearch.WordTrace]
  refine ⟨100017308382380143272221741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66678205588253428848147827 100017308382380143272221741)
  ·
    refine ⟨37506490643392553727083153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100017308382380143272221741 37506490643392553727083153)
    ·
      refine ⟨28129867982544415295312365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37506490643392553727083153 28129867982544415295312365)
      ·
        refine ⟨10548700493454155735742137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28129867982544415295312365 10548700493454155735742137)
        ·
          refine ⟨7911525370090616801806603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10548700493454155735742137 7911525370090616801806603)
          ·
            refine ⟨11867288055135925202709905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7911525370090616801806603 11867288055135925202709905)
            ·
              refine ⟨8900466041351943902032429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11867288055135925202709905 8900466041351943902032429)
              ·
                refine ⟨3337674765506978963262161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8900466041351943902032429 3337674765506978963262161)
                ·
                  refine ⟨2503256074130234222446621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3337674765506978963262161 2503256074130234222446621)
                  ·
                    refine ⟨938721027798837833417483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2503256074130234222446621 938721027798837833417483)
                    ·
                      rfl

theorem cell22_2742229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_2742229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742229 prefixEnd_2742229 := by exact prefixLift 2742229
  have htrace : WordTrace (prefixWord ++ tailWord_2742229) baseStart_2742229 baseEnd_2742229 := by
    simpa [prefixWord, tailWord_2742229, baseEnd_2742229] using wordTrace_append hprefix tailTrace_2742229
  have hstable : (prefixWord ++ tailWord_2742229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742229).length < 2 ^ (prefixWord ++ tailWord_2742229).sum := by decide
  have hdescent : baseEnd_2742229 < baseStart_2742229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742364 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2742364 : Nat := 118140960795 + 2742364 * 2 ^ 59
def prefixEnd_2742364 : Nat := 4983230072969 + 3 ^ 40 * 2742364 * 2
def baseEnd_2742364 : Nat := 938767241057742481292069

theorem tailTrace_2742364 : CollatzResearch.WordTrace tailWord_2742364 prefixEnd_2742364 938767241057742481292069 := by
  unfold tailWord_2742364
  simp only [CollatzResearch.WordTrace]
  refine ⟨50011116118445530664193073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66681488157927374218924097 50011116118445530664193073)
  ·
    refine ⟨37508337088834147998144805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50011116118445530664193073 37508337088834147998144805)
    ·
      refine ⟨7032813204156402749652151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37508337088834147998144805 7032813204156402749652151)
      ·
        refine ⟨10549219806234604124478227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7032813204156402749652151 10549219806234604124478227)
        ·
          refine ⟨15823829709351906186717341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10549219806234604124478227 15823829709351906186717341)
          ·
            refine ⟨5933936141006964820019003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15823829709351906186717341 5933936141006964820019003)
            ·
              refine ⟨8900904211510447230028505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5933936141006964820019003 8900904211510447230028505)
              ·
                refine ⟨6675678158632835422521379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8900904211510447230028505 6675678158632835422521379)
                ·
                  refine ⟨10013517237949253133782069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6675678158632835422521379 10013517237949253133782069)
                  ·
                    refine ⟨938767241057742481292069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10013517237949253133782069 938767241057742481292069)
                    ·
                      rfl

theorem cell22_2742364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2742364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742364 prefixEnd_2742364 := by exact prefixLift 2742364
  have htrace : WordTrace (prefixWord ++ tailWord_2742364) baseStart_2742364 baseEnd_2742364 := by
    simpa [prefixWord, tailWord_2742364, baseEnd_2742364] using wordTrace_append hprefix tailTrace_2742364
  have hstable : (prefixWord ++ tailWord_2742364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742364).length < 2 ^ (prefixWord ++ tailWord_2742364).sum := by decide
  have hdescent : baseEnd_2742364 < baseStart_2742364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742381 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_2742381 : Nat := 118140960795 + 2742381 * 2 ^ 59
def prefixEnd_2742381 : Nat := 4983230072969 + 3 ^ 40 * 2742381 * 2
def baseEnd_2742381 : Nat := 938773060505160103617017

theorem tailTrace_2742381 : CollatzResearch.WordTrace tailWord_2742381 prefixEnd_2742381 938773060505160103617017 := by
  unfold tailWord_2742381
  simp only [CollatzResearch.WordTrace]
  refine ⟨100022852277829473231754997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66681901518552982154503331 100022852277829473231754997)
  ·
    refine ⟨9377142401046513115477031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100022852277829473231754997 9377142401046513115477031)
    ·
      refine ⟨14065713601569769673215547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9377142401046513115477031 14065713601569769673215547)
      ·
        refine ⟨21098570402354654509823321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14065713601569769673215547 21098570402354654509823321)
        ·
          refine ⟨15823927801765990882367491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21098570402354654509823321 15823927801765990882367491)
          ·
            refine ⟨23735891702648986323551237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15823927801765990882367491 23735891702648986323551237)
            ·
              refine ⟨4450479694246684935665857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23735891702648986323551237 4450479694246684935665857)
              ·
                refine ⟨3337859770685013701749393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4450479694246684935665857 3337859770685013701749393)
                ·
                  refine ⟨2503394828013760276312045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3337859770685013701749393 2503394828013760276312045)
                  ·
                    refine ⟨938773060505160103617017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2503394828013760276312045 938773060505160103617017)
                    ·
                      rfl

theorem cell22_2742381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_2742381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742381 prefixEnd_2742381 := by exact prefixLift 2742381
  have htrace : WordTrace (prefixWord ++ tailWord_2742381) baseStart_2742381 baseEnd_2742381 := by
    simpa [prefixWord, tailWord_2742381, baseEnd_2742381] using wordTrace_append hprefix tailTrace_2742381
  have hstable : (prefixWord ++ tailWord_2742381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742381).length < 2 ^ (prefixWord ++ tailWord_2742381).sum := by decide
  have hdescent : baseEnd_2742381 < baseStart_2742381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742409 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 3, 3]
def baseStart_2742409 : Nat := 118140960795 + 2742409 * 2 ^ 59
def prefixEnd_2742409 : Nat := 4983230072969 + 3 ^ 40 * 2742409 * 2
def baseEnd_2742409 : Nat := 938782645477377363916931

theorem tailTrace_2742409 : CollatzResearch.WordTrace tailWord_2742409 prefixEnd_2742409 938782645477377363916931 := by
  unfold tailWord_2742409
  simp only [CollatzResearch.WordTrace]
  refine ⟨100023873521728034013774281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66682582347818689342516187 100023873521728034013774281)
  ·
    refine ⟨75017905141296025510330711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100023873521728034013774281 75017905141296025510330711)
    ·
      refine ⟨112526857711944038265496067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75017905141296025510330711 112526857711944038265496067)
      ·
        refine ⟨168790286567916057398244101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112526857711944038265496067 168790286567916057398244101)
        ·
          refine ⟨31648178731484260762170769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168790286567916057398244101 31648178731484260762170769)
          ·
            refine ⟨23736134048613195571628077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31648178731484260762170769 23736134048613195571628077)
            ·
              refine ⟨8901050268229948339360529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23736134048613195571628077 8901050268229948339360529)
              ·
                refine ⟨6675787701172461254520397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8901050268229948339360529 6675787701172461254520397)
                ·
                  refine ⟨2503420387939672970445149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6675787701172461254520397 2503420387939672970445149)
                  ·
                    refine ⟨938782645477377363916931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2503420387939672970445149 938782645477377363916931)
                    ·
                      rfl

theorem cell22_2742409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 3].length) (baseStart_2742409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742409 prefixEnd_2742409 := by exact prefixLift 2742409
  have htrace : WordTrace (prefixWord ++ tailWord_2742409) baseStart_2742409 baseEnd_2742409 := by
    simpa [prefixWord, tailWord_2742409, baseEnd_2742409] using wordTrace_append hprefix tailTrace_2742409
  have hstable : (prefixWord ++ tailWord_2742409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742409).length < 2 ^ (prefixWord ++ tailWord_2742409).sum := by decide
  have hdescent : baseEnd_2742409 < baseStart_2742409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742437 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_2742437 : Nat := 118140960795 + 2742437 * 2 ^ 59
def prefixEnd_2742437 : Nat := 4983230072969 + 3 ^ 40 * 2742437 * 2
def baseEnd_2742437 : Nat := 938792230449594624216845

theorem tailTrace_2742437 : CollatzResearch.WordTrace tailWord_2742437 prefixEnd_2742437 938792230449594624216845 := by
  unfold tailWord_2742437
  simp only [CollatzResearch.WordTrace]
  refine ⟨100024894765626594795793565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66683263177084396530529043 100024894765626594795793565)
  ·
    refine ⟨37509335537109973048422587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100024894765626594795793565 37509335537109973048422587)
    ·
      refine ⟨56264003305664959572633881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37509335537109973048422587 56264003305664959572633881)
      ·
        refine ⟨42198002479248719679475411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56264003305664959572633881 42198002479248719679475411)
        ·
          refine ⟨63297003718873079519213117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42198002479248719679475411 63297003718873079519213117)
          ·
            refine ⟨23736376394577404819704919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63297003718873079519213117 23736376394577404819704919)
            ·
              refine ⟨35604564591866107229557379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23736376394577404819704919 35604564591866107229557379)
              ·
                refine ⟨53406846887799160844336069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35604564591866107229557379 53406846887799160844336069)
                ·
                  refine ⟨10013783791462342658313013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53406846887799160844336069 10013783791462342658313013)
                  ·
                    refine ⟨938792230449594624216845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10013783791462342658313013 938792230449594624216845)
                    ·
                      rfl

theorem cell22_2742437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_2742437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742437 prefixEnd_2742437 := by exact prefixLift 2742437
  have htrace : WordTrace (prefixWord ++ tailWord_2742437) baseStart_2742437 baseEnd_2742437 := by
    simpa [prefixWord, tailWord_2742437, baseEnd_2742437] using wordTrace_append hprefix tailTrace_2742437
  have hstable : (prefixWord ++ tailWord_2742437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742437).length < 2 ^ (prefixWord ++ tailWord_2742437).sum := by decide
  have hdescent : baseEnd_2742437 < baseStart_2742437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742469 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_2742469 : Nat := 118140960795 + 2742469 * 2 ^ 59
def prefixEnd_2742469 : Nat := 4983230072969 + 3 ^ 40 * 2742469 * 2
def baseEnd_2742469 : Nat := 938803184703557207416747

theorem tailTrace_2742469 : CollatzResearch.WordTrace tailWord_2742469 prefixEnd_2742469 938803184703557207416747 := by
  unfold tailWord_2742469
  simp only [CollatzResearch.WordTrace]
  refine ⟨100026061901510664260958461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66684041267673776173972307 100026061901510664260958461)
  ·
    refine ⟨37509773213066499097859423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100026061901510664260958461 37509773213066499097859423)
    ·
      refine ⟨56264659819599748646789135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37509773213066499097859423 56264659819599748646789135)
      ·
        refine ⟨84396989729399622970183703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56264659819599748646789135 84396989729399622970183703)
        ·
          refine ⟨126595484594099434455275555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84396989729399622970183703 126595484594099434455275555)
          ·
            refine ⟨189893226891149151682913333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126595484594099434455275555 189893226891149151682913333)
            ·
              refine ⟨17802490021045232970273125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189893226891149151682913333 17802490021045232970273125)
              ·
                refine ⟨3337966878945981181926211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17802490021045232970273125 3337966878945981181926211)
                ·
                  refine ⟨5006950318418971772889317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337966878945981181926211 5006950318418971772889317)
                  ·
                    refine ⟨938803184703557207416747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5006950318418971772889317 938803184703557207416747)
                    ·
                      rfl

theorem cell22_2742469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_2742469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742469 prefixEnd_2742469 := by exact prefixLift 2742469
  have htrace : WordTrace (prefixWord ++ tailWord_2742469) baseStart_2742469 baseEnd_2742469 := by
    simpa [prefixWord, tailWord_2742469, baseEnd_2742469] using wordTrace_append hprefix tailTrace_2742469
  have hstable : (prefixWord ++ tailWord_2742469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742469).length < 2 ^ (prefixWord ++ tailWord_2742469).sum := by decide
  have hdescent : baseEnd_2742469 < baseStart_2742469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742501 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 6]
def baseStart_2742501 : Nat := 118140960795 + 2742501 * 2 ^ 59
def prefixEnd_2742501 : Nat := 4983230072969 + 3 ^ 40 * 2742501 * 2
def baseEnd_2742501 : Nat := 312938046319173263538883

theorem tailTrace_2742501 : CollatzResearch.WordTrace tailWord_2742501 prefixEnd_2742501 312938046319173263538883 := by
  unfold tailWord_2742501
  simp only [CollatzResearch.WordTrace]
  refine ⟨100027229037394733726123357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66684819358263155817415571 100027229037394733726123357)
  ·
    refine ⟨37510210889023025147296259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100027229037394733726123357 37510210889023025147296259)
    ·
      refine ⟨56265316333534537720944389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37510210889023025147296259 56265316333534537720944389)
      ·
        refine ⟨10549746812537725822677073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56265316333534537720944389 10549746812537725822677073)
        ·
          refine ⟨7912310109403294367007805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10549746812537725822677073 7912310109403294367007805)
          ·
            refine ⟨2967116291026235387627927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7912310109403294367007805 2967116291026235387627927)
            ·
              refine ⟨4450674436539353081441891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2967116291026235387627927 4450674436539353081441891)
              ·
                refine ⟨6676011654809029622162837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4450674436539353081441891 6676011654809029622162837)
                ·
                  refine ⟨312938046319173263538883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6676011654809029622162837 312938046319173263538883)
                  ·
                    rfl

theorem cell22_2742501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_2742501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742501 prefixEnd_2742501 := by exact prefixLift 2742501
  have htrace : WordTrace (prefixWord ++ tailWord_2742501) baseStart_2742501 baseEnd_2742501 := by
    simpa [prefixWord, tailWord_2742501, baseEnd_2742501] using wordTrace_append hprefix tailTrace_2742501
  have hstable : (prefixWord ++ tailWord_2742501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742501).length < 2 ^ (prefixWord ++ tailWord_2742501).sum := by decide
  have hdescent : baseEnd_2742501 < baseStart_2742501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742559 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 2, 6]
def baseStart_2742559 : Nat := 118140960795 + 2742559 * 2 ^ 59
def prefixEnd_2742559 : Nat := 4983230072969 + 3 ^ 40 * 2742559 * 2
def baseEnd_2742559 : Nat := 938833993542826972666471

theorem tailTrace_2742559 : CollatzResearch.WordTrace tailWord_2742559 prefixEnd_2742559 938833993542826972666471 := by
  unfold tailWord_2742559
  simp only [CollatzResearch.WordTrace]
  refine ⟨100029344471184609631734731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66686229647456406421156487 100029344471184609631734731)
  ·
    refine ⟨150044016706776914447602097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100029344471184609631734731 150044016706776914447602097)
    ·
      refine ⟨112533012530082685835701573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150044016706776914447602097 112533012530082685835701573)
      ·
        refine ⟨21099939849390503594194045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112533012530082685835701573 21099939849390503594194045)
        ·
          refine ⟨7912477443521438847822767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21099939849390503594194045 7912477443521438847822767)
          ·
            refine ⟨11868716165282158271734151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7912477443521438847822767 11868716165282158271734151)
            ·
              refine ⟨17803074247923237407601227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11868716165282158271734151 17803074247923237407601227)
              ·
                refine ⟨26704611371884856111401841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17803074247923237407601227 26704611371884856111401841)
                ·
                  refine ⟨20028458528913642083551381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26704611371884856111401841 20028458528913642083551381)
                  ·
                    refine ⟨938833993542826972666471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20028458528913642083551381 938833993542826972666471)
                    ·
                      rfl

theorem cell22_2742559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_2742559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742559 prefixEnd_2742559 := by exact prefixLift 2742559
  have htrace : WordTrace (prefixWord ++ tailWord_2742559) baseStart_2742559 baseEnd_2742559 := by
    simpa [prefixWord, tailWord_2742559, baseEnd_2742559] using wordTrace_append hprefix tailTrace_2742559
  have hstable : (prefixWord ++ tailWord_2742559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742559).length < 2 ^ (prefixWord ++ tailWord_2742559).sum := by decide
  have hdescent : baseEnd_2742559 < baseStart_2742559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742578 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_2742578 : Nat := 118140960795 + 2742578 * 2 ^ 59
def prefixEnd_2742578 : Nat := 4983230072969 + 3 ^ 40 * 2742578 * 2
def baseEnd_2742578 : Nat := 938840497631117256441413

theorem tailTrace_2742578 : CollatzResearch.WordTrace tailWord_2742578 prefixEnd_2742578 938840497631117256441413 := by
  unfold tailWord_2742578
  simp only [CollatzResearch.WordTrace]
  refine ⟨25007509364528943969169097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66686691638743850584450925 25007509364528943969169097)
  ·
    refine ⟨18755632023396707976876823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25007509364528943969169097 18755632023396707976876823)
    ·
      refine ⟨28133448035095061965315235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18755632023396707976876823 28133448035095061965315235)
      ·
        refine ⟨42200172052642592947972853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28133448035095061965315235 42200172052642592947972853)
        ·
          refine ⟨3956266129935243088872455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42200172052642592947972853 3956266129935243088872455)
          ·
            refine ⟨5934399194902864633308683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956266129935243088872455 5934399194902864633308683)
            ·
              refine ⟨8901598792354296949963025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5934399194902864633308683 8901598792354296949963025)
              ·
                refine ⟨6676199094265722712472269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8901598792354296949963025 6676199094265722712472269)
                ·
                  refine ⟨2503574660349646017177101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6676199094265722712472269 2503574660349646017177101)
                  ·
                    refine ⟨938840497631117256441413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2503574660349646017177101 938840497631117256441413)
                    ·
                      rfl

theorem cell22_2742578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_2742578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742578 prefixEnd_2742578 := by exact prefixLift 2742578
  have htrace : WordTrace (prefixWord ++ tailWord_2742578) baseStart_2742578 baseEnd_2742578 := by
    simpa [prefixWord, tailWord_2742578, baseEnd_2742578] using wordTrace_append hprefix tailTrace_2742578
  have hstable : (prefixWord ++ tailWord_2742578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742578).length < 2 ^ (prefixWord ++ tailWord_2742578).sum := by decide
  have hdescent : baseEnd_2742578 < baseStart_2742578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742646 : List Nat := [5, 1, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_2742646 : Nat := 118140960795 + 2742646 * 2 ^ 59
def prefixEnd_2742646 : Nat := 4983230072969 + 3 ^ 40 * 2742646 * 2
def baseEnd_2742646 : Nat := 938863775420787745741205

theorem tailTrace_2742646 : CollatzResearch.WordTrace tailWord_2742646 prefixEnd_2742646 938863775420787745741205 := by
  unfold tailWord_2742646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6252032351366838968134487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66688345081246282326767861 6252032351366838968134487)
  ·
    refine ⟨9378048527050258452201731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6252032351366838968134487 9378048527050258452201731)
    ·
      refine ⟨14067072790575387678302597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9378048527050258452201731 14067072790575387678302597)
      ·
        refine ⟨2637576148232885189681737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14067072790575387678302597 2637576148232885189681737)
        ·
          refine ⟨1978182111174663892261303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2637576148232885189681737 1978182111174663892261303)
          ·
            refine ⟨2967273166761995838391955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978182111174663892261303 2967273166761995838391955)
            ·
              refine ⟨4450909750142993757587933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2967273166761995838391955 4450909750142993757587933)
              ·
                refine ⟨1669091156303622659095475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4450909750142993757587933 1669091156303622659095475)
                ·
                  refine ⟨2503636734455433988643213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669091156303622659095475 2503636734455433988643213)
                  ·
                    refine ⟨938863775420787745741205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2503636734455433988643213 938863775420787745741205)
                    ·
                      rfl

theorem cell22_2742646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_2742646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742646 prefixEnd_2742646 := by exact prefixLift 2742646
  have htrace : WordTrace (prefixWord ++ tailWord_2742646) baseStart_2742646 baseEnd_2742646 := by
    simpa [prefixWord, tailWord_2742646, baseEnd_2742646] using wordTrace_append hprefix tailTrace_2742646
  have hstable : (prefixWord ++ tailWord_2742646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742646).length < 2 ^ (prefixWord ++ tailWord_2742646).sum := by decide
  have hdescent : baseEnd_2742646 < baseStart_2742646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742651 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 4, 3]
def baseStart_2742651 : Nat := 118140960795 + 2742651 * 2 ^ 59
def prefixEnd_2742651 : Nat := 4983230072969 + 3 ^ 40 * 2742651 * 2
def baseEnd_2742651 : Nat := 938865487022969399366189

theorem tailTrace_2742651 : CollatzResearch.WordTrace tailWord_2742651 prefixEnd_2742651 938865487022969399366189 := by
  unfold tailWord_2742651
  simp only [CollatzResearch.WordTrace]
  refine ⟨100032699986851309344083807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66688466657900872896055871 100032699986851309344083807)
  ·
    refine ⟨150049049980276964016125711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100032699986851309344083807 150049049980276964016125711)
    ·
      refine ⟨225073574970415446024188567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150049049980276964016125711 225073574970415446024188567)
      ·
        refine ⟨337610362455623169036282851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225073574970415446024188567 337610362455623169036282851)
        ·
          refine ⟨506415543683434753554424277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337610362455623169036282851 506415543683434753554424277)
          ·
            refine ⟨11869114305080502036431819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 506415543683434753554424277 11869114305080502036431819)
            ·
              refine ⟨17803671457620753054647729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11869114305080502036431819 17803671457620753054647729)
              ·
                refine ⟨13352753593215564790985797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17803671457620753054647729 13352753593215564790985797)
                ·
                  refine ⟨2503641298727918398309837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13352753593215564790985797 2503641298727918398309837)
                  ·
                    refine ⟨938865487022969399366189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2503641298727918398309837 938865487022969399366189)
                    ·
                      rfl

theorem cell22_2742651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 3].length) (baseStart_2742651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742651 prefixEnd_2742651 := by exact prefixLift 2742651
  have htrace : WordTrace (prefixWord ++ tailWord_2742651) baseStart_2742651 baseEnd_2742651 := by
    simpa [prefixWord, tailWord_2742651, baseEnd_2742651] using wordTrace_append hprefix tailTrace_2742651
  have hstable : (prefixWord ++ tailWord_2742651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742651).length < 2 ^ (prefixWord ++ tailWord_2742651).sum := by decide
  have hdescent : baseEnd_2742651 < baseStart_2742651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742653 : List Nat := [1, 4, 1, 1, 2, 3, 3, 3, 4]
def baseStart_2742653 : Nat := 118140960795 + 2742653 * 2 ^ 59
def prefixEnd_2742653 : Nat := 4983230072969 + 3 ^ 40 * 2742653 * 2
def baseEnd_2742653 : Nat := 312955390554614020272061

theorem tailTrace_2742653 : CollatzResearch.WordTrace tailWord_2742653 prefixEnd_2742653 312955390554614020272061 := by
  unfold tailWord_2742653
  simp only [CollatzResearch.WordTrace]
  refine ⟨100032772932844063685656613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66688515288562709123771075 100032772932844063685656613)
  ·
    refine ⟨18756144924908261941060615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100032772932844063685656613 18756144924908261941060615)
    ·
      refine ⟨28134217387362392911590923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18756144924908261941060615 28134217387362392911590923)
      ·
        refine ⟨42201326081043589367386385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28134217387362392911590923 42201326081043589367386385)
        ·
          refine ⟨31650994560782692025539789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42201326081043589367386385 31650994560782692025539789)
          ·
            refine ⟨11869122960293509509577421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31650994560782692025539789 11869122960293509509577421)
            ·
              refine ⟨4450921110110066066091533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11869122960293509509577421 4450921110110066066091533)
              ·
                refine ⟨1669095416291274774784325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4450921110110066066091533 1669095416291274774784325)
                ·
                  refine ⟨312955390554614020272061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669095416291274774784325 312955390554614020272061)
                  ·
                    rfl

theorem cell22_2742653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_2742653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742653 prefixEnd_2742653 := by exact prefixLift 2742653
  have htrace : WordTrace (prefixWord ++ tailWord_2742653) baseStart_2742653 baseEnd_2742653 := by
    simpa [prefixWord, tailWord_2742653, baseEnd_2742653] using wordTrace_append hprefix tailTrace_2742653
  have hstable : (prefixWord ++ tailWord_2742653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742653).length < 2 ^ (prefixWord ++ tailWord_2742653).sum := by decide
  have hdescent : baseEnd_2742653 < baseStart_2742653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742685 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_2742685 : Nat := 118140960795 + 2742685 * 2 ^ 59
def prefixEnd_2742685 : Nat := 4983230072969 + 3 ^ 40 * 2742685 * 2
def baseEnd_2742685 : Nat := 938877125917804644016085

theorem tailTrace_2742685 : CollatzResearch.WordTrace tailWord_2742685 prefixEnd_2742685 938877125917804644016085 := by
  unfold tailWord_2742685
  simp only [CollatzResearch.WordTrace]
  refine ⟨100033940068728133150821509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66689293379152088767214339 100033940068728133150821509)
  ·
    refine ⟨18756363762886524965779033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100033940068728133150821509 18756363762886524965779033)
    ·
      refine ⟨14067272822164893724334275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18756363762886524965779033 14067272822164893724334275)
      ·
        refine ⟨21100909233247340586501413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14067272822164893724334275 21100909233247340586501413)
        ·
          refine ⟨3956420481233876359969015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21100909233247340586501413 3956420481233876359969015)
          ·
            refine ⟨5934630721850814539953523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956420481233876359969015 5934630721850814539953523)
            ·
              refine ⟨8901946082776221809930285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5934630721850814539953523 8901946082776221809930285)
              ·
                refine ⟨3338229781041083178723857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8901946082776221809930285 3338229781041083178723857)
                ·
                  refine ⟨2503672335780812384042893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3338229781041083178723857 2503672335780812384042893)
                  ·
                    refine ⟨938877125917804644016085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2503672335780812384042893 938877125917804644016085)
                    ·
                      rfl

theorem cell22_2742685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_2742685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742685 prefixEnd_2742685 := by exact prefixLift 2742685
  have htrace : WordTrace (prefixWord ++ tailWord_2742685) baseStart_2742685 baseEnd_2742685 := by
    simpa [prefixWord, tailWord_2742685, baseEnd_2742685] using wordTrace_append hprefix tailTrace_2742685
  have hstable : (prefixWord ++ tailWord_2742685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742685).length < 2 ^ (prefixWord ++ tailWord_2742685).sum := by decide
  have hdescent : baseEnd_2742685 < baseStart_2742685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742721 : List Nat := [1, 2, 7, 1, 1, 2, 2, 2, 4]
def baseStart_2742721 : Nat := 118140960795 + 2742721 * 2 ^ 59
def prefixEnd_2742721 : Nat := 4983230072969 + 3 ^ 40 * 2742721 * 2
def baseEnd_2742721 : Nat := 312963149817837516705325

theorem tailTrace_2742721 : CollatzResearch.WordTrace tailWord_2742721 prefixEnd_2742721 312963149817837516705325 := by
  unfold tailWord_2742721
  simp only [CollatzResearch.WordTrace]
  refine ⟨100035253096597711299132017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66690168731065140866088011 100035253096597711299132017)
  ·
    refine ⟨75026439822448283474349013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100035253096597711299132017 75026439822448283474349013)
    ·
      refine ⟨1758432183338631643930055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 75026439822448283474349013 1758432183338631643930055)
      ·
        refine ⟨2637648275007947465895083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1758432183338631643930055 2637648275007947465895083)
        ·
          refine ⟨3956472412511921198842625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637648275007947465895083 3956472412511921198842625)
          ·
            refine ⟨2967354309383940899131969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3956472412511921198842625 2967354309383940899131969)
            ·
              refine ⟨2225515732037955674348977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2967354309383940899131969 2225515732037955674348977)
              ·
                refine ⟨1669136799028466755761733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2225515732037955674348977 1669136799028466755761733)
                ·
                  refine ⟨312963149817837516705325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669136799028466755761733 312963149817837516705325)
                  ·
                    rfl

theorem cell22_2742721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 4].length) (baseStart_2742721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742721 prefixEnd_2742721 := by exact prefixLift 2742721
  have htrace : WordTrace (prefixWord ++ tailWord_2742721) baseStart_2742721 baseEnd_2742721 := by
    simpa [prefixWord, tailWord_2742721, baseEnd_2742721] using wordTrace_append hprefix tailTrace_2742721
  have hstable : (prefixWord ++ tailWord_2742721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742721).length < 2 ^ (prefixWord ++ tailWord_2742721).sum := by decide
  have hdescent : baseEnd_2742721 < baseStart_2742721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742730 : List Nat := [3, 1, 2, 1, 2, 2, 3, 4, 1, 3]
def baseStart_2742730 : Nat := 118140960795 + 2742730 * 2 ^ 59
def prefixEnd_2742730 : Nat := 4983230072969 + 3 ^ 40 * 2742730 * 2
def baseEnd_2742730 : Nat := 938892530337439526640947

theorem tailTrace_2742730 : CollatzResearch.WordTrace tailWord_2742730 prefixEnd_2742730 938892530337439526640947 := by
  unfold tailWord_2742730
  simp only [CollatzResearch.WordTrace]
  refine ⟨25008895338391276459052411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66690387569043403890806429 25008895338391276459052411)
  ·
    refine ⟨37513343007586914688578617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25008895338391276459052411 37513343007586914688578617)
    ·
      refine ⟨28135007255690186016433963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37513343007586914688578617 28135007255690186016433963)
      ·
        refine ⟨42202510883535279024650945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28135007255690186016433963 42202510883535279024650945)
        ·
          refine ⟨31651883162651459268488209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42202510883535279024650945 31651883162651459268488209)
          ·
            refine ⟨23738912371988594451366157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31651883162651459268488209 23738912371988594451366157)
            ·
              refine ⟨8902092139495722919262309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23738912371988594451366157 8902092139495722919262309)
              ·
                refine ⟨1669142276155448047361683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8902092139495722919262309 1669142276155448047361683)
                ·
                  refine ⟨2503713414233172071042525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669142276155448047361683 2503713414233172071042525)
                  ·
                    refine ⟨938892530337439526640947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2503713414233172071042525 938892530337439526640947)
                    ·
                      rfl

theorem cell22_2742730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_2742730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742730 prefixEnd_2742730 := by exact prefixLift 2742730
  have htrace : WordTrace (prefixWord ++ tailWord_2742730) baseStart_2742730 baseEnd_2742730 := by
    simpa [prefixWord, tailWord_2742730, baseEnd_2742730] using wordTrace_append hprefix tailTrace_2742730
  have hstable : (prefixWord ++ tailWord_2742730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742730).length < 2 ^ (prefixWord ++ tailWord_2742730).sum := by decide
  have hdescent : baseEnd_2742730 < baseStart_2742730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742741 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_2742741 : Nat := 118140960795 + 2742741 * 2 ^ 59
def prefixEnd_2742741 : Nat := 4983230072969 + 3 ^ 40 * 2742741 * 2
def baseEnd_2742741 : Nat := 938896295862239164615913

theorem tailTrace_2742741 : CollatzResearch.WordTrace tailWord_2742741 prefixEnd_2742741 938896295862239164615913 := by
  unfold tailWord_2742741
  simp only [CollatzResearch.WordTrace]
  refine ⟨100035982556525254714860077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66690655037683503143240051 100035982556525254714860077)
  ·
    refine ⟨37513493458696970518072529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100035982556525254714860077 37513493458696970518072529)
    ·
      refine ⟨28135120094022727888554397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37513493458696970518072529 28135120094022727888554397)
      ·
        refine ⟨10550670035258522958207899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28135120094022727888554397 10550670035258522958207899)
        ·
          refine ⟨15826005052887784437311849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10550670035258522958207899 15826005052887784437311849)
          ·
            refine ⟨11869503789665838327983887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15826005052887784437311849 11869503789665838327983887)
            ·
              refine ⟨17804255684498757491975831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11869503789665838327983887 17804255684498757491975831)
              ·
                refine ⟨26706383526748136237963747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17804255684498757491975831 26706383526748136237963747)
                ·
                  refine ⟨40059575290122204356945621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26706383526748136237963747 40059575290122204356945621)
                  ·
                    refine ⟨938896295862239164615913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40059575290122204356945621 938896295862239164615913)
                    ·
                      rfl

theorem cell22_2742741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_2742741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742741 prefixEnd_2742741 := by exact prefixLift 2742741
  have htrace : WordTrace (prefixWord ++ tailWord_2742741) baseStart_2742741 baseEnd_2742741 := by
    simpa [prefixWord, tailWord_2742741, baseEnd_2742741] using wordTrace_append hprefix tailTrace_2742741
  have hstable : (prefixWord ++ tailWord_2742741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742741).length < 2 ^ (prefixWord ++ tailWord_2742741).sum := by decide
  have hdescent : baseEnd_2742741 < baseStart_2742741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742788 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 6]
def baseStart_2742788 : Nat := 118140960795 + 2742788 * 2 ^ 59
def prefixEnd_2742788 : Nat := 4983230072969 + 3 ^ 40 * 2742788 * 2
def baseEnd_2742788 : Nat := 312970794974248902896923

theorem tailTrace_2742788 : CollatzResearch.WordTrace tailWord_2742788 prefixEnd_2742788 312970794974248902896923 := by
  unfold tailWord_2742788
  simp only [CollatzResearch.WordTrace]
  refine ⟨50018848393677490870910509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66691797858236654494547345 50018848393677490870910509)
  ·
    refine ⟨18757068147629059076591441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50018848393677490870910509 18757068147629059076591441)
    ·
      refine ⟨14067801110721794307443581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18757068147629059076591441 14067801110721794307443581)
      ·
        refine ⟨5275425416520672865291343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14067801110721794307443581 5275425416520672865291343)
        ·
          refine ⟨7913138124781009297937015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5275425416520672865291343 7913138124781009297937015)
          ·
            refine ⟨11869707187171513946905523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7913138124781009297937015 11869707187171513946905523)
            ·
              refine ⟨17804560780757270920358285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11869707187171513946905523 17804560780757270920358285)
              ·
                refine ⟨6676710292783976595134357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17804560780757270920358285 6676710292783976595134357)
                ·
                  refine ⟨312970794974248902896923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6676710292783976595134357 312970794974248902896923)
                  ·
                    rfl

theorem cell22_2742788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_2742788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742788 prefixEnd_2742788 := by exact prefixLift 2742788
  have htrace : WordTrace (prefixWord ++ tailWord_2742788) baseStart_2742788 baseEnd_2742788 := by
    simpa [prefixWord, tailWord_2742788, baseEnd_2742788] using wordTrace_append hprefix tailTrace_2742788
  have hstable : (prefixWord ++ tailWord_2742788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742788).length < 2 ^ (prefixWord ++ tailWord_2742788).sum := by decide
  have hdescent : baseEnd_2742788 < baseStart_2742788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742801 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 6, 4]
def baseStart_2742801 : Nat := 118140960795 + 2742801 * 2 ^ 59
def prefixEnd_2742801 : Nat := 4983230072969 + 3 ^ 40 * 2742801 * 2
def baseEnd_2742801 : Nat := 938916835088419008115729

theorem tailTrace_2742801 : CollatzResearch.WordTrace tailWord_2742801 prefixEnd_2742801 938916835088419008115729 := by
  unfold tailWord_2742801
  simp only [CollatzResearch.WordTrace]
  refine ⟨100038170936307884962044257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66692113957538589974696171 100038170936307884962044257)
  ·
    refine ⟨75028628202230913721533193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100038170936307884962044257 75028628202230913721533193)
    ·
      refine ⟨56271471151673185291149895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75028628202230913721533193 56271471151673185291149895)
      ·
        refine ⟨84407206727509777936724843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56271471151673185291149895 84407206727509777936724843)
        ·
          refine ⟨126610810091264666905087265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84407206727509777936724843 126610810091264666905087265)
          ·
            refine ⟨94958107568448500178815449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126610810091264666905087265 94958107568448500178815449)
            ·
              refine ⟨71218580676336375134111587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94958107568448500178815449 71218580676336375134111587)
              ·
                refine ⟨106827871014504562701167381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71218580676336375134111587 106827871014504562701167381)
                ·
                  refine ⟨5007556453804901376617221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106827871014504562701167381 5007556453804901376617221)
                  ·
                    refine ⟨938916835088419008115729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5007556453804901376617221 938916835088419008115729)
                    ·
                      rfl

theorem cell22_2742801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_2742801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742801 prefixEnd_2742801 := by exact prefixLift 2742801
  have htrace : WordTrace (prefixWord ++ tailWord_2742801) baseStart_2742801 baseEnd_2742801 := by
    simpa [prefixWord, tailWord_2742801, baseEnd_2742801] using wordTrace_append hprefix tailTrace_2742801
  have hstable : (prefixWord ++ tailWord_2742801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742801).length < 2 ^ (prefixWord ++ tailWord_2742801).sum := by decide
  have hdescent : baseEnd_2742801 < baseStart_2742801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742807 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 1, 4]
def baseStart_2742807 : Nat := 118140960795 + 2742807 * 2 ^ 59
def prefixEnd_2742807 : Nat := 4983230072969 + 3 ^ 40 * 2742807 * 2
def baseEnd_2742807 : Nat := 938918889011036992465711

theorem tailTrace_2742807 : CollatzResearch.WordTrace tailWord_2742807 prefixEnd_2742807 938918889011036992465711 := by
  unfold tailWord_2742807
  simp only [CollatzResearch.WordTrace]
  refine ⟨100038389774286147986762675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66692259849524098657841783 100038389774286147986762675)
  ·
    refine ⟨150057584661429221980144013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100038389774286147986762675 150057584661429221980144013)
    ·
      refine ⟨56271594248035958242554005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150057584661429221980144013 56271594248035958242554005)
      ·
        refine ⟨2637730980376685542619719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56271594248035958242554005 2637730980376685542619719)
        ·
          refine ⟨3956596470565028313929579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637730980376685542619719 3956596470565028313929579)
          ·
            refine ⟨5934894705847542470894369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956596470565028313929579 5934894705847542470894369)
            ·
              refine ⟨4451171029385656853170777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5934894705847542470894369 4451171029385656853170777)
              ·
                refine ⟨3338378272039242639878083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4451171029385656853170777 3338378272039242639878083)
                ·
                  refine ⟨5007567408058863959817125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338378272039242639878083 5007567408058863959817125)
                  ·
                    refine ⟨938918889011036992465711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5007567408058863959817125 938918889011036992465711)
                    ·
                      rfl

theorem cell22_2742807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_2742807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742807 prefixEnd_2742807 := by exact prefixLift 2742807
  have htrace : WordTrace (prefixWord ++ tailWord_2742807) baseStart_2742807 baseEnd_2742807 := by
    simpa [prefixWord, tailWord_2742807, baseEnd_2742807] using wordTrace_append hprefix tailTrace_2742807
  have hstable : (prefixWord ++ tailWord_2742807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742807).length < 2 ^ (prefixWord ++ tailWord_2742807).sum := by decide
  have hdescent : baseEnd_2742807 < baseStart_2742807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742818 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2742818 : Nat := 118140960795 + 2742818 * 2 ^ 59
def prefixEnd_2742818 : Nat := 4983230072969 + 3 ^ 40 * 2742818 * 2
def baseEnd_2742818 : Nat := 938922654535836630440677

theorem tailTrace_2742818 : CollatzResearch.WordTrace tailWord_2742818 prefixEnd_2742818 938922654535836630440677 := by
  unfold tailWord_2742818
  simp only [CollatzResearch.WordTrace]
  refine ⟨25009697744311574216353277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66692527318164197910275405 25009697744311574216353277)
  ·
    refine ⟨9378636654116840331132479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25009697744311574216353277 9378636654116840331132479)
    ·
      refine ⟨14067954981175260496698719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9378636654116840331132479 14067954981175260496698719)
      ·
        refine ⟨21101932471762890745048079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14067954981175260496698719 21101932471762890745048079)
        ·
          refine ⟨31652898707644336117572119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21101932471762890745048079 31652898707644336117572119)
          ·
            refine ⟨47479348061466504176358179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31652898707644336117572119 47479348061466504176358179)
            ·
              refine ⟨71219022092199756264537269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47479348061466504176358179 71219022092199756264537269)
              ·
                refine ⟨6676783321143727149800369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71219022092199756264537269 6676783321143727149800369)
                ·
                  refine ⟨5007587490857795362350277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6676783321143727149800369 5007587490857795362350277)
                  ·
                    refine ⟨938922654535836630440677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5007587490857795362350277 938922654535836630440677)
                    ·
                      rfl

theorem cell22_2742818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2742818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742818 prefixEnd_2742818 := by exact prefixLift 2742818
  have htrace : WordTrace (prefixWord ++ tailWord_2742818) baseStart_2742818 baseEnd_2742818 := by
    simpa [prefixWord, tailWord_2742818, baseEnd_2742818] using wordTrace_append hprefix tailTrace_2742818
  have hstable : (prefixWord ++ tailWord_2742818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742818).length < 2 ^ (prefixWord ++ tailWord_2742818).sum := by decide
  have hdescent : baseEnd_2742818 < baseStart_2742818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742854 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_2742854 : Nat := 118140960795 + 2742854 * 2 ^ 59
def prefixEnd_2742854 : Nat := 4983230072969 + 3 ^ 40 * 2742854 * 2
def baseEnd_2742854 : Nat := 938934978071544536540567

theorem tailTrace_2742854 : CollatzResearch.WordTrace tailWord_2742854 prefixEnd_2742854 938934978071544536540567 := by
  unfold tailWord_2742854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3126253250159871094178863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66693402670077250009149077 3126253250159871094178863)
  ·
    refine ⟨4689379875239806641268295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3126253250159871094178863 4689379875239806641268295)
    ·
      refine ⟨7034069812859709961902443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4689379875239806641268295 7034069812859709961902443)
      ·
        refine ⟨10551104719289564942853665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7034069812859709961902443 10551104719289564942853665)
        ·
          refine ⟨7913328539467173707140249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10551104719289564942853665 7913328539467173707140249)
          ·
            refine ⟨5934996404600380280355187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7913328539467173707140249 5934996404600380280355187)
            ·
              refine ⟨8902494606900570420532781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5934996404600380280355187 8902494606900570420532781)
              ·
                refine ⟨3338435477587713907699793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8902494606900570420532781 3338435477587713907699793)
                ·
                  refine ⟨2503826608190785430774845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3338435477587713907699793 2503826608190785430774845)
                  ·
                    refine ⟨938934978071544536540567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2503826608190785430774845 938934978071544536540567)
                    ·
                      rfl

theorem cell22_2742854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_2742854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742854 prefixEnd_2742854 := by exact prefixLift 2742854
  have htrace : WordTrace (prefixWord ++ tailWord_2742854) baseStart_2742854 baseEnd_2742854 := by
    simpa [prefixWord, tailWord_2742854, baseEnd_2742854] using wordTrace_append hprefix tailTrace_2742854
  have hstable : (prefixWord ++ tailWord_2742854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742854).length < 2 ^ (prefixWord ++ tailWord_2742854).sum := by decide
  have hdescent : baseEnd_2742854 < baseStart_2742854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742908 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_2742908 : Nat := 118140960795 + 2742908 * 2 ^ 59
def prefixEnd_2742908 : Nat := 4983230072969 + 3 ^ 40 * 2742908 * 2
def baseEnd_2742908 : Nat := 938953463375106395690401

theorem tailTrace_2742908 : CollatzResearch.WordTrace tailWord_2742908 prefixEnd_2742908 938953463375106395690401 := by
  unfold tailWord_2742908
  simp only [CollatzResearch.WordTrace]
  refine ⟨50021036773460121118094689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66694715697946828157459585 50021036773460121118094689)
  ·
    refine ⟨37515777580095090838571017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50021036773460121118094689 37515777580095090838571017)
    ·
      refine ⟨28136833185071318128928263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37515777580095090838571017 28136833185071318128928263)
      ·
        refine ⟨42205249777606977193392395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28136833185071318128928263 42205249777606977193392395)
        ·
          refine ⟨63307874666410465790088593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42205249777606977193392395 63307874666410465790088593)
          ·
            refine ⟨47480905999807849342566445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63307874666410465790088593 47480905999807849342566445)
            ·
              refine ⟨17805339749927943503462417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47480905999807849342566445 17805339749927943503462417)
              ·
                refine ⟨13354004812445957627596813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17805339749927943503462417 13354004812445957627596813)
                ·
                  refine ⟨5007751804667234110348805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13354004812445957627596813 5007751804667234110348805)
                  ·
                    refine ⟨938953463375106395690401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5007751804667234110348805 938953463375106395690401)
                    ·
                      rfl

theorem cell22_2742908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_2742908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742908 prefixEnd_2742908 := by exact prefixLift 2742908
  have htrace : WordTrace (prefixWord ++ tailWord_2742908) baseStart_2742908 baseEnd_2742908 := by
    simpa [prefixWord, tailWord_2742908, baseEnd_2742908] using wordTrace_append hprefix tailTrace_2742908
  have hstable : (prefixWord ++ tailWord_2742908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742908).length < 2 ^ (prefixWord ++ tailWord_2742908).sum := by decide
  have hdescent : baseEnd_2742908 < baseStart_2742908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742942 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2742942 : Nat := 118140960795 + 2742942 * 2 ^ 59
def prefixEnd_2742942 : Nat := 4983230072969 + 3 ^ 40 * 2742942 * 2
def baseEnd_2742942 : Nat := 938965102269941640340297

theorem tailTrace_2742942 : CollatzResearch.WordTrace tailWord_2742942 prefixEnd_2742942 938965102269941640340297 := by
  unfold tailWord_2742942
  simp only [CollatzResearch.WordTrace]
  refine ⟨12505414203599633255365885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66695542419198044028618053 12505414203599633255365885)
  ·
    refine ⟨4689530326349862470762207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12505414203599633255365885 4689530326349862470762207)
    ·
      refine ⟨7034295489524793706143311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4689530326349862470762207 7034295489524793706143311)
      ·
        refine ⟨10551443234287190559214967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7034295489524793706143311 10551443234287190559214967)
        ·
          refine ⟨15827164851430785838822451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10551443234287190559214967 15827164851430785838822451)
          ·
            refine ⟨23740747277146178758233677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15827164851430785838822451 23740747277146178758233677)
            ·
              refine ⟨8902780228929817034337629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23740747277146178758233677 8902780228929817034337629)
              ·
                refine ⟨3338542585848681387876611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8902780228929817034337629 3338542585848681387876611)
                ·
                  refine ⟨5007813878773022081814917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338542585848681387876611 5007813878773022081814917)
                  ·
                    refine ⟨938965102269941640340297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5007813878773022081814917 938965102269941640340297)
                    ·
                      rfl

theorem cell22_2742942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2742942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742942 prefixEnd_2742942 := by exact prefixLift 2742942
  have htrace : WordTrace (prefixWord ++ tailWord_2742942) baseStart_2742942 baseEnd_2742942 := by
    simpa [prefixWord, tailWord_2742942, baseEnd_2742942] using wordTrace_append hprefix tailTrace_2742942
  have hstable : (prefixWord ++ tailWord_2742942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742942).length < 2 ^ (prefixWord ++ tailWord_2742942).sum := by decide
  have hdescent : baseEnd_2742942 < baseStart_2742942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2742957 : List Nat := [1, 5, 2, 1, 1, 2, 2, 4, 4]
def baseStart_2742957 : Nat := 118140960795 + 2742957 * 2 ^ 59
def prefixEnd_2742957 : Nat := 4983230072969 + 3 ^ 40 * 2742957 * 2
def baseEnd_2742957 : Nat := 312990079025495533738417

theorem tailTrace_2742957 : CollatzResearch.WordTrace tailWord_2742957 prefixEnd_2742957 312990079025495533738417 := by
  unfold tailWord_2742957
  simp only [CollatzResearch.WordTrace]
  refine ⟨100043860723742723604723125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66695907149161815736482083 100043860723742723604723125)
  ·
    refine ⟨9379111942850880337942793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100043860723742723604723125 9379111942850880337942793)
    ·
      refine ⟨7034333957138160253457095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9379111942850880337942793 7034333957138160253457095)
      ·
        refine ⟨10551500935707240380185643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7034333957138160253457095 10551500935707240380185643)
        ·
          refine ⟨15827251403560860570278465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10551500935707240380185643 15827251403560860570278465)
          ·
            refine ⟨11870438552670645427708849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15827251403560860570278465 11870438552670645427708849)
            ·
              refine ⟨8902828914502984070781637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11870438552670645427708849 8902828914502984070781637)
              ·
                refine ⟨1669280421469309513271557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8902828914502984070781637 1669280421469309513271557)
                ·
                  refine ⟨312990079025495533738417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669280421469309513271557 312990079025495533738417)
                  ·
                    rfl

theorem cell22_2742957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_2742957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2742957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2742957 prefixEnd_2742957 := by exact prefixLift 2742957
  have htrace : WordTrace (prefixWord ++ tailWord_2742957) baseStart_2742957 baseEnd_2742957 := by
    simpa [prefixWord, tailWord_2742957, baseEnd_2742957] using wordTrace_append hprefix tailTrace_2742957
  have hstable : (prefixWord ++ tailWord_2742957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2742957).length < 2 ^ (prefixWord ++ tailWord_2742957).sum := by decide
  have hdescent : baseEnd_2742957 < baseStart_2742957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2742957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743017 : List Nat := [1, 2, 1, 1, 1, 2, 4, 6, 1, 3]
def baseStart_2743017 : Nat := 118140960795 + 2743017 * 2 ^ 59
def prefixEnd_2743017 : Nat := 4983230072969 + 3 ^ 40 * 2743017 * 2
def baseEnd_2743017 : Nat := 938990776302666444715067

theorem tailTrace_2743017 : CollatzResearch.WordTrace tailWord_2743017 prefixEnd_2743017 938990776302666444715067 := by
  unfold tailWord_2743017
  simp only [CollatzResearch.WordTrace]
  refine ⟨100046049103525353851907305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66697366069016902567938203 100046049103525353851907305)
  ·
    refine ⟨75034536827644015388930479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100046049103525353851907305 75034536827644015388930479)
    ·
      refine ⟨112551805241466023083395719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75034536827644015388930479 112551805241466023083395719)
      ·
        refine ⟨168827707862199034625093579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112551805241466023083395719 168827707862199034625093579)
        ·
          refine ⟨253241561793298551937640369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168827707862199034625093579 253241561793298551937640369)
          ·
            refine ⟨189931171344973913953230277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253241561793298551937640369 189931171344973913953230277)
            ·
              refine ⟨35612094627182608866230677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189931171344973913953230277 35612094627182608866230677)
              ·
                refine ⟨1669316935649184790604563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35612094627182608866230677 1669316935649184790604563)
                ·
                  refine ⟨2503975403473777185906845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669316935649184790604563 2503975403473777185906845)
                  ·
                    refine ⟨938990776302666444715067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2503975403473777185906845 938990776302666444715067)
                    ·
                      rfl

theorem cell22_2743017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 1, 3].length) (baseStart_2743017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743017 prefixEnd_2743017 := by exact prefixLift 2743017
  have htrace : WordTrace (prefixWord ++ tailWord_2743017) baseStart_2743017 baseEnd_2743017 := by
    simpa [prefixWord, tailWord_2743017, baseEnd_2743017] using wordTrace_append hprefix tailTrace_2743017
  have hstable : (prefixWord ++ tailWord_2743017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743017).length < 2 ^ (prefixWord ++ tailWord_2743017).sum := by decide
  have hdescent : baseEnd_2743017 < baseStart_2743017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743124 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_2743124 : Nat := 118140960795 + 2743124 * 2 ^ 59
def prefixEnd_2743124 : Nat := 4983230072969 + 3 ^ 40 * 2743124 * 2
def baseEnd_2743124 : Nat := 939027404589353832289739

theorem tailTrace_2743124 : CollatzResearch.WordTrace tailWord_2743124 prefixEnd_2743124 939027404589353832289739 := by
  unfold tailWord_2743124
  simp only [CollatzResearch.WordTrace]
  refine ⟨50024975857068855563026213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66699967809425140750701617 50024975857068855563026213)
  ·
    refine ⟨9379682973200410418067415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50024975857068855563026213 9379682973200410418067415)
    ·
      refine ⟨14069524459800615627101123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9379682973200410418067415 14069524459800615627101123)
      ·
        refine ⟨21104286689700923440651685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14069524459800615627101123 21104286689700923440651685)
        ·
          refine ⟨3957053754318923145122191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21104286689700923440651685 3957053754318923145122191)
          ·
            refine ⟨5935580631478384717683287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3957053754318923145122191 5935580631478384717683287)
            ·
              refine ⟨8903370947217577076524931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5935580631478384717683287 8903370947217577076524931)
              ·
                refine ⟨13355056420826365614787397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8903370947217577076524931 13355056420826365614787397)
                ·
                  refine ⟨2504073078904943552772637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13355056420826365614787397 2504073078904943552772637)
                  ·
                    refine ⟨939027404589353832289739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504073078904943552772637 939027404589353832289739)
                    ·
                      rfl

theorem cell22_2743124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_2743124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743124 prefixEnd_2743124 := by exact prefixLift 2743124
  have htrace : WordTrace (prefixWord ++ tailWord_2743124) baseStart_2743124 baseEnd_2743124 := by
    simpa [prefixWord, tailWord_2743124, baseEnd_2743124] using wordTrace_append hprefix tailTrace_2743124
  have hstable : (prefixWord ++ tailWord_2743124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743124).length < 2 ^ (prefixWord ++ tailWord_2743124).sum := by decide
  have hdescent : baseEnd_2743124 < baseStart_2743124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743152 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 3, 3]
def baseStart_2743152 : Nat := 118140960795 + 2743152 * 2 ^ 59
def prefixEnd_2743152 : Nat := 4983230072969 + 3 ^ 40 * 2743152 * 2
def baseEnd_2743152 : Nat := 939036989561571092589653

theorem tailTrace_2743152 : CollatzResearch.WordTrace tailWord_2743152 prefixEnd_2743152 939036989561571092589653 := by
  unfold tailWord_2743152
  simp only [CollatzResearch.WordTrace]
  refine ⟨50025486479018135954035855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66700648638690847938714473 50025486479018135954035855)
  ·
    refine ⟨75038229718527203931053783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50025486479018135954035855 75038229718527203931053783)
    ·
      refine ⟨112557344577790805896580675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75038229718527203931053783 112557344577790805896580675)
      ·
        refine ⟨168836016866686208844871013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112557344577790805896580675 168836016866686208844871013)
        ·
          refine ⟨31656753162503664158413315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168836016866686208844871013 31656753162503664158413315)
          ·
            refine ⟨47485129743755496237619973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31656753162503664158413315 47485129743755496237619973)
            ·
              refine ⟨8903461826954155544553745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47485129743755496237619973 8903461826954155544553745)
              ·
                refine ⟨6677596370215616658415309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8903461826954155544553745 6677596370215616658415309)
                ·
                  refine ⟨2504098638830856246905741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6677596370215616658415309 2504098638830856246905741)
                  ·
                    refine ⟨939036989561571092589653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504098638830856246905741 939036989561571092589653)
                    ·
                      rfl

theorem cell22_2743152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3, 3].length) (baseStart_2743152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743152 prefixEnd_2743152 := by exact prefixLift 2743152
  have htrace : WordTrace (prefixWord ++ tailWord_2743152) baseStart_2743152 baseEnd_2743152 := by
    simpa [prefixWord, tailWord_2743152, baseEnd_2743152] using wordTrace_append hprefix tailTrace_2743152
  have hstable : (prefixWord ++ tailWord_2743152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743152).length < 2 ^ (prefixWord ++ tailWord_2743152).sum := by decide
  have hdescent : baseEnd_2743152 < baseStart_2743152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743165 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 7]
def baseStart_2743165 : Nat := 118140960795 + 2743165 * 2 ^ 59
def prefixEnd_2743165 : Nat := 4983230072969 + 3 ^ 40 * 2743165 * 2
def baseEnd_2743165 : Nat := 313013813242414464004871

theorem tailTrace_2743165 : CollatzResearch.WordTrace tailWord_2743165 prefixEnd_2743165 313013813242414464004871 := by
  unfold tailWord_2743165
  simp only [CollatzResearch.WordTrace]
  refine ⟨100051447106989175128294949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66700964737992783418863299 100051447106989175128294949)
  ·
    refine ⟨18759646332560470336555303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100051447106989175128294949 18759646332560470336555303)
    ·
      refine ⟨28139469498840705504832955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18759646332560470336555303 28139469498840705504832955)
      ·
        refine ⟨42209204248261058257249433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28139469498840705504832955 42209204248261058257249433)
        ·
          refine ⟨31656903186195793692937075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42209204248261058257249433 31656903186195793692937075)
          ·
            refine ⟨47485354779293690539405613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31656903186195793692937075 47485354779293690539405613)
            ·
              refine ⟨17807008042235133952277105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47485354779293690539405613 17807008042235133952277105)
              ·
                refine ⟨13355256031676350464207829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17807008042235133952277105 13355256031676350464207829)
                ·
                  refine ⟨313013813242414464004871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13355256031676350464207829 313013813242414464004871)
                  ·
                    rfl

theorem cell22_2743165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_2743165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743165 prefixEnd_2743165 := by exact prefixLift 2743165
  have htrace : WordTrace (prefixWord ++ tailWord_2743165) baseStart_2743165 baseEnd_2743165 := by
    simpa [prefixWord, tailWord_2743165, baseEnd_2743165] using wordTrace_append hprefix tailTrace_2743165
  have hstable : (prefixWord ++ tailWord_2743165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743165).length < 2 ^ (prefixWord ++ tailWord_2743165).sum := by decide
  have hdescent : baseEnd_2743165 < baseStart_2743165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743180 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_2743180 : Nat := 118140960795 + 2743180 * 2 ^ 59
def prefixEnd_2743180 : Nat := 4983230072969 + 3 ^ 40 * 2743180 * 2
def baseEnd_2743180 : Nat := 939046574533788352889567

theorem tailTrace_2743180 : CollatzResearch.WordTrace tailWord_2743180 prefixEnd_2743180 939046574533788352889567 := by
  unfold tailWord_2743180
  simp only [CollatzResearch.WordTrace]
  refine ⟨50025997100967416345045497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66701329467956555126727329 50025997100967416345045497)
  ·
    refine ⟨37519497825725562258784123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50025997100967416345045497 37519497825725562258784123)
    ·
      refine ⟨56279246738588343388176185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37519497825725562258784123 56279246738588343388176185)
      ·
        refine ⟨42209435053941257541132139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56279246738588343388176185 42209435053941257541132139)
        ·
          refine ⟨63314152580911886311698209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42209435053941257541132139 63314152580911886311698209)
          ·
            refine ⟨47485614435683914733773657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63314152580911886311698209 47485614435683914733773657)
            ·
              refine ⟨35614210826762936050330243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47485614435683914733773657 35614210826762936050330243)
              ·
                refine ⟨53421316240144404075495365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35614210826762936050330243 53421316240144404075495365)
                ·
                  refine ⟨10016496795027075764155381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53421316240144404075495365 10016496795027075764155381)
                  ·
                    refine ⟨939046574533788352889567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10016496795027075764155381 939046574533788352889567)
                    ·
                      rfl

theorem cell22_2743180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_2743180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743180 prefixEnd_2743180 := by exact prefixLift 2743180
  have htrace : WordTrace (prefixWord ++ tailWord_2743180) baseStart_2743180 baseEnd_2743180 := by
    simpa [prefixWord, tailWord_2743180, baseEnd_2743180] using wordTrace_append hprefix tailTrace_2743180
  have hstable : (prefixWord ++ tailWord_2743180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743180).length < 2 ^ (prefixWord ++ tailWord_2743180).sum := by decide
  have hdescent : baseEnd_2743180 < baseStart_2743180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743199 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 5]
def baseStart_2743199 : Nat := 118140960795 + 2743199 * 2 ^ 59
def prefixEnd_2743199 : Nat := 4983230072969 + 3 ^ 40 * 2743199 * 2
def baseEnd_2743199 : Nat := 313017692874026212221503

theorem tailTrace_2743199 : CollatzResearch.WordTrace tailWord_2743199 prefixEnd_2743199 313017692874026212221503 := by
  unfold tailWord_2743199
  simp only [CollatzResearch.WordTrace]
  refine ⟨100052687188865998935032651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66701791459243999290021767 100052687188865998935032651)
  ·
    refine ⟨150079030783298998402548977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100052687188865998935032651 150079030783298998402548977)
    ·
      refine ⟨112559273087474248801911733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150079030783298998402548977 112559273087474248801911733)
      ·
        refine ⟨10552431851950710825179225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112559273087474248801911733 10552431851950710825179225)
        ·
          refine ⟨7914323888963033118884419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10552431851950710825179225 7914323888963033118884419)
          ·
            refine ⟨11871485833444549678326629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914323888963033118884419 11871485833444549678326629)
            ·
              refine ⟨2225903593770853064686243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11871485833444549678326629 2225903593770853064686243)
              ·
                refine ⟨3338855390656279597029365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2225903593770853064686243 3338855390656279597029365)
                ·
                  refine ⟨313017692874026212221503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3338855390656279597029365 313017692874026212221503)
                  ·
                    rfl

theorem cell22_2743199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 5].length) (baseStart_2743199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743199 prefixEnd_2743199 := by exact prefixLift 2743199
  have htrace : WordTrace (prefixWord ++ tailWord_2743199) baseStart_2743199 baseEnd_2743199 := by
    simpa [prefixWord, tailWord_2743199, baseEnd_2743199] using wordTrace_append hprefix tailTrace_2743199
  have hstable : (prefixWord ++ tailWord_2743199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743199).length < 2 ^ (prefixWord ++ tailWord_2743199).sum := by decide
  have hdescent : baseEnd_2743199 < baseStart_2743199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743244 : List Nat := [2, 2, 1, 4, 1, 1, 3, 4, 4]
def baseStart_2743244 : Nat := 118140960795 + 2743244 * 2 ^ 59
def prefixEnd_2743244 : Nat := 4983230072969 + 3 ^ 40 * 2743244 * 2
def baseEnd_2743244 : Nat := 313022827680571173096457

theorem tailTrace_2743244 : CollatzResearch.WordTrace tailWord_2743244 prefixEnd_2743244 313022827680571173096457 := by
  unfold tailWord_2743244
  simp only [CollatzResearch.WordTrace]
  refine ⟨50027164236851485810210393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66702885649135314413613857 50027164236851485810210393)
  ·
    refine ⟨37520373177638614357657795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50027164236851485810210393 37520373177638614357657795)
    ·
      refine ⟨56280559766457921536486693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37520373177638614357657795 56280559766457921536486693)
      ·
        refine ⟨10552604956210860288091255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56280559766457921536486693 10552604956210860288091255)
        ·
          refine ⟨15828907434316290432136883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10552604956210860288091255 15828907434316290432136883)
          ·
            refine ⟨23743361151474435648205325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15828907434316290432136883 23743361151474435648205325)
            ·
              refine ⟨8903760431802913368076997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23743361151474435648205325 8903760431802913368076997)
              ·
                refine ⟨1669455080963046256514437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8903760431802913368076997 1669455080963046256514437)
                ·
                  refine ⟨313022827680571173096457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669455080963046256514437 313022827680571173096457)
                  ·
                    rfl

theorem cell22_2743244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_2743244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743244 prefixEnd_2743244 := by exact prefixLift 2743244
  have htrace : WordTrace (prefixWord ++ tailWord_2743244) baseStart_2743244 baseEnd_2743244 := by
    simpa [prefixWord, tailWord_2743244, baseEnd_2743244] using wordTrace_append hprefix tailTrace_2743244
  have hstable : (prefixWord ++ tailWord_2743244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743244).length < 2 ^ (prefixWord ++ tailWord_2743244).sum := by decide
  have hdescent : baseEnd_2743244 < baseStart_2743244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743255 : List Nat := [1, 1, 3, 2, 1, 1, 2, 11]
def baseStart_2743255 : Nat := 118140960795 + 2743255 * 2 ^ 59
def prefixEnd_2743255 : Nat := 4983230072969 + 3 ^ 40 * 2743255 * 2
def baseEnd_2743255 : Nat := 104341360951834795251593

theorem tailTrace_2743255 : CollatzResearch.WordTrace tailWord_2743255 prefixEnd_2743255 104341360951834795251593 := by
  unfold tailWord_2743255
  simp only [CollatzResearch.WordTrace]
  refine ⟨100054729676663120499071219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66703153117775413666047479 100054729676663120499071219)
  ·
    refine ⟨150082094514994680748606829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100054729676663120499071219 150082094514994680748606829)
    ·
      refine ⟨56280785443123005280727561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150082094514994680748606829 56280785443123005280727561)
      ·
        refine ⟨42210589082342253960545671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56280785443123005280727561 42210589082342253960545671)
        ·
          refine ⟨63315883623513380940818507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42210589082342253960545671 63315883623513380940818507)
          ·
            refine ⟨94973825435270071411227761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63315883623513380940818507 94973825435270071411227761)
            ·
              refine ⟨71230369076452553558420821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94973825435270071411227761 71230369076452553558420821)
              ·
                refine ⟨104341360951834795251593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 71230369076452553558420821 104341360951834795251593)
                ·
                  rfl

theorem cell22_2743255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 11].length) (baseStart_2743255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743255 prefixEnd_2743255 := by exact prefixLift 2743255
  have htrace : WordTrace (prefixWord ++ tailWord_2743255) baseStart_2743255 baseEnd_2743255 := by
    simpa [prefixWord, tailWord_2743255, baseEnd_2743255] using wordTrace_append hprefix tailTrace_2743255
  have hstable : (prefixWord ++ tailWord_2743255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743255).length < 2 ^ (prefixWord ++ tailWord_2743255).sum := by decide
  have hdescent : baseEnd_2743255 < baseStart_2743255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743274 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_2743274 : Nat := 118140960795 + 2743274 * 2 ^ 59
def prefixEnd_2743274 : Nat := 4983230072969 + 3 ^ 40 * 2743274 * 2
def baseEnd_2743274 : Nat := 939078752654803441039279

theorem tailTrace_2743274 : CollatzResearch.WordTrace tailWord_2743274 prefixEnd_2743274 939078752654803441039279 := by
  unfold tailWord_2743274
  simp only [CollatzResearch.WordTrace]
  refine ⟨25013855665898571686003219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66703615109062857829341917 25013855665898571686003219)
  ·
    refine ⟨37520783498847857529004829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25013855665898571686003219 37520783498847857529004829)
    ·
      refine ⟨14070293812067946573376811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37520783498847857529004829 14070293812067946573376811)
      ·
        refine ⟨21105440718101919860065217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14070293812067946573376811 21105440718101919860065217)
        ·
          refine ⟨15829080538576439895048913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21105440718101919860065217 15829080538576439895048913)
          ·
            refine ⟨11871810403932329921286685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15829080538576439895048913 11871810403932329921286685)
            ·
              refine ⟨4451928901474623720482507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11871810403932329921286685 4451928901474623720482507)
              ·
                refine ⟨6677893352211935580723761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4451928901474623720482507 6677893352211935580723761)
                ·
                  refine ⟨5008420014158951685542821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6677893352211935580723761 5008420014158951685542821)
                  ·
                    refine ⟨939078752654803441039279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5008420014158951685542821 939078752654803441039279)
                    ·
                      rfl

theorem cell22_2743274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_2743274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743274 prefixEnd_2743274 := by exact prefixLift 2743274
  have htrace : WordTrace (prefixWord ++ tailWord_2743274) baseStart_2743274 baseEnd_2743274 := by
    simpa [prefixWord, tailWord_2743274, baseEnd_2743274] using wordTrace_append hprefix tailTrace_2743274
  have hstable : (prefixWord ++ tailWord_2743274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743274).length < 2 ^ (prefixWord ++ tailWord_2743274).sum := by decide
  have hdescent : baseEnd_2743274 < baseStart_2743274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743304 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 3, 3]
def baseStart_2743304 : Nat := 118140960795 + 2743304 * 2 ^ 59
def prefixEnd_2743304 : Nat := 4983230072969 + 3 ^ 40 * 2743304 * 2
def baseEnd_2743304 : Nat := 939089022267893362789187

theorem tailTrace_2743304 : CollatzResearch.WordTrace tailWord_2743304 prefixEnd_2743304 939089022267893362789187 := by
  unfold tailWord_2743304
  simp only [CollatzResearch.WordTrace]
  refine ⟨50028258426742800933802483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66704344568990401245069977 50028258426742800933802483)
  ·
    refine ⟨75042387640114201400703725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50028258426742800933802483 75042387640114201400703725)
    ·
      refine ⟨28140895365042825525263897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75042387640114201400703725 28140895365042825525263897)
      ·
        refine ⟨21105671523782119143947923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28140895365042825525263897 21105671523782119143947923)
        ·
          refine ⟨31658507285673178715921885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21105671523782119143947923 31658507285673178715921885)
          ·
            refine ⟨11871940232127442018470707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31658507285673178715921885 11871940232127442018470707)
            ·
              refine ⟨17807910348191163027706061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11871940232127442018470707 17807910348191163027706061)
              ·
                refine ⟨6677966380571686135389773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17807910348191163027706061 6677966380571686135389773)
                ·
                  refine ⟨2504237392714382300771165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6677966380571686135389773 2504237392714382300771165)
                  ·
                    refine ⟨939089022267893362789187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504237392714382300771165 939089022267893362789187)
                    ·
                      rfl

theorem cell22_2743304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_2743304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743304 prefixEnd_2743304 := by exact prefixLift 2743304
  have htrace : WordTrace (prefixWord ++ tailWord_2743304) baseStart_2743304 baseEnd_2743304 := by
    simpa [prefixWord, tailWord_2743304, baseEnd_2743304] using wordTrace_append hprefix tailTrace_2743304
  have hstable : (prefixWord ++ tailWord_2743304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743304).length < 2 ^ (prefixWord ++ tailWord_2743304).sum := by decide
  have hdescent : baseEnd_2743304 < baseStart_2743304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743347 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 5, 4]
def baseStart_2743347 : Nat := 118140960795 + 2743347 * 2 ^ 59
def prefixEnd_2743347 : Nat := 4983230072969 + 3 ^ 40 * 2743347 * 2
def baseEnd_2743347 : Nat := 939103742046655583964055

theorem tailTrace_2743347 : CollatzResearch.WordTrace tailWord_2743347 prefixEnd_2743347 939103742046655583964055 := by
  unfold tailWord_2743347
  simp only [CollatzResearch.WordTrace]
  refine ⟨100058085192329820211420295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66705390128219880140946863 100058085192329820211420295)
  ·
    refine ⟨150087127788494730317130443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100058085192329820211420295 150087127788494730317130443)
    ·
      refine ⟨225130691682742095475695665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150087127788494730317130443 225130691682742095475695665)
      ·
        refine ⟨168848018762056571606771749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225130691682742095475695665 168848018762056571606771749)
        ·
          refine ⟨31659003517885607176269703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168848018762056571606771749 31659003517885607176269703)
          ·
            refine ⟨47488505276828410764404555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31659003517885607176269703 47488505276828410764404555)
            ·
              refine ⟨71232757915242616146606833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47488505276828410764404555 71232757915242616146606833)
              ·
                refine ⟨53424568436431962109955125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71232757915242616146606833 53424568436431962109955125)
                ·
                  refine ⟨5008553290915496447808293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53424568436431962109955125 5008553290915496447808293)
                  ·
                    refine ⟨939103742046655583964055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5008553290915496447808293 939103742046655583964055)
                    ·
                      rfl

theorem cell22_2743347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 4].length) (baseStart_2743347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743347 prefixEnd_2743347 := by exact prefixLift 2743347
  have htrace : WordTrace (prefixWord ++ tailWord_2743347) baseStart_2743347 baseEnd_2743347 := by
    simpa [prefixWord, tailWord_2743347, baseEnd_2743347] using wordTrace_append hprefix tailTrace_2743347
  have hstable : (prefixWord ++ tailWord_2743347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743347).length < 2 ^ (prefixWord ++ tailWord_2743347).sum := by decide
  have hdescent : baseEnd_2743347 < baseStart_2743347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743467 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 2, 11]
def baseStart_2743467 : Nat := 118140960795 + 2743467 * 2 ^ 59
def prefixEnd_2743467 : Nat := 4983230072969 + 3 ^ 40 * 2743467 * 2
def baseEnd_2743467 : Nat := 939144820499015270963687

theorem tailTrace_2743467 : CollatzResearch.WordTrace tailWord_2743467 prefixEnd_2743467 939144820499015270963687 := by
  unfold tailWord_2743467
  simp only [CollatzResearch.WordTrace]
  refine ⟨100062461951895080705788655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66708307967930053803859103 100062461951895080705788655)
  ·
    refine ⟨150093692927842621058682983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100062461951895080705788655 150093692927842621058682983)
    ·
      refine ⟨225140539391763931588024475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150093692927842621058682983 225140539391763931588024475)
      ·
        refine ⟨337710809087645897382036713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225140539391763931588024475 337710809087645897382036713)
        ·
          refine ⟨253283106815734423036527535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337710809087645897382036713 253283106815734423036527535)
          ·
            refine ⟨379924660223601634554791303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253283106815734423036527535 379924660223601634554791303)
            ·
              refine ⟨569886990335402451832186955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379924660223601634554791303 569886990335402451832186955)
              ·
                refine ⟨854830485503103677748280433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569886990335402451832186955 854830485503103677748280433)
                ·
                  refine ⟨641122864127327758311210325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 854830485503103677748280433 641122864127327758311210325)
                  ·
                    refine ⟨939144820499015270963687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 641122864127327758311210325 939144820499015270963687)
                    ·
                      rfl

theorem cell22_2743467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_2743467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743467 prefixEnd_2743467 := by exact prefixLift 2743467
  have htrace : WordTrace (prefixWord ++ tailWord_2743467) baseStart_2743467 baseEnd_2743467 := by
    simpa [prefixWord, tailWord_2743467, baseEnd_2743467] using wordTrace_append hprefix tailTrace_2743467
  have hstable : (prefixWord ++ tailWord_2743467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743467).length < 2 ^ (prefixWord ++ tailWord_2743467).sum := by decide
  have hdescent : baseEnd_2743467 < baseStart_2743467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743473 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 3, 3]
def baseStart_2743473 : Nat := 118140960795 + 2743473 * 2 ^ 59
def prefixEnd_2743473 : Nat := 4983230072969 + 3 ^ 40 * 2743473 * 2
def baseEnd_2743473 : Nat := 939146874421633255313669

theorem tailTrace_2743473 : CollatzResearch.WordTrace tailWord_2743473 prefixEnd_2743473 939146874421633255313669 := by
  unfold tailWord_2743473
  simp only [CollatzResearch.WordTrace]
  refine ⟨100062680789873343730507073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66708453859915562487004715 100062680789873343730507073)
  ·
    refine ⟨75047010592405007797880305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100062680789873343730507073 75047010592405007797880305)
    ·
      refine ⟨56285257944303755848410229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75047010592405007797880305 56285257944303755848410229)
      ·
        refine ⟨5276742932278477110788459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56285257944303755848410229 5276742932278477110788459)
        ·
          refine ⟨7915114398417715666182689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5276742932278477110788459 7915114398417715666182689)
          ·
            refine ⟨5936335798813286749637017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7915114398417715666182689 5936335798813286749637017)
            ·
              refine ⟨4452251849109965062227763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5936335798813286749637017 4452251849109965062227763)
              ·
                refine ⟨6678377773664947593341645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452251849109965062227763 6678377773664947593341645)
                ·
                  refine ⟨2504391665124355347503117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6678377773664947593341645 2504391665124355347503117)
                  ·
                    refine ⟨939146874421633255313669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504391665124355347503117 939146874421633255313669)
                    ·
                      rfl

theorem cell22_2743473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_2743473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743473 prefixEnd_2743473 := by exact prefixLift 2743473
  have htrace : WordTrace (prefixWord ++ tailWord_2743473) baseStart_2743473 baseEnd_2743473 := by
    simpa [prefixWord, tailWord_2743473, baseEnd_2743473] using wordTrace_append hprefix tailTrace_2743473
  have hstable : (prefixWord ++ tailWord_2743473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743473).length < 2 ^ (prefixWord ++ tailWord_2743473).sum := by decide
  have hdescent : baseEnd_2743473 < baseStart_2743473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743531 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 6]
def baseStart_2743531 : Nat := 118140960795 + 2743531 * 2 ^ 59
def prefixEnd_2743531 : Nat := 4983230072969 + 3 ^ 40 * 2743531 * 2
def baseEnd_2743531 : Nat := 313055576335646812454497

theorem tailTrace_2743531 : CollatzResearch.WordTrace tailWord_2743531 prefixEnd_2743531 313055576335646812454497 := by
  unfold tailWord_2743531
  simp only [CollatzResearch.WordTrace]
  refine ⟨100064796223663219636118447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66709864149108813090745631 100064796223663219636118447)
  ·
    refine ⟨150097194335494829454177671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100064796223663219636118447 150097194335494829454177671)
    ·
      refine ⟨225145791503242244181266507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150097194335494829454177671 225145791503242244181266507)
      ·
        refine ⟨337718687254863366271899761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225145791503242244181266507 337718687254863366271899761)
        ·
          refine ⟨253289015441147524703924821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337718687254863366271899761 253289015441147524703924821)
          ·
            refine ⟨2968230649700947555124119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 253289015441147524703924821 2968230649700947555124119)
            ·
              refine ⟨4452345974551421332686179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968230649700947555124119 4452345974551421332686179)
              ·
                refine ⟨6678518961827131999029269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452345974551421332686179 6678518961827131999029269)
                ·
                  refine ⟨313055576335646812454497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6678518961827131999029269 313055576335646812454497)
                  ·
                    rfl

theorem cell22_2743531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 6].length) (baseStart_2743531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743531 prefixEnd_2743531 := by exact prefixLift 2743531
  have htrace : WordTrace (prefixWord ++ tailWord_2743531) baseStart_2743531 baseEnd_2743531 := by
    simpa [prefixWord, tailWord_2743531, baseEnd_2743531] using wordTrace_append hprefix tailTrace_2743531
  have hstable : (prefixWord ++ tailWord_2743531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743531).length < 2 ^ (prefixWord ++ tailWord_2743531).sum := by decide
  have hdescent : baseEnd_2743531 < baseStart_2743531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743550 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2743550 : Nat := 118140960795 + 2743550 * 2 ^ 59
def prefixEnd_2743550 : Nat := 4983230072969 + 3 ^ 40 * 2743550 * 2
def baseEnd_2743550 : Nat := 939173233095230721138433

theorem tailTrace_2743550 : CollatzResearch.WordTrace tailWord_2743550 prefixEnd_2743550 939173233095230721138433 := by
  unfold tailWord_2743550
  simp only [CollatzResearch.WordTrace]
  refine ⟨12508186151324298235132513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66710326140396257254040069 12508186151324298235132513)
  ·
    refine ⟨9381139613493223676349385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12508186151324298235132513 9381139613493223676349385)
    ·
      refine ⟨7035854710119917757262039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9381139613493223676349385 7035854710119917757262039)
      ·
        refine ⟨10553782065179876635893059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7035854710119917757262039 10553782065179876635893059)
        ·
          refine ⟨15830673097769814953839589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10553782065179876635893059 15830673097769814953839589)
          ·
            refine ⟨2968251205831840303844923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15830673097769814953839589 2968251205831840303844923)
            ·
              refine ⟨4452376808747760455767385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968251205831840303844923 4452376808747760455767385)
              ·
                refine ⟨3339282606560820341825539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4452376808747760455767385 3339282606560820341825539)
                ·
                  refine ⟨5008923909841230512738309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339282606560820341825539 5008923909841230512738309)
                  ·
                    refine ⟨939173233095230721138433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5008923909841230512738309 939173233095230721138433)
                    ·
                      rfl

theorem cell22_2743550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2743550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743550 prefixEnd_2743550 := by exact prefixLift 2743550
  have htrace : WordTrace (prefixWord ++ tailWord_2743550) baseStart_2743550 baseEnd_2743550 := by
    simpa [prefixWord, tailWord_2743550, baseEnd_2743550] using wordTrace_append hprefix tailTrace_2743550
  have hstable : (prefixWord ++ tailWord_2743550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743550).length < 2 ^ (prefixWord ++ tailWord_2743550).sum := by decide
  have hdescent : baseEnd_2743550 < baseStart_2743550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743561 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 2, 4]
def baseStart_2743561 : Nat := 118140960795 + 2743561 * 2 ^ 59
def prefixEnd_2743561 : Nat := 4983230072969 + 3 ^ 40 * 2743561 * 2
def baseEnd_2743561 : Nat := 939176998620030359113399

theorem tailTrace_2743561 : CollatzResearch.WordTrace tailWord_2743561 prefixEnd_2743561 939176998620030359113399 := by
  unfold tailWord_2743561
  simp only [CollatzResearch.WordTrace]
  refine ⟨100065890413554534759710537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66710593609036356506473691 100065890413554534759710537)
  ·
    refine ⟨75049417810165901069782903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100065890413554534759710537 75049417810165901069782903)
    ·
      refine ⟨112574126715248851604674355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75049417810165901069782903 112574126715248851604674355)
      ·
        refine ⟨168861190072873277407011533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112574126715248851604674355 168861190072873277407011533)
        ·
          refine ⟨63322946277327479027629325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168861190072873277407011533 63322946277327479027629325)
          ·
            refine ⟨23746104853997804635360997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63322946277327479027629325 23746104853997804635360997)
            ·
              refine ⟨4452394660124588369130187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23746104853997804635360997 4452394660124588369130187)
              ·
                refine ⟨6678591990186882553695281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452394660124588369130187 6678591990186882553695281)
                ·
                  refine ⟨5008943992640161915271461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6678591990186882553695281 5008943992640161915271461)
                  ·
                    refine ⟨939176998620030359113399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5008943992640161915271461 939176998620030359113399)
                    ·
                      rfl

theorem cell22_2743561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_2743561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743561 prefixEnd_2743561 := by exact prefixLift 2743561
  have htrace : WordTrace (prefixWord ++ tailWord_2743561) baseStart_2743561 baseEnd_2743561 := by
    simpa [prefixWord, tailWord_2743561, baseEnd_2743561] using wordTrace_append hprefix tailTrace_2743561
  have hstable : (prefixWord ++ tailWord_2743561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743561).length < 2 ^ (prefixWord ++ tailWord_2743561).sum := by decide
  have hdescent : baseEnd_2743561 < baseStart_2743561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743582 : List Nat := [4, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2743582 : Nat := 118140960795 + 2743582 * 2 ^ 59
def prefixEnd_2743582 : Nat := 4983230072969 + 3 ^ 40 * 2743582 * 2
def baseEnd_2743582 : Nat := 313061395783064434779445

theorem tailTrace_2743582 : CollatzResearch.WordTrace tailWord_2743582 prefixEnd_2743582 313061395783064434779445 := by
  unfold tailWord_2743582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12508332043309806918278125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66711104230985636897483333 12508332043309806918278125)
  ·
    refine ⟨4690624516241177594354297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12508332043309806918278125 4690624516241177594354297)
    ·
      refine ⟨3517968387180883195765723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4690624516241177594354297 3517968387180883195765723)
      ·
        refine ⟨5276952580771324793648585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3517968387180883195765723 5276952580771324793648585)
        ·
          refine ⟨3957714435578493595236439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5276952580771324793648585 3957714435578493595236439)
          ·
            refine ⟨5936571653367740392854659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3957714435578493595236439 5936571653367740392854659)
            ·
              refine ⟨8904857480051610589281989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5936571653367740392854659 8904857480051610589281989)
              ·
                refine ⟨1669660777509676985490373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8904857480051610589281989 1669660777509676985490373)
                ·
                  refine ⟨313061395783064434779445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669660777509676985490373 313061395783064434779445)
                  ·
                    rfl

theorem cell22_2743582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2743582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743582 prefixEnd_2743582 := by exact prefixLift 2743582
  have htrace : WordTrace (prefixWord ++ tailWord_2743582) baseStart_2743582 baseEnd_2743582 := by
    simpa [prefixWord, tailWord_2743582, baseEnd_2743582] using wordTrace_append hprefix tailTrace_2743582
  have hstable : (prefixWord ++ tailWord_2743582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743582).length < 2 ^ (prefixWord ++ tailWord_2743582).sum := by decide
  have hdescent : baseEnd_2743582 < baseStart_2743582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743619 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 3, 7]
def baseStart_2743619 : Nat := 118140960795 + 2743619 * 2 ^ 59
def prefixEnd_2743619 : Nat := 4983230072969 + 3 ^ 40 * 2743619 * 2
def baseEnd_2743619 : Nat := 939196853205337541163221

theorem tailTrace_2743619 : CollatzResearch.WordTrace tailWord_2743619 prefixEnd_2743619 939196853205337541163221 := by
  unfold tailWord_2743619
  simp only [CollatzResearch.WordTrace]
  refine ⟨100068005847344410665321911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66712003898229607110214607 100068005847344410665321911)
  ·
    refine ⟨150102008771016615997982867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100068005847344410665321911 150102008771016615997982867)
    ·
      refine ⟨225153013156524923996974301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150102008771016615997982867 225153013156524923996974301)
      ·
        refine ⟨84432379933696846498865363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225153013156524923996974301 84432379933696846498865363)
        ·
          refine ⟨126648569900545269748298045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84432379933696846498865363 126648569900545269748298045)
          ·
            refine ⟨47493213712704476155611767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126648569900545269748298045 47493213712704476155611767)
            ·
              refine ⟨71239820569056714233417651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47493213712704476155611767 71239820569056714233417651)
              ·
                refine ⟨106859730853585071350126477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71239820569056714233417651 106859730853585071350126477)
                ·
                  refine ⟨40072399070094401756297429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106859730853585071350126477 40072399070094401756297429)
                  ·
                    refine ⟨939196853205337541163221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40072399070094401756297429 939196853205337541163221)
                    ·
                      rfl

theorem cell22_2743619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_2743619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743619 prefixEnd_2743619 := by exact prefixLift 2743619
  have htrace : WordTrace (prefixWord ++ tailWord_2743619) baseStart_2743619 baseEnd_2743619 := by
    simpa [prefixWord, tailWord_2743619, baseEnd_2743619] using wordTrace_append hprefix tailTrace_2743619
  have hstable : (prefixWord ++ tailWord_2743619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743619).length < 2 ^ (prefixWord ++ tailWord_2743619).sum := by decide
  have hdescent : baseEnd_2743619 < baseStart_2743619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743636 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_2743636 : Nat := 118140960795 + 2743636 * 2 ^ 59
def prefixEnd_2743636 : Nat := 4983230072969 + 3 ^ 40 * 2743636 * 2
def baseEnd_2743636 : Nat := 939202672652755163488169

theorem tailTrace_2743636 : CollatzResearch.WordTrace tailWord_2743636 prefixEnd_2743636 939202672652755163488169 := by
  unfold tailWord_2743636
  simp only [CollatzResearch.WordTrace]
  refine ⟨50034312944141411284345381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66712417258855215045793841 50034312944141411284345381)
  ·
    refine ⟨9381433677026514615814759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50034312944141411284345381 9381433677026514615814759)
    ·
      refine ⟨14072150515539771923722139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9381433677026514615814759 14072150515539771923722139)
      ·
        refine ⟨21108225773309657885583209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14072150515539771923722139 21108225773309657885583209)
        ·
          refine ⟨15831169329982243414187407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21108225773309657885583209 15831169329982243414187407)
          ·
            refine ⟨23746753994973365121281111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15831169329982243414187407 23746753994973365121281111)
            ·
              refine ⟨35620130992460047681921667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23746753994973365121281111 35620130992460047681921667)
              ·
                refine ⟨53430196488690071522882501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35620130992460047681921667 53430196488690071522882501)
                ·
                  refine ⟨10018161841629388410540469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53430196488690071522882501 10018161841629388410540469)
                  ·
                    refine ⟨939202672652755163488169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10018161841629388410540469 939202672652755163488169)
                    ·
                      rfl

theorem cell22_2743636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_2743636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743636 prefixEnd_2743636 := by exact prefixLift 2743636
  have htrace : WordTrace (prefixWord ++ tailWord_2743636) baseStart_2743636 baseEnd_2743636 := by
    simpa [prefixWord, tailWord_2743636, baseEnd_2743636] using wordTrace_append hprefix tailTrace_2743636
  have hstable : (prefixWord ++ tailWord_2743636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743636).length < 2 ^ (prefixWord ++ tailWord_2743636).sum := by decide
  have hdescent : baseEnd_2743636 < baseStart_2743636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743655 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 5]
def baseStart_2743655 : Nat := 118140960795 + 2743655 * 2 ^ 59
def prefixEnd_2743655 : Nat := 4983230072969 + 3 ^ 40 * 2743655 * 2
def baseEnd_2743655 : Nat := 313069725580348482421037

theorem tailTrace_2743655 : CollatzResearch.WordTrace tailWord_2743655 prefixEnd_2743655 313069725580348482421037 := by
  unfold tailWord_2743655
  simp only [CollatzResearch.WordTrace]
  refine ⟨100069318875213988813632419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66712879250142659209088279 100069318875213988813632419)
  ·
    refine ⟨150103978312820983220448629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100069318875213988813632419 150103978312820983220448629)
    ·
      refine ⟨14072247966826967176917059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150103978312820983220448629 14072247966826967176917059)
      ·
        refine ⟨21108371950240450765375589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14072247966826967176917059 21108371950240450765375589)
        ·
          refine ⟨3957819740670084518507923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21108371950240450765375589 3957819740670084518507923)
          ·
            refine ⟨5936729611005126777761885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3957819740670084518507923 5936729611005126777761885)
            ·
              refine ⟨2226273604126922541660707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5936729611005126777761885 2226273604126922541660707)
              ·
                refine ⟨3339410406190383812491061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226273604126922541660707 3339410406190383812491061)
                ·
                  refine ⟨313069725580348482421037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3339410406190383812491061 313069725580348482421037)
                  ·
                    rfl

theorem cell22_2743655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 5].length) (baseStart_2743655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743655 prefixEnd_2743655 := by exact prefixLift 2743655
  have htrace : WordTrace (prefixWord ++ tailWord_2743655) baseStart_2743655 baseEnd_2743655 := by
    simpa [prefixWord, tailWord_2743655, baseEnd_2743655] using wordTrace_append hprefix tailTrace_2743655
  have hstable : (prefixWord ++ tailWord_2743655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743655).length < 2 ^ (prefixWord ++ tailWord_2743655).sum := by decide
  have hdescent : baseEnd_2743655 < baseStart_2743655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743666 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_2743666 : Nat := 118140960795 + 2743666 * 2 ^ 59
def prefixEnd_2743666 : Nat := 4983230072969 + 3 ^ 40 * 2743666 * 2
def baseEnd_2743666 : Nat := 313070980755281695079359

theorem tailTrace_2743666 : CollatzResearch.WordTrace tailWord_2743666 prefixEnd_2743666 313070980755281695079359 := by
  unfold tailWord_2743666
  simp only [CollatzResearch.WordTrace]
  refine ⟨25017430019543534423070713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66713146718782758461521901 25017430019543534423070713)
  ·
    refine ⟨18763072514657650817303035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25017430019543534423070713 18763072514657650817303035)
    ·
      refine ⟨28144608771986476225954553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18763072514657650817303035 28144608771986476225954553)
      ·
        refine ⟨21108456578989857169465915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28144608771986476225954553 21108456578989857169465915)
        ·
          refine ⟨31662684868484785754198873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21108456578989857169465915 31662684868484785754198873)
          ·
            refine ⟨23747013651363589315649155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31662684868484785754198873 23747013651363589315649155)
            ·
              refine ⟨35620520477045383973473733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23747013651363589315649155 35620520477045383973473733)
              ·
                refine ⟨6678847589446009495026325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35620520477045383973473733 6678847589446009495026325)
                ·
                  refine ⟨313070980755281695079359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6678847589446009495026325 313070980755281695079359)
                  ·
                    rfl

theorem cell22_2743666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_2743666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743666 prefixEnd_2743666 := by exact prefixLift 2743666
  have htrace : WordTrace (prefixWord ++ tailWord_2743666) baseStart_2743666 baseEnd_2743666 := by
    simpa [prefixWord, tailWord_2743666, baseEnd_2743666] using wordTrace_append hprefix tailTrace_2743666
  have hstable : (prefixWord ++ tailWord_2743666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743666).length < 2 ^ (prefixWord ++ tailWord_2743666).sum := by decide
  have hdescent : baseEnd_2743666 < baseStart_2743666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743700 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 6]
def baseStart_2743700 : Nat := 118140960795 + 2743700 * 2 ^ 59
def prefixEnd_2743700 : Nat := 4983230072969 + 3 ^ 40 * 2743700 * 2
def baseEnd_2743700 : Nat := 313074860386893443295991

theorem tailTrace_2743700 : CollatzResearch.WordTrace tailWord_2743700 prefixEnd_2743700 313074860386893443295991 := by
  unfold tailWord_2743700
  simp only [CollatzResearch.WordTrace]
  refine ⟨50035480080025480749510277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66713973440033974332680369 50035480080025480749510277)
  ·
    refine ⟨9381652515004777640533177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50035480080025480749510277 9381652515004777640533177)
    ·
      refine ⟨7036239386253583230399883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9381652515004777640533177 7036239386253583230399883)
      ·
        refine ⟨10554359079380374845599825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7036239386253583230399883 10554359079380374845599825)
        ·
          refine ⟨7915769309535281134199869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10554359079380374845599825 7915769309535281134199869)
          ·
            refine ⟨2968413491075730425324951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7915769309535281134199869 2968413491075730425324951)
            ·
              refine ⟨4452620236613595637987427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968413491075730425324951 4452620236613595637987427)
              ·
                refine ⟨6678930354920393456981141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452620236613595637987427 6678930354920393456981141)
                ·
                  refine ⟨313074860386893443295991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6678930354920393456981141 313074860386893443295991)
                  ·
                    rfl

theorem cell22_2743700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_2743700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743700 prefixEnd_2743700 := by exact prefixLift 2743700
  have htrace : WordTrace (prefixWord ++ tailWord_2743700) baseStart_2743700 baseEnd_2743700 := by
    simpa [prefixWord, tailWord_2743700, baseEnd_2743700] using wordTrace_append hprefix tailTrace_2743700
  have hstable : (prefixWord ++ tailWord_2743700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743700).length < 2 ^ (prefixWord ++ tailWord_2743700).sum := by decide
  have hdescent : baseEnd_2743700 < baseStart_2743700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743711 : List Nat := [1, 1, 2, 5, 1, 2, 1, 9]
def baseStart_2743711 : Nat := 118140960795 + 2743711 * 2 ^ 59
def prefixEnd_2743711 : Nat := 4983230072969 + 3 ^ 40 * 2743711 * 2
def baseEnd_2743711 : Nat := 104358705187275551984771

theorem tailTrace_2743711 : CollatzResearch.WordTrace tailWord_2743711 prefixEnd_2743711 104358705187275551984771 := by
  unfold tailWord_2743711
  simp only [CollatzResearch.WordTrace]
  refine ⟨100071361363011110377670987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66714240908674073585113991 100071361363011110377670987)
  ·
    refine ⟨150107042044516665566506481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100071361363011110377670987 150107042044516665566506481)
    ·
      refine ⟨112580281533387499174879861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150107042044516665566506481 112580281533387499174879861)
      ·
        refine ⟨10554401393755078047644987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112580281533387499174879861 10554401393755078047644987)
        ·
          refine ⟨15831602090632617071467481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10554401393755078047644987 15831602090632617071467481)
          ·
            refine ⟨11873701567974462803600611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15831602090632617071467481 11873701567974462803600611)
            ·
              refine ⟨17810552351961694205400917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11873701567974462803600611 17810552351961694205400917)
              ·
                refine ⟨104358705187275551984771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17810552351961694205400917 104358705187275551984771)
                ·
                  rfl

theorem cell22_2743711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 9].length) (baseStart_2743711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743711 prefixEnd_2743711 := by exact prefixLift 2743711
  have htrace : WordTrace (prefixWord ++ tailWord_2743711) baseStart_2743711 baseEnd_2743711 := by
    simpa [prefixWord, tailWord_2743711, baseEnd_2743711] using wordTrace_append hprefix tailTrace_2743711
  have hstable : (prefixWord ++ tailWord_2743711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743711).length < 2 ^ (prefixWord ++ tailWord_2743711).sum := by decide
  have hdescent : baseEnd_2743711 < baseStart_2743711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743760 : List Nat := [2, 1, 1, 1, 1, 2, 2, 8, 1, 3]
def baseStart_2743760 : Nat := 118140960795 + 2743760 * 2 ^ 59
def prefixEnd_2743760 : Nat := 4983230072969 + 3 ^ 40 * 2743760 * 2
def baseEnd_2743760 : Nat := 939245120386860173387789

theorem tailTrace_2743760 : CollatzResearch.WordTrace tailWord_2743760 prefixEnd_2743760 939245120386860173387789 := by
  unfold tailWord_2743760
  simp only [CollatzResearch.WordTrace]
  refine ⟨50036574269916795873102367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66715432359889061164136489 50036574269916795873102367)
  ·
    refine ⟨75054861404875193809653551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50036574269916795873102367 75054861404875193809653551)
    ·
      refine ⟨112582292107312790714480327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75054861404875193809653551 112582292107312790714480327)
      ·
        refine ⟨168873438160969186071720491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112582292107312790714480327 168873438160969186071720491)
        ·
          refine ⟨253310157241453779107580737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168873438160969186071720491 253310157241453779107580737)
          ·
            refine ⟨189982617931090334330685553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253310157241453779107580737 189982617931090334330685553)
            ·
              refine ⟨142486963448317750748014165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189982617931090334330685553 142486963448317750748014165)
              ·
                refine ⟨1669769102909973641578291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 142486963448317750748014165 1669769102909973641578291)
                ·
                  refine ⟨2504653654364960462367437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669769102909973641578291 2504653654364960462367437)
                  ·
                    refine ⟨939245120386860173387789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504653654364960462367437 939245120386860173387789)
                    ·
                      rfl

theorem cell22_2743760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 1, 3].length) (baseStart_2743760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743760 prefixEnd_2743760 := by exact prefixLift 2743760
  have htrace : WordTrace (prefixWord ++ tailWord_2743760) baseStart_2743760 baseEnd_2743760 := by
    simpa [prefixWord, tailWord_2743760, baseEnd_2743760] using wordTrace_append hprefix tailTrace_2743760
  have hstable : (prefixWord ++ tailWord_2743760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743760).length < 2 ^ (prefixWord ++ tailWord_2743760).sum := by decide
  have hdescent : baseEnd_2743760 < baseStart_2743760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743794 : List Nat := [3, 2, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_2743794 : Nat := 118140960795 + 2743794 * 2 ^ 59
def prefixEnd_2743794 : Nat := 4983230072969 + 3 ^ 40 * 2743794 * 2
def baseEnd_2743794 : Nat := 939256759281695418037685

theorem tailTrace_2743794 : CollatzResearch.WordTrace tailWord_2743794 prefixEnd_2743794 939256759281695418037685 := by
  unfold tailWord_2743794
  simp only [CollatzResearch.WordTrace]
  refine ⟨25018597155427603888235609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66716259081140277035294957 25018597155427603888235609)
  ·
    refine ⟨18763947866570702916176707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25018597155427603888235609 18763947866570702916176707)
    ·
      refine ⟨28145921799856054374265061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18763947866570702916176707 28145921799856054374265061)
      ·
        refine ⟨5277360337473010195174699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28145921799856054374265061 5277360337473010195174699)
        ·
          refine ⟨7916040506209515292762049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5277360337473010195174699 7916040506209515292762049)
          ·
            refine ⟨5937030379657136469571537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7916040506209515292762049 5937030379657136469571537)
            ·
              refine ⟨4452772784742852352178653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5937030379657136469571537 4452772784742852352178653)
              ·
                refine ⟨1669789794278569632066995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4452772784742852352178653 1669789794278569632066995)
                ·
                  refine ⟨2504684691417854448100493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669789794278569632066995 2504684691417854448100493)
                  ·
                    refine ⟨939256759281695418037685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504684691417854448100493 939256759281695418037685)
                    ·
                      rfl

theorem cell22_2743794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_2743794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743794 prefixEnd_2743794 := by exact prefixLift 2743794
  have htrace : WordTrace (prefixWord ++ tailWord_2743794) baseStart_2743794 baseEnd_2743794 := by
    simpa [prefixWord, tailWord_2743794, baseEnd_2743794] using wordTrace_append hprefix tailTrace_2743794
  have hstable : (prefixWord ++ tailWord_2743794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743794).length < 2 ^ (prefixWord ++ tailWord_2743794).sum := by decide
  have hdescent : baseEnd_2743794 < baseStart_2743794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743801 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 10]
def baseStart_2743801 : Nat := 118140960795 + 2743801 * 2 ^ 59
def prefixEnd_2743801 : Nat := 4983230072969 + 3 ^ 40 * 2743801 * 2
def baseEnd_2743801 : Nat := 313086385174916577704221

theorem tailTrace_2743801 : CollatzResearch.WordTrace tailWord_2743801 prefixEnd_2743801 313086385174916577704221 := by
  unfold tailWord_2743801
  simp only [CollatzResearch.WordTrace]
  refine ⟨100074643932685055748447257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66716429288456703832298171 100074643932685055748447257)
  ·
    refine ⟨75055982949513791811335443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100074643932685055748447257 75055982949513791811335443)
    ·
      refine ⟨112583974424270687717003165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75055982949513791811335443 112583974424270687717003165)
      ·
        refine ⟨42218990409101507893876187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112583974424270687717003165 42218990409101507893876187)
        ·
          refine ⟨63328485613652261840814281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42218990409101507893876187 63328485613652261840814281)
          ·
            refine ⟨47496364210239196380610711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63328485613652261840814281 47496364210239196380610711)
            ·
              refine ⟨71244546315358794570916067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47496364210239196380610711 71244546315358794570916067)
              ·
                refine ⟨106866819473038191856374101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71244546315358794570916067 106866819473038191856374101)
                ·
                  refine ⟨313086385174916577704221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 106866819473038191856374101 313086385174916577704221)
                  ·
                    rfl

theorem cell22_2743801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_2743801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743801 prefixEnd_2743801 := by exact prefixLift 2743801
  have htrace : WordTrace (prefixWord ++ tailWord_2743801) baseStart_2743801 baseEnd_2743801 := by
    simpa [prefixWord, tailWord_2743801, baseEnd_2743801] using wordTrace_append hprefix tailTrace_2743801
  have hstable : (prefixWord ++ tailWord_2743801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743801).length < 2 ^ (prefixWord ++ tailWord_2743801).sum := by decide
  have hdescent : baseEnd_2743801 < baseStart_2743801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743803 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 1, 4]
def baseStart_2743803 : Nat := 118140960795 + 2743803 * 2 ^ 59
def prefixEnd_2743803 : Nat := 4983230072969 + 3 ^ 40 * 2743803 * 2
def baseEnd_2743803 : Nat := 939259840165622394562657

theorem tailTrace_2743803 : CollatzResearch.WordTrace tailWord_2743803 prefixEnd_2743803 939259840165622394562657 := by
  unfold tailWord_2743803
  simp only [CollatzResearch.WordTrace]
  refine ⟨100074716878677810090020063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66716477919118540060013375 100074716878677810090020063)
  ·
    refine ⟨150112075318016715135030095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100074716878677810090020063 150112075318016715135030095)
    ·
      refine ⟨225168112977025072702545143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150112075318016715135030095 225168112977025072702545143)
      ·
        refine ⟨337752169465537609053817715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225168112977025072702545143 337752169465537609053817715)
        ·
          refine ⟨506628254198306413580726573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337752169465537609053817715 506628254198306413580726573)
          ·
            refine ⟨189985595324364905092772465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 506628254198306413580726573 189985595324364905092772465)
            ·
              refine ⟨142489196493273678819579349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189985595324364905092772465 142489196493273678819579349)
              ·
                refine ⟨3339590542811101847333891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 142489196493273678819579349 3339590542811101847333891)
                ·
                  refine ⟨5009385814216652771000837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339590542811101847333891 5009385814216652771000837)
                  ·
                    refine ⟨939259840165622394562657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5009385814216652771000837 939259840165622394562657)
                    ·
                      rfl

theorem cell22_2743803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 4].length) (baseStart_2743803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743803 prefixEnd_2743803 := by exact prefixLift 2743803
  have htrace : WordTrace (prefixWord ++ tailWord_2743803) baseStart_2743803 baseEnd_2743803 := by
    simpa [prefixWord, tailWord_2743803, baseEnd_2743803] using wordTrace_append hprefix tailTrace_2743803
  have hstable : (prefixWord ++ tailWord_2743803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743803).length < 2 ^ (prefixWord ++ tailWord_2743803).sum := by decide
  have hdescent : baseEnd_2743803 < baseStart_2743803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743818 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_2743818 : Nat := 118140960795 + 2743818 * 2 ^ 59
def prefixEnd_2743818 : Nat := 4983230072969 + 3 ^ 40 * 2743818 * 2
def baseEnd_2743818 : Nat := 313088324990722451812537

theorem tailTrace_2743818 : CollatzResearch.WordTrace tailWord_2743818 prefixEnd_2743818 313088324990722451812537 := by
  unfold tailWord_2743818
  simp only [CollatzResearch.WordTrace]
  refine ⟨25018815993405866912954027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66716842649082311767877405 25018815993405866912954027)
  ·
    refine ⟨37528223990108800369431041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25018815993405866912954027 37528223990108800369431041)
    ·
      refine ⟨28146167992581600277073281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37528223990108800369431041 28146167992581600277073281)
      ·
        refine ⟨21109625994436200207804961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28146167992581600277073281 21109625994436200207804961)
        ·
          refine ⟨15832219495827150155853721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21109625994436200207804961 15832219495827150155853721)
          ·
            refine ⟨11874164621870362616890291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15832219495827150155853721 11874164621870362616890291)
            ·
              refine ⟨17811246932805543925335437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11874164621870362616890291 17811246932805543925335437)
              ·
                refine ⟨6679217599802078972000789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17811246932805543925335437 6679217599802078972000789)
                ·
                  refine ⟨313088324990722451812537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6679217599802078972000789 313088324990722451812537)
                  ·
                    rfl

theorem cell22_2743818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_2743818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743818 prefixEnd_2743818 := by exact prefixLift 2743818
  have htrace : WordTrace (prefixWord ++ tailWord_2743818) baseStart_2743818 baseEnd_2743818 := by
    simpa [prefixWord, tailWord_2743818, baseEnd_2743818] using wordTrace_append hprefix tailTrace_2743818
  have hstable : (prefixWord ++ tailWord_2743818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743818).length < 2 ^ (prefixWord ++ tailWord_2743818).sum := by decide
  have hdescent : baseEnd_2743818 < baseStart_2743818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743833 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 8, 3]
def baseStart_2743833 : Nat := 118140960795 + 2743833 * 2 ^ 59
def prefixEnd_2743833 : Nat := 4983230072969 + 3 ^ 40 * 2743833 * 2
def baseEnd_2743833 : Nat := 939270109778712316312565

theorem tailTrace_2743833 : CollatzResearch.WordTrace tailWord_2743833 prefixEnd_2743833 939270109778712316312565 := by
  unfold tailWord_2743833
  simp only [CollatzResearch.WordTrace]
  refine ⟨100075811068569125213612153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66717207379046083475741435 100075811068569125213612153)
  ·
    refine ⟨75056858301426843910209115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100075811068569125213612153 75056858301426843910209115)
    ·
      refine ⟨112585287452140265865313673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75056858301426843910209115 112585287452140265865313673)
      ·
        refine ⟨84438965589105199398985255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112585287452140265865313673 84438965589105199398985255)
        ·
          refine ⟨126658448383657799098477883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84438965589105199398985255 126658448383657799098477883)
          ·
            refine ⟨189987672575486698647716825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126658448383657799098477883 189987672575486698647716825)
            ·
              refine ⟨142490754431615023985787619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189987672575486698647716825 142490754431615023985787619)
              ·
                refine ⟨213736131647422535978681429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142490754431615023985787619 213736131647422535978681429)
                ·
                  refine ⟨2504720292743232843500173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 213736131647422535978681429 2504720292743232843500173)
                  ·
                    refine ⟨939270109778712316312565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504720292743232843500173 939270109778712316312565)
                    ·
                      rfl

theorem cell22_2743833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 3].length) (baseStart_2743833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743833 prefixEnd_2743833 := by exact prefixLift 2743833
  have htrace : WordTrace (prefixWord ++ tailWord_2743833) baseStart_2743833 baseEnd_2743833 := by
    simpa [prefixWord, tailWord_2743833, baseEnd_2743833] using wordTrace_append hprefix tailTrace_2743833
  have hstable : (prefixWord ++ tailWord_2743833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743833).length < 2 ^ (prefixWord ++ tailWord_2743833).sum := by decide
  have hdescent : baseEnd_2743833 < baseStart_2743833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743850 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 6, 3]
def baseStart_2743850 : Nat := 118140960795 + 2743850 * 2 ^ 59
def prefixEnd_2743850 : Nat := 4983230072969 + 3 ^ 40 * 2743850 * 2
def baseEnd_2743850 : Nat := 939275929226129938637513

theorem tailTrace_2743850 : CollatzResearch.WordTrace tailWord_2743850 prefixEnd_2743850 939275929226129938637513 := by
  unfold tailWord_2743850
  simp only [CollatzResearch.WordTrace]
  refine ⟨25019107777376884279245251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66717620739671691411320669 25019107777376884279245251)
  ·
    refine ⟨37528661666065326418867877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25019107777376884279245251 37528661666065326418867877)
    ·
      refine ⟨7036624062387248703537727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37528661666065326418867877 7036624062387248703537727)
      ·
        refine ⟨10554936093580873055306591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7036624062387248703537727 10554936093580873055306591)
        ·
          refine ⟨15832404140371309582959887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10554936093580873055306591 15832404140371309582959887)
          ·
            refine ⟨23748606210556964374439831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15832404140371309582959887 23748606210556964374439831)
            ·
              refine ⟨35622909315835446561659747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23748606210556964374439831 35622909315835446561659747)
              ·
                refine ⟨53434363973753169842489621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35622909315835446561659747 53434363973753169842489621)
                ·
                  refine ⟨2504735811269679836366701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53434363973753169842489621 2504735811269679836366701)
                  ·
                    refine ⟨939275929226129938637513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504735811269679836366701 939275929226129938637513)
                    ·
                      rfl

theorem cell22_2743850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_2743850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743850 prefixEnd_2743850 := by exact prefixLift 2743850
  have htrace : WordTrace (prefixWord ++ tailWord_2743850) baseStart_2743850 baseEnd_2743850 := by
    simpa [prefixWord, tailWord_2743850, baseEnd_2743850] using wordTrace_append hprefix tailTrace_2743850
  have hstable : (prefixWord ++ tailWord_2743850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743850).length < 2 ^ (prefixWord ++ tailWord_2743850).sum := by decide
  have hdescent : baseEnd_2743850 < baseStart_2743850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743863 : List Nat := [1, 1, 3, 1, 2, 6, 8]
def baseStart_2743863 : Nat := 118140960795 + 2743863 * 2 ^ 59
def prefixEnd_2743863 : Nat := 4983230072969 + 3 ^ 40 * 2743863 * 2
def baseEnd_2743863 : Nat := 34788162199696379187499

theorem tailTrace_2743863 : CollatzResearch.WordTrace tailWord_2743863 prefixEnd_2743863 34788162199696379187499 := by
  unfold tailWord_2743863
  simp only [CollatzResearch.WordTrace]
  refine ⟨100076905258460440337204243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66717936838973626891469495 100076905258460440337204243)
  ·
    refine ⟨150115357887690660505806365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100076905258460440337204243 150115357887690660505806365)
    ·
      refine ⟨56293259207883997689677387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150115357887690660505806365 56293259207883997689677387)
      ·
        refine ⟨84439888811825996534516081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56293259207883997689677387 84439888811825996534516081)
        ·
          refine ⟨63329916608869497400887061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84439888811825996534516081 63329916608869497400887061)
          ·
            refine ⟨2968589841040757690666581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63329916608869497400887061 2968589841040757690666581)
            ·
              refine ⟨34788162199696379187499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2968589841040757690666581 34788162199696379187499)
              ·
                rfl

theorem cell22_2743863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 8].length) (baseStart_2743863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743863 prefixEnd_2743863 := by exact prefixLift 2743863
  have htrace : WordTrace (prefixWord ++ tailWord_2743863) baseStart_2743863 baseEnd_2743863 := by
    simpa [prefixWord, tailWord_2743863, baseEnd_2743863] using wordTrace_append hprefix tailTrace_2743863
  have hstable : (prefixWord ++ tailWord_2743863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743863).length < 2 ^ (prefixWord ++ tailWord_2743863).sum := by decide
  have hdescent : baseEnd_2743863 < baseStart_2743863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743865 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 2, 4]
def baseStart_2743865 : Nat := 118140960795 + 2743865 * 2 ^ 59
def prefixEnd_2743865 : Nat := 4983230072969 + 3 ^ 40 * 2743865 * 2
def baseEnd_2743865 : Nat := 939281064032674899512467

theorem tailTrace_2743865 : CollatzResearch.WordTrace tailWord_2743865 prefixEnd_2743865 939281064032674899512467 := by
  unfold tailWord_2743865
  simp only [CollatzResearch.WordTrace]
  refine ⟨100076978204453194678777049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66717985469635463119184699 100076978204453194678777049)
  ·
    refine ⟨75057733653339896009082787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100076978204453194678777049 75057733653339896009082787)
    ·
      refine ⟨112586600480009844013624181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75057733653339896009082787 112586600480009844013624181)
      ·
        refine ⟨10554993795000922876277267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112586600480009844013624181 10554993795000922876277267)
        ·
          refine ⟨15832490692501384314415901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10554993795000922876277267 15832490692501384314415901)
          ·
            refine ⟨5937184009688019117905963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15832490692501384314415901 5937184009688019117905963)
            ·
              refine ⟨8905776014532028676858945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937184009688019117905963 8905776014532028676858945)
              ·
                refine ⟨6679332010899021507644209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8905776014532028676858945 6679332010899021507644209)
                ·
                  refine ⟨5009499008174266130733157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6679332010899021507644209 5009499008174266130733157)
                  ·
                    refine ⟨939281064032674899512467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5009499008174266130733157 939281064032674899512467)
                    ·
                      rfl

theorem cell22_2743865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_2743865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743865 prefixEnd_2743865 := by exact prefixLift 2743865
  have htrace : WordTrace (prefixWord ++ tailWord_2743865) baseStart_2743865 baseEnd_2743865 := by
    simpa [prefixWord, tailWord_2743865, baseEnd_2743865] using wordTrace_append hprefix tailTrace_2743865
  have hstable : (prefixWord ++ tailWord_2743865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743865).length < 2 ^ (prefixWord ++ tailWord_2743865).sum := by decide
  have hdescent : baseEnd_2743865 < baseStart_2743865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743869 : List Nat := [1, 4, 1, 3, 3, 1, 3, 2, 4]
def baseStart_2743869 : Nat := 118140960795 + 2743869 * 2 ^ 59
def prefixEnd_2743869 : Nat := 4983230072969 + 3 ^ 40 * 2743869 * 2
def baseEnd_2743869 : Nat := 313094144438140074137485

theorem tailTrace_2743869 : CollatzResearch.WordTrace tailWord_2743869 prefixEnd_2743869 313094144438140074137485 := by
  unfold tailWord_2743869
  simp only [CollatzResearch.WordTrace]
  refine ⟨100077124096438703361922661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66718082730959135574615107 100077124096438703361922661)
  ·
    refine ⟨18764460768082256880360499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100077124096438703361922661 18764460768082256880360499)
    ·
      refine ⟨28146691152123385320540749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18764460768082256880360499 28146691152123385320540749)
      ·
        refine ⟨10555009182046269495202781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28146691152123385320540749 10555009182046269495202781)
        ·
          refine ⟨3958128443267351060701043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10555009182046269495202781 3958128443267351060701043)
          ·
            refine ⟨5937192664901026591051565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3958128443267351060701043 5937192664901026591051565)
            ·
              refine ⟨2226447249337884971644337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5937192664901026591051565 2226447249337884971644337)
              ·
                refine ⟨1669835437003413728733253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2226447249337884971644337 1669835437003413728733253)
                ·
                  refine ⟨313094144438140074137485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669835437003413728733253 313094144438140074137485)
                  ·
                    rfl

theorem cell22_2743869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_2743869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743869 prefixEnd_2743869 := by exact prefixLift 2743869
  have htrace : WordTrace (prefixWord ++ tailWord_2743869) baseStart_2743869 baseEnd_2743869 := by
    simpa [prefixWord, tailWord_2743869, baseEnd_2743869] using wordTrace_append hprefix tailTrace_2743869
  have hstable : (prefixWord ++ tailWord_2743869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743869).length < 2 ^ (prefixWord ++ tailWord_2743869).sum := by decide
  have hdescent : baseEnd_2743869 < baseStart_2743869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743884 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 2, 3]
def baseStart_2743884 : Nat := 118140960795 + 2743884 * 2 ^ 59
def prefixEnd_2743884 : Nat := 4983230072969 + 3 ^ 40 * 2743884 * 2
def baseEnd_2743884 : Nat := 939287568120965183287409

theorem tailTrace_2743884 : CollatzResearch.WordTrace tailWord_2743884 prefixEnd_2743884 939287568120965183287409 := by
  unfold tailWord_2743884
  simp only [CollatzResearch.WordTrace]
  refine ⟨50038835595692180461859353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66718447460922907282479137 50038835595692180461859353)
  ·
    refine ⟨37529126696769135346394515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50038835595692180461859353 37529126696769135346394515)
    ·
      refine ⟨56293690045153703019591773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37529126696769135346394515 56293690045153703019591773)
      ·
        refine ⟨21110133766932638632346915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56293690045153703019591773 21110133766932638632346915)
        ·
          refine ⟨31665200650398957948520373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21110133766932638632346915 31665200650398957948520373)
          ·
            refine ⟨2968612560974902307673785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31665200650398957948520373 2968612560974902307673785)
            ·
              refine ⟨2226459420731176730755339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2968612560974902307673785 2226459420731176730755339)
              ·
                refine ⟨3339689131096765096133009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226459420731176730755339 3339689131096765096133009)
                ·
                  refine ⟨2504766848322573822099757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3339689131096765096133009 2504766848322573822099757)
                  ·
                    refine ⟨939287568120965183287409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504766848322573822099757 939287568120965183287409)
                    ·
                      rfl

theorem cell22_2743884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_2743884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743884 prefixEnd_2743884 := by exact prefixLift 2743884
  have htrace : WordTrace (prefixWord ++ tailWord_2743884) baseStart_2743884 baseEnd_2743884 := by
    simpa [prefixWord, tailWord_2743884, baseEnd_2743884] using wordTrace_append hprefix tailTrace_2743884
  have hstable : (prefixWord ++ tailWord_2743884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743884).length < 2 ^ (prefixWord ++ tailWord_2743884).sum := by decide
  have hdescent : baseEnd_2743884 < baseStart_2743884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2743972 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_2743972 : Nat := 118140960795 + 2743972 * 2 ^ 59
def prefixEnd_2743972 : Nat := 4983230072969 + 3 ^ 40 * 2743972 * 2
def baseEnd_2743972 : Nat := 939317692319362287087139

theorem tailTrace_2743972 : CollatzResearch.WordTrace tailWord_2743972 prefixEnd_2743972 939317692319362287087139 := by
  unfold tailWord_2743972
  simp only [CollatzResearch.WordTrace]
  refine ⟨50040440407532775976461085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66720587210043701301948113 50040440407532775976461085)
  ·
    refine ⟨18765165152824790991172907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50040440407532775976461085 18765165152824790991172907)
    ·
      refine ⟨28147747729237186486759361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18765165152824790991172907 28147747729237186486759361)
      ·
        refine ⟨21110810796927889865069521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28147747729237186486759361 21110810796927889865069521)
        ·
          refine ⟨15833108097695917398802141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21110810796927889865069521 15833108097695917398802141)
          ·
            refine ⟨5937415536635969024550803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15833108097695917398802141 5937415536635969024550803)
            ·
              refine ⟨8906123304953953536826205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937415536635969024550803 8906123304953953536826205)
              ·
                refine ⟨3339796239357732576309827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8906123304953953536826205 3339796239357732576309827)
                ·
                  refine ⟨5009694359036598864464741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339796239357732576309827 5009694359036598864464741)
                  ·
                    refine ⟨939317692319362287087139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5009694359036598864464741 939317692319362287087139)
                    ·
                      rfl

theorem cell22_2743972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_2743972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2743972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2743972 prefixEnd_2743972 := by exact prefixLift 2743972
  have htrace : WordTrace (prefixWord ++ tailWord_2743972) baseStart_2743972 baseEnd_2743972 := by
    simpa [prefixWord, tailWord_2743972, baseEnd_2743972] using wordTrace_append hprefix tailTrace_2743972
  have hstable : (prefixWord ++ tailWord_2743972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2743972).length < 2 ^ (prefixWord ++ tailWord_2743972).sum := by decide
  have hdescent : baseEnd_2743972 < baseStart_2743972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2743972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744006 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2744006 : Nat := 118140960795 + 2744006 * 2 ^ 59
def prefixEnd_2744006 : Nat := 4983230072969 + 3 ^ 40 * 2744006 * 2
def baseEnd_2744006 : Nat := 939329331214197531737035

theorem tailTrace_2744006 : CollatzResearch.WordTrace tailWord_2744006 prefixEnd_2744006 939329331214197531737035 := by
  unfold tailWord_2744006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3127566278029449242489371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66721413931294917173106581 3127566278029449242489371)
  ·
    refine ⟨4691349417044173863734057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3127566278029449242489371 4691349417044173863734057)
    ·
      refine ⟨3518512062783130397800543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4691349417044173863734057 3518512062783130397800543)
      ·
        refine ⟨5277768094174695596700815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3518512062783130397800543 5277768094174695596700815)
        ·
          refine ⟨7916652141262043395051223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5277768094174695596700815 7916652141262043395051223)
          ·
            refine ⟨11874978211893065092576835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7916652141262043395051223 11874978211893065092576835)
            ·
              refine ⟨17812467317839597638865253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11874978211893065092576835 17812467317839597638865253)
              ·
                refine ⟨3339837622094924557287235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17812467317839597638865253 3339837622094924557287235)
                ·
                  refine ⟨5009756433142386835930853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339837622094924557287235 5009756433142386835930853)
                  ·
                    refine ⟨939329331214197531737035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5009756433142386835930853 939329331214197531737035)
                    ·
                      rfl

theorem cell22_2744006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2744006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744006 prefixEnd_2744006 := by exact prefixLift 2744006
  have htrace : WordTrace (prefixWord ++ tailWord_2744006) baseStart_2744006 baseEnd_2744006 := by
    simpa [prefixWord, tailWord_2744006, baseEnd_2744006] using wordTrace_append hprefix tailTrace_2744006
  have hstable : (prefixWord ++ tailWord_2744006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744006).length < 2 ^ (prefixWord ++ tailWord_2744006).sum := by decide
  have hdescent : baseEnd_2744006 < baseStart_2744006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744070 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2744070 : Nat := 118140960795 + 2744070 * 2 ^ 59
def prefixEnd_2744070 : Nat := 4983230072969 + 3 ^ 40 * 2744070 * 2
def baseEnd_2744070 : Nat := 939351239722122698136839

theorem tailTrace_2744070 : CollatzResearch.WordTrace tailWord_2744070 prefixEnd_2744070 939351239722122698136839 := by
  unfold tailWord_2744070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3127639224022203584062177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66722970112473676459993109 3127639224022203584062177)
  ·
    refine ⟨2345729418016652688046633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3127639224022203584062177 2345729418016652688046633)
    ·
      refine ⟨1759297063512489516034975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2345729418016652688046633 1759297063512489516034975)
      ·
        refine ⟨2638945595268734274052463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1759297063512489516034975 2638945595268734274052463)
        ·
          refine ⟨3958418392903101411078695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2638945595268734274052463 3958418392903101411078695)
          ·
            refine ⟨5937627589354652116618043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3958418392903101411078695 5937627589354652116618043)
            ·
              refine ⟨8906441384031978174927065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937627589354652116618043 8906441384031978174927065)
              ·
                refine ⟨6679831038023983631195299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8906441384031978174927065 6679831038023983631195299)
                ·
                  refine ⟨10019746557035975446792949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6679831038023983631195299 10019746557035975446792949)
                  ·
                    refine ⟨939351239722122698136839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10019746557035975446792949 939351239722122698136839)
                    ·
                      rfl

theorem cell22_2744070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2744070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744070 prefixEnd_2744070 := by exact prefixLift 2744070
  have htrace : WordTrace (prefixWord ++ tailWord_2744070) baseStart_2744070 baseEnd_2744070 := by
    simpa [prefixWord, tailWord_2744070, baseEnd_2744070] using wordTrace_append hprefix tailTrace_2744070
  have hstable : (prefixWord ++ tailWord_2744070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744070).length < 2 ^ (prefixWord ++ tailWord_2744070).sum := by decide
  have hdescent : baseEnd_2744070 < baseStart_2744070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744122 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_2744122 : Nat := 118140960795 + 2744122 * 2 ^ 59
def prefixEnd_2744122 : Nat := 4983230072969 + 3 ^ 40 * 2744122 * 2
def baseEnd_2744122 : Nat := 313123013461603965278893

theorem tailTrace_2744122 : CollatzResearch.WordTrace tailWord_2744122 prefixEnd_2744122 313123013461603965278893 := by
  unfold tailWord_2744122
  simp only [CollatzResearch.WordTrace]
  refine ⟨25021587941130531892720655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66724234509681418380588413 25021587941130531892720655)
  ·
    refine ⟨37532381911695797839080983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25021587941130531892720655 37532381911695797839080983)
    ·
      refine ⟨56298572867543696758621475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37532381911695797839080983 56298572867543696758621475)
      ·
        refine ⟨84447859301315545137932213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56298572867543696758621475 84447859301315545137932213)
        ·
          refine ⟨7916986809498332356681145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84447859301315545137932213 7916986809498332356681145)
          ·
            refine ⟨5937740107123749267510859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7916986809498332356681145 5937740107123749267510859)
            ·
              refine ⟨8906610160685623901266289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937740107123749267510859 8906610160685623901266289)
              ·
                refine ⟨6679957620514217925949717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8906610160685623901266289 6679957620514217925949717)
                ·
                  refine ⟨313123013461603965278893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6679957620514217925949717 313123013461603965278893)
                  ·
                    rfl

theorem cell22_2744122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_2744122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744122 prefixEnd_2744122 := by exact prefixLift 2744122
  have htrace : WordTrace (prefixWord ++ tailWord_2744122) baseStart_2744122 baseEnd_2744122 := by
    simpa [prefixWord, tailWord_2744122, baseEnd_2744122] using wordTrace_append hprefix tailTrace_2744122
  have hstable : (prefixWord ++ tailWord_2744122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744122).length < 2 ^ (prefixWord ++ tailWord_2744122).sum := by decide
  have hdescent : baseEnd_2744122 < baseStart_2744122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744137 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 4, 3]
def baseStart_2744137 : Nat := 118140960795 + 2744137 * 2 ^ 59
def prefixEnd_2744137 : Nat := 4983230072969 + 3 ^ 40 * 2744137 * 2
def baseEnd_2744137 : Nat := 939374175191356856711633

theorem tailTrace_2744137 : CollatzResearch.WordTrace tailWord_2744137 prefixEnd_2744137 939374175191356856711633 := by
  unfold tailWord_2744137
  simp only [CollatzResearch.WordTrace]
  refine ⟨100086898859467785132678665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66724599239645190088452443 100086898859467785132678665)
  ·
    refine ⟨75065174144600838849508999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100086898859467785132678665 75065174144600838849508999)
    ·
      refine ⟨112597761216901258274263499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75065174144600838849508999 112597761216901258274263499)
      ·
        refine ⟨168896641825351887411395249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112597761216901258274263499 168896641825351887411395249)
        ·
          refine ⟨126672481369013915558546437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168896641825351887411395249 126672481369013915558546437)
          ·
            refine ⟨23751090256690109167227457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126672481369013915558546437 23751090256690109167227457)
            ·
              refine ⟨17813317692517581875420593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23751090256690109167227457 17813317692517581875420593)
              ·
                refine ⟨13359988269388186406565445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17813317692517581875420593 13359988269388186406565445)
                ·
                  refine ⟨2504997800510284951231021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13359988269388186406565445 2504997800510284951231021)
                  ·
                    refine ⟨939374175191356856711633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504997800510284951231021 939374175191356856711633)
                    ·
                      rfl

theorem cell22_2744137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 3].length) (baseStart_2744137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744137 prefixEnd_2744137 := by exact prefixLift 2744137
  have htrace : WordTrace (prefixWord ++ tailWord_2744137) baseStart_2744137 baseEnd_2744137 := by
    simpa [prefixWord, tailWord_2744137, baseEnd_2744137] using wordTrace_append hprefix tailTrace_2744137
  have hstable : (prefixWord ++ tailWord_2744137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744137).length < 2 ^ (prefixWord ++ tailWord_2744137).sum := by decide
  have hdescent : baseEnd_2744137 < baseStart_2744137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744141 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_2744141 : Nat := 118140960795 + 2744141 * 2 ^ 59
def prefixEnd_2744141 : Nat := 4983230072969 + 3 ^ 40 * 2744141 * 2
def baseEnd_2744141 : Nat := 939375544473102179611621

theorem tailTrace_2744141 : CollatzResearch.WordTrace tailWord_2744141 prefixEnd_2744141 939375544473102179611621 := by
  unfold tailWord_2744141
  simp only [CollatzResearch.WordTrace]
  refine ⟨100087044751453293815824277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66724696500968862543882851 100087044751453293815824277)
  ·
    refine ⟨4691580222724373147616763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100087044751453293815824277 4691580222724373147616763)
    ·
      refine ⟨7037370334086559721425145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4691580222724373147616763 7037370334086559721425145)
      ·
        refine ⟨5278027750564919791068859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7037370334086559721425145 5278027750564919791068859)
        ·
          refine ⟨7917041625847379686603289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5278027750564919791068859 7917041625847379686603289)
          ·
            refine ⟨5937781219385534764952467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7917041625847379686603289 5937781219385534764952467)
            ·
              refine ⟨8906671829078302147428701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5937781219385534764952467 8906671829078302147428701)
              ·
                refine ⟨3340001935904363305285763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8906671829078302147428701 3340001935904363305285763)
                ·
                  refine ⟨5010002903856544957928645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340001935904363305285763 5010002903856544957928645)
                  ·
                    refine ⟨939375544473102179611621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010002903856544957928645 939375544473102179611621)
                    ·
                      rfl

theorem cell22_2744141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_2744141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744141 prefixEnd_2744141 := by exact prefixLift 2744141
  have htrace : WordTrace (prefixWord ++ tailWord_2744141) baseStart_2744141 baseEnd_2744141 := by
    simpa [prefixWord, tailWord_2744141, baseEnd_2744141] using wordTrace_append hprefix tailTrace_2744141
  have hstable : (prefixWord ++ tailWord_2744141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744141).length < 2 ^ (prefixWord ++ tailWord_2744141).sum := by decide
  have hdescent : baseEnd_2744141 < baseStart_2744141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744222 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_2744222 : Nat := 118140960795 + 2744222 * 2 ^ 59
def prefixEnd_2744222 : Nat := 4983230072969 + 3 ^ 40 * 2744222 * 2
def baseEnd_2744222 : Nat := 939403272428444968336373

theorem tailTrace_2744222 : CollatzResearch.WordTrace tailWord_2744222 prefixEnd_2744222 939403272428444968336373 := by
  unfold tailWord_2744222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12511249883019980581190365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66726666042773229766348613 12511249883019980581190365)
  ·
    refine ⟨4691718706132492717946387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12511249883019980581190365 4691718706132492717946387)
    ·
      refine ⟨7037578059198739076919581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4691718706132492717946387 7037578059198739076919581)
      ·
        refine ⟨2639091772199527153844843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7037578059198739076919581 2639091772199527153844843)
        ·
          refine ⟨3958637658299290730767265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2639091772199527153844843 3958637658299290730767265)
          ·
            refine ⟨2968978243724468048075449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3958637658299290730767265 2968978243724468048075449)
            ·
              refine ⟨2226733682793351036056587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2968978243724468048075449 2226733682793351036056587)
              ·
                refine ⟨3340100524190026554084881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226733682793351036056587 3340100524190026554084881)
                ·
                  refine ⟨2505075393142519915563661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3340100524190026554084881 2505075393142519915563661)
                  ·
                    refine ⟨939403272428444968336373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2505075393142519915563661 939403272428444968336373)
                    ·
                      rfl

theorem cell22_2744222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_2744222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744222 prefixEnd_2744222 := by exact prefixLift 2744222
  have htrace : WordTrace (prefixWord ++ tailWord_2744222) baseStart_2744222 baseEnd_2744222 := by
    simpa [prefixWord, tailWord_2744222, baseEnd_2744222] using wordTrace_append hprefix tailTrace_2744222
  have hstable : (prefixWord ++ tailWord_2744222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744222).length < 2 ^ (prefixWord ++ tailWord_2744222).sum := by decide
  have hdescent : baseEnd_2744222 < baseStart_2744222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744304 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 2, 4]
def baseStart_2744304 : Nat := 118140960795 + 2744304 * 2 ^ 59
def prefixEnd_2744304 : Nat := 4983230072969 + 3 ^ 40 * 2744304 * 2
def baseEnd_2744304 : Nat := 939431342704224087786121

theorem tailTrace_2744304 : CollatzResearch.WordTrace tailWord_2744304 prefixEnd_2744304 939431342704224087786121 := by
  unfold tailWord_2744304
  simp only [CollatzResearch.WordTrace]
  refine ⟨50046494924931386327003983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66728659899908515102671977 50046494924931386327003983)
  ·
    refine ⟨75069742387397079490505975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50046494924931386327003983 75069742387397079490505975)
    ·
      refine ⟨112604613581095619235758963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75069742387397079490505975 112604613581095619235758963)
      ·
        refine ⟨168906920371643428853638445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112604613581095619235758963 168906920371643428853638445)
        ·
          refine ⟨63340095139366285820114417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168906920371643428853638445 63340095139366285820114417)
          ·
            refine ⟨47505071354524714365085813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63340095139366285820114417 47505071354524714365085813)
            ·
              refine ⟨4453600439486691971726795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47505071354524714365085813 4453600439486691971726795)
              ·
                refine ⟨6680400659230037957590193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4453600439486691971726795 6680400659230037957590193)
                ·
                  refine ⟨5010300494422528468192645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6680400659230037957590193 5010300494422528468192645)
                  ·
                    refine ⟨939431342704224087786121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010300494422528468192645 939431342704224087786121)
                    ·
                      rfl

theorem cell22_2744304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_2744304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744304 prefixEnd_2744304 := by exact prefixLift 2744304
  have htrace : WordTrace (prefixWord ++ tailWord_2744304) baseStart_2744304 baseEnd_2744304 := by
    simpa [prefixWord, tailWord_2744304, baseEnd_2744304] using wordTrace_append hprefix tailTrace_2744304
  have hstable : (prefixWord ++ tailWord_2744304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744304).length < 2 ^ (prefixWord ++ tailWord_2744304).sum := by decide
  have hdescent : baseEnd_2744304 < baseStart_2744304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744310 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_2744310 : Nat := 118140960795 + 2744310 * 2 ^ 59
def prefixEnd_2744310 : Nat := 4983230072969 + 3 ^ 40 * 2744310 * 2
def baseEnd_2744310 : Nat := 939433396626842072136103

theorem tailTrace_2744310 : CollatzResearch.WordTrace tailWord_2744310 prefixEnd_2744310 939433396626842072136103 := by
  unfold tailWord_2744310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6255825542990064729920399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66728805791894023785817589 6255825542990064729920399)
  ·
    refine ⟨9383738314485097094880599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6255825542990064729920399 9383738314485097094880599)
    ·
      refine ⟨14075607471727645642320899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9383738314485097094880599 14075607471727645642320899)
      ·
        refine ⟨21113411207591468463481349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14075607471727645642320899 21113411207591468463481349)
        ·
          refine ⟨3958764601423400336902753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21113411207591468463481349 3958764601423400336902753)
          ·
            refine ⟨2969073451067550252677065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3958764601423400336902753 2969073451067550252677065)
            ·
              refine ⟨2226805088300662689507799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969073451067550252677065 2226805088300662689507799)
              ·
                refine ⟨3340207632450994034261699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226805088300662689507799 3340207632450994034261699)
                ·
                  refine ⟨5010311448676491051392549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340207632450994034261699 5010311448676491051392549)
                  ·
                    refine ⟨939433396626842072136103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010311448676491051392549 939433396626842072136103)
                    ·
                      rfl

theorem cell22_2744310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_2744310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744310 prefixEnd_2744310 := by exact prefixLift 2744310
  have htrace : WordTrace (prefixWord ++ tailWord_2744310) baseStart_2744310 baseEnd_2744310 := by
    simpa [prefixWord, tailWord_2744310, baseEnd_2744310] using wordTrace_append hprefix tailTrace_2744310
  have hstable : (prefixWord ++ tailWord_2744310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744310).length < 2 ^ (prefixWord ++ tailWord_2744310).sum := by decide
  have hdescent : baseEnd_2744310 < baseStart_2744310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744340 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2744340 : Nat := 118140960795 + 2744340 * 2 ^ 59
def prefixEnd_2744340 : Nat := 4983230072969 + 3 ^ 40 * 2744340 * 2
def baseEnd_2744340 : Nat := 939443666239931993886011

theorem tailTrace_2744340 : CollatzResearch.WordTrace tailWord_2744340 prefixEnd_2744340 939443666239931993886011 := by
  unfold tailWord_2744340
  simp only [CollatzResearch.WordTrace]
  refine ⟨50047151438866175401159237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66729535251821567201545649 50047151438866175401159237)
  ·
    refine ⟨9383840894787407887717357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50047151438866175401159237 9383840894787407887717357)
    ·
      refine ⟨3518940335545277957894009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9383840894787407887717357 3518940335545277957894009)
      ·
        refine ⟨2639205251658958468420507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3518940335545277957894009 2639205251658958468420507)
        ·
          refine ⟨3958807877488437702630761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2639205251658958468420507 3958807877488437702630761)
          ·
            refine ⟨2969105908116328276973071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3958807877488437702630761 2969105908116328276973071)
            ·
              refine ⟨4453658862174492415459607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969105908116328276973071 4453658862174492415459607)
              ·
                refine ⟨6680488293261738623189411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4453658862174492415459607 6680488293261738623189411)
                ·
                  refine ⟨10020732439892607934784117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6680488293261738623189411 10020732439892607934784117)
                  ·
                    refine ⟨939443666239931993886011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10020732439892607934784117 939443666239931993886011)
                    ·
                      rfl

theorem cell22_2744340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2744340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744340 prefixEnd_2744340 := by exact prefixLift 2744340
  have htrace : WordTrace (prefixWord ++ tailWord_2744340) baseStart_2744340 baseEnd_2744340 := by
    simpa [prefixWord, tailWord_2744340, baseEnd_2744340] using wordTrace_append hprefix tailTrace_2744340
  have hstable : (prefixWord ++ tailWord_2744340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744340).length < 2 ^ (prefixWord ++ tailWord_2744340).sum := by decide
  have hdescent : baseEnd_2744340 < baseStart_2744340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744353 : List Nat := [1, 2, 3, 2, 5, 1, 2, 6]
def baseStart_2744353 : Nat := 118140960795 + 2744353 * 2 ^ 59
def prefixEnd_2744353 : Nat := 4983230072969 + 3 ^ 40 * 2744353 * 2
def baseEnd_2744353 : Nat := 104383124045067143701219

theorem tailTrace_2744353 : CollatzResearch.WordTrace tailWord_2744353 prefixEnd_2744353 104383124045067143701219 := by
  unfold tailWord_2744353
  simp only [CollatzResearch.WordTrace]
  refine ⟨100094777026685254022541713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66729851351123502681694475 100094777026685254022541713)
  ·
    refine ⟨75071082770013940516906285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100094777026685254022541713 75071082770013940516906285)
    ·
      refine ⟨28151656038755227693839857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75071082770013940516906285 28151656038755227693839857)
      ·
        refine ⟨21113742029066420770379893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28151656038755227693839857 21113742029066420770379893)
        ·
          refine ⟨1979413315224976947223115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21113742029066420770379893 1979413315224976947223115)
          ·
            refine ⟨2969119972837465420834673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1979413315224976947223115 2969119972837465420834673)
            ·
              refine ⟨2226839979628099065626005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969119972837465420834673 2226839979628099065626005)
              ·
                refine ⟨104383124045067143701219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2226839979628099065626005 104383124045067143701219)
                ·
                  rfl

theorem cell22_2744353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 6].length) (baseStart_2744353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744353 prefixEnd_2744353 := by exact prefixLift 2744353
  have htrace : WordTrace (prefixWord ++ tailWord_2744353) baseStart_2744353 baseEnd_2744353 := by
    simpa [prefixWord, tailWord_2744353, baseEnd_2744353] using wordTrace_append hprefix tailTrace_2744353
  have hstable : (prefixWord ++ tailWord_2744353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744353).length < 2 ^ (prefixWord ++ tailWord_2744353).sum := by decide
  have hdescent : baseEnd_2744353 < baseStart_2744353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744368 : List Nat := [2, 1, 1, 1, 2, 5, 3, 3, 1, 3]
def baseStart_2744368 : Nat := 118140960795 + 2744368 * 2 ^ 59
def prefixEnd_2744368 : Nat := 4983230072969 + 3 ^ 40 * 2744368 * 2
def baseEnd_2744368 : Nat := 939453251212149254185925

theorem tailTrace_2744368 : CollatzResearch.WordTrace tailWord_2744368 prefixEnd_2744368 939453251212149254185925 := by
  unfold tailWord_2744368
  simp only [CollatzResearch.WordTrace]
  refine ⟨50047662060815455792168879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66730216081087274389558505 50047662060815455792168879)
  ·
    refine ⟨75071493091223183688253319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50047662060815455792168879 75071493091223183688253319)
    ·
      refine ⟨112607239636834775532379979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75071493091223183688253319 112607239636834775532379979)
      ·
        refine ⟨168910859455252163298569969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112607239636834775532379979 168910859455252163298569969)
        ·
          refine ⟨126683144591439122473927477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168910859455252163298569969 126683144591439122473927477)
          ·
            refine ⟨11876544805447417731930701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126683144591439122473927477 11876544805447417731930701)
            ·
              refine ⟨4453704302042781649474013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11876544805447417731930701 4453704302042781649474013)
              ·
                refine ⟨1670139113266043118552755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4453704302042781649474013 1670139113266043118552755)
                ·
                  refine ⟨2505208669899064677829133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670139113266043118552755 2505208669899064677829133)
                  ·
                    refine ⟨939453251212149254185925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2505208669899064677829133 939453251212149254185925)
                    ·
                      rfl

theorem cell22_2744368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 1, 3].length) (baseStart_2744368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744368 prefixEnd_2744368 := by exact prefixLift 2744368
  have htrace : WordTrace (prefixWord ++ tailWord_2744368) baseStart_2744368 baseEnd_2744368 := by
    simpa [prefixWord, tailWord_2744368, baseEnd_2744368] using wordTrace_append hprefix tailTrace_2744368
  have hstable : (prefixWord ++ tailWord_2744368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744368).length < 2 ^ (prefixWord ++ tailWord_2744368).sum := by decide
  have hdescent : baseEnd_2744368 < baseStart_2744368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744394 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_2744394 : Nat := 118140960795 + 2744394 * 2 ^ 59
def prefixEnd_2744394 : Nat := 4983230072969 + 3 ^ 40 * 2744394 * 2
def baseEnd_2744394 : Nat := 939462151543493853035845

theorem tailTrace_2744394 : CollatzResearch.WordTrace tailWord_2744394 prefixEnd_2744394 939462151543493853035845 := by
  unfold tailWord_2744394
  simp only [CollatzResearch.WordTrace]
  refine ⟨25024068104884179506196059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66730848279691145349856157 25024068104884179506196059)
  ·
    refine ⟨37536102157326269259294089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25024068104884179506196059 37536102157326269259294089)
    ·
      refine ⟨28152076617994701944470567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37536102157326269259294089 28152076617994701944470567)
      ·
        refine ⟨42228114926992052916705851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28152076617994701944470567 42228114926992052916705851)
        ·
          refine ⟨63342172390488079375058777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42228114926992052916705851 63342172390488079375058777)
          ·
            refine ⟨47506629292866059531294083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63342172390488079375058777 47506629292866059531294083)
            ·
              refine ⟨71259943939299089296941125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47506629292866059531294083 71259943939299089296941125)
              ·
                refine ⟨13361239488618579243176461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71259943939299089296941125 13361239488618579243176461)
                ·
                  refine ⟨5010464808231967216191173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13361239488618579243176461 5010464808231967216191173)
                  ·
                    refine ⟨939462151543493853035845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010464808231967216191173 939462151543493853035845)
                    ·
                      rfl

theorem cell22_2744394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_2744394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744394 prefixEnd_2744394 := by exact prefixLift 2744394
  have htrace : WordTrace (prefixWord ++ tailWord_2744394) baseStart_2744394 baseEnd_2744394 := by
    simpa [prefixWord, tailWord_2744394, baseEnd_2744394] using wordTrace_append hprefix tailTrace_2744394
  have hstable : (prefixWord ++ tailWord_2744394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744394).length < 2 ^ (prefixWord ++ tailWord_2744394).sum := by decide
  have hdescent : baseEnd_2744394 < baseStart_2744394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744398 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_2744398 : Nat := 118140960795 + 2744398 * 2 ^ 59
def prefixEnd_2744398 : Nat := 4983230072969 + 3 ^ 40 * 2744398 * 2
def baseEnd_2744398 : Nat := 313154506941746391978611

theorem tailTrace_2744398 : CollatzResearch.WordTrace tailWord_2744398 prefixEnd_2744398 313154506941746391978611 := by
  unfold tailWord_2744398
  simp only [CollatzResearch.WordTrace]
  refine ⟨12512052288940278338491231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66730945541014817805286565 12512052288940278338491231)
  ·
    refine ⟨18768078433410417507736847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12512052288940278338491231 18768078433410417507736847)
    ·
      refine ⟨28152117650115626261605271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18768078433410417507736847 28152117650115626261605271)
      ·
        refine ⟨42228176475173439392407907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28152117650115626261605271 42228176475173439392407907)
        ·
          refine ⟨63342264712760159088611861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42228176475173439392407907 63342264712760159088611861)
          ·
            refine ⟨2969168658410632457278681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63342264712760159088611861 2969168658410632457278681)
            ·
              refine ⟨2226876493807974342959011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969168658410632457278681 2226876493807974342959011)
              ·
                refine ⟨3340314740711961514438517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226876493807974342959011 3340314740711961514438517)
                ·
                  refine ⟨313154506941746391978611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3340314740711961514438517 313154506941746391978611)
                  ·
                    rfl

theorem cell22_2744398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_2744398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744398 prefixEnd_2744398 := by exact prefixLift 2744398
  have htrace : WordTrace (prefixWord ++ tailWord_2744398) baseStart_2744398 baseEnd_2744398 := by
    simpa [prefixWord, tailWord_2744398, baseEnd_2744398] using wordTrace_append hprefix tailTrace_2744398
  have hstable : (prefixWord ++ tailWord_2744398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744398).length < 2 ^ (prefixWord ++ tailWord_2744398).sum := by decide
  have hdescent : baseEnd_2744398 < baseStart_2744398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744428 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 1, 4]
def baseStart_2744428 : Nat := 118140960795 + 2744428 * 2 ^ 59
def prefixEnd_2744428 : Nat := 4983230072969 + 3 ^ 40 * 2744428 * 2
def baseEnd_2744428 : Nat := 939473790438329097685741

theorem tailTrace_2744428 : CollatzResearch.WordTrace tailWord_2744428 prefixEnd_2744428 939473790438329097685741 := by
  unfold tailWord_2744428
  simp only [CollatzResearch.WordTrace]
  refine ⟨50048756250706770915760969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66731675000942361221014625 50048756250706770915760969)
  ·
    refine ⟨37536567188030078186820727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50048756250706770915760969 37536567188030078186820727)
    ·
      refine ⟨56304850782045117280231091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37536567188030078186820727 56304850782045117280231091)
      ·
        refine ⟨84457276173067675920346637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56304850782045117280231091 84457276173067675920346637)
        ·
          refine ⟨31671478564900378470129989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84457276173067675920346637 31671478564900378470129989)
          ·
            refine ⟨5938402230918820963149373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31671478564900378470129989 5938402230918820963149373)
            ·
              refine ⟨2226900836594557861181015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5938402230918820963149373 2226900836594557861181015)
              ·
                refine ⟨3340351254891836791771523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226900836594557861181015 3340351254891836791771523)
                ·
                  refine ⟨5010526882337755187657285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340351254891836791771523 5010526882337755187657285)
                  ·
                    refine ⟨939473790438329097685741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010526882337755187657285 939473790438329097685741)
                    ·
                      rfl

theorem cell22_2744428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_2744428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744428 prefixEnd_2744428 := by exact prefixLift 2744428
  have htrace : WordTrace (prefixWord ++ tailWord_2744428) baseStart_2744428 baseEnd_2744428 := by
    simpa [prefixWord, tailWord_2744428, baseEnd_2744428] using wordTrace_append hprefix tailTrace_2744428
  have hstable : (prefixWord ++ tailWord_2744428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744428).length < 2 ^ (prefixWord ++ tailWord_2744428).sum := by decide
  have hdescent : baseEnd_2744428 < baseStart_2744428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744458 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 2, 3]
def baseStart_2744458 : Nat := 118140960795 + 2744458 * 2 ^ 59
def prefixEnd_2744458 : Nat := 4983230072969 + 3 ^ 40 * 2744458 * 2
def baseEnd_2744458 : Nat := 939484060051419019435649

theorem tailTrace_2744458 : CollatzResearch.WordTrace tailWord_2744458 prefixEnd_2744458 939484060051419019435649 := by
  unfold tailWord_2744458
  simp only [CollatzResearch.WordTrace]
  refine ⟨25024651672826214238778507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66732404460869904636742685 25024651672826214238778507)
  ·
    refine ⟨37536977509239321358167761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25024651672826214238778507 37536977509239321358167761)
    ·
      refine ⟨28152733131929491018625821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37536977509239321358167761 28152733131929491018625821)
      ·
        refine ⟨10557274924473559131984683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28152733131929491018625821 10557274924473559131984683)
        ·
          refine ⟨15835912386710338697977025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10557274924473559131984683 15835912386710338697977025)
          ·
            refine ⟨11876934290032754023482769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15835912386710338697977025 11876934290032754023482769)
            ·
              refine ⟨8907700717524565517612077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11876934290032754023482769 8907700717524565517612077)
              ·
                refine ⟨3340387769071712069104529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8907700717524565517612077 3340387769071712069104529)
                ·
                  refine ⟨2505290826803784051828397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3340387769071712069104529 2505290826803784051828397)
                  ·
                    refine ⟨939484060051419019435649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2505290826803784051828397 939484060051419019435649)
                    ·
                      rfl

theorem cell22_2744458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_2744458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744458 prefixEnd_2744458 := by exact prefixLift 2744458
  have htrace : WordTrace (prefixWord ++ tailWord_2744458) baseStart_2744458 baseEnd_2744458 := by
    simpa [prefixWord, tailWord_2744458, baseEnd_2744458] using wordTrace_append hprefix tailTrace_2744458
  have hstable : (prefixWord ++ tailWord_2744458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744458).length < 2 ^ (prefixWord ++ tailWord_2744458).sum := by decide
  have hdescent : baseEnd_2744458 < baseStart_2744458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744503 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 3, 3]
def baseStart_2744503 : Nat := 118140960795 + 2744503 * 2 ^ 59
def prefixEnd_2744503 : Nat := 4983230072969 + 3 ^ 40 * 2744503 * 2
def baseEnd_2744503 : Nat := 939499464471053902060511

theorem tailTrace_2744503 : CollatzResearch.WordTrace tailWord_2744503 prefixEnd_2744503 939499464471053902060511 := by
  unfold tailWord_2744503
  simp only [CollatzResearch.WordTrace]
  refine ⟨100100247976141829640502163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66733498650761219760334775 100100247976141829640502163)
  ·
    refine ⟨150150371964212744460753245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100100247976141829640502163 150150371964212744460753245)
    ·
      refine ⟨56306389486579779172782467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150150371964212744460753245 56306389486579779172782467)
      ·
        refine ⟨84459584229869668759173701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56306389486579779172782467 84459584229869668759173701)
        ·
          refine ⟨15836172043100562892345069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84459584229869668759173701 15836172043100562892345069)
          ·
            refine ⟨5938564516162711084629401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15836172043100562892345069 5938564516162711084629401)
            ·
              refine ⟨4453923387122033313472051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5938564516162711084629401 4453923387122033313472051)
              ·
                refine ⟨6680885080683049970208077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4453923387122033313472051 6680885080683049970208077)
                ·
                  refine ⟨2505331905256143738828029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6680885080683049970208077 2505331905256143738828029)
                  ·
                    refine ⟨939499464471053902060511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2505331905256143738828029 939499464471053902060511)
                    ·
                      rfl

theorem cell22_2744503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_2744503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744503 prefixEnd_2744503 := by exact prefixLift 2744503
  have htrace : WordTrace (prefixWord ++ tailWord_2744503) baseStart_2744503 baseEnd_2744503 := by
    simpa [prefixWord, tailWord_2744503, baseEnd_2744503] using wordTrace_append hprefix tailTrace_2744503
  have hstable : (prefixWord ++ tailWord_2744503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744503).length < 2 ^ (prefixWord ++ tailWord_2744503).sum := by decide
  have hdescent : baseEnd_2744503 < baseStart_2744503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744561 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 6]
def baseStart_2744561 : Nat := 118140960795 + 2744561 * 2 ^ 59
def prefixEnd_2744561 : Nat := 4983230072969 + 3 ^ 40 * 2744561 * 2
def baseEnd_2744561 : Nat := 313173106352120361370111

theorem tailTrace_2744561 : CollatzResearch.WordTrace tailWord_2744561 prefixEnd_2744561 313173106352120361370111 := by
  unfold tailWord_2744561
  simp only [CollatzResearch.WordTrace]
  refine ⟨100102363409931705546113537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66734908939954470364075691 100102363409931705546113537)
  ·
    refine ⟨75076772557448779159585153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100102363409931705546113537 75076772557448779159585153)
    ·
      refine ⟨56307579418086584369688865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75076772557448779159585153 56307579418086584369688865)
      ·
        refine ⟨42230684563564938277266649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56307579418086584369688865 42230684563564938277266649)
        ·
          refine ⟨31673013422673703707949987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42230684563564938277266649 31673013422673703707949987)
          ·
            refine ⟨47509520134010555561924981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31673013422673703707949987 47509520134010555561924981)
            ·
              refine ⟨4454017512563489583930467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47509520134010555561924981 4454017512563489583930467)
              ·
                refine ⟨6681026268845234375895701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4454017512563489583930467 6681026268845234375895701)
                ·
                  refine ⟨313173106352120361370111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6681026268845234375895701 313173106352120361370111)
                  ·
                    rfl

theorem cell22_2744561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_2744561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744561 prefixEnd_2744561 := by exact prefixLift 2744561
  have htrace : WordTrace (prefixWord ++ tailWord_2744561) baseStart_2744561 baseEnd_2744561 := by
    simpa [prefixWord, tailWord_2744561, baseEnd_2744561] using wordTrace_append hprefix tailTrace_2744561
  have hstable : (prefixWord ++ tailWord_2744561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744561).length < 2 ^ (prefixWord ++ tailWord_2744561).sum := by decide
  have hdescent : baseEnd_2744561 < baseStart_2744561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744608 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 2, 4]
def baseStart_2744608 : Nat := 118140960795 + 2744608 * 2 ^ 59
def prefixEnd_2744608 : Nat := 4983230072969 + 3 ^ 40 * 2744608 * 2
def baseEnd_2744608 : Nat := 939535408116868628185189

theorem tailTrace_2744608 : CollatzResearch.WordTrace tailWord_2744608 prefixEnd_2744608 939535408116868628185189 := by
  unfold tailWord_2744608
  simp only [CollatzResearch.WordTrace]
  refine ⟨50052038820380716286537239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66736051760507621715382985 50052038820380716286537239)
  ·
    refine ⟨75078058230571074429805859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50052038820380716286537239 75078058230571074429805859)
    ·
      refine ⟨112617087345856611644708789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75078058230571074429805859 112617087345856611644708789)
      ·
        refine ⟨10557851938674057341691449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112617087345856611644708789 10557851938674057341691449)
        ·
          refine ⟨7918388954005543006268587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10557851938674057341691449 7918388954005543006268587)
          ·
            refine ⟨11877583431008314509402881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7918388954005543006268587 11877583431008314509402881)
            ·
              refine ⟨8908187573256235882052161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11877583431008314509402881 8908187573256235882052161)
              ·
                refine ⟨6681140679942176911539121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8908187573256235882052161 6681140679942176911539121)
                ·
                  refine ⟨5010855509956632683654341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6681140679942176911539121 5010855509956632683654341)
                  ·
                    refine ⟨939535408116868628185189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5010855509956632683654341 939535408116868628185189)
                    ·
                      rfl

theorem cell22_2744608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_2744608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744608 prefixEnd_2744608 := by exact prefixLift 2744608
  have htrace : WordTrace (prefixWord ++ tailWord_2744608) baseStart_2744608 baseEnd_2744608 := by
    simpa [prefixWord, tailWord_2744608, baseEnd_2744608] using wordTrace_append hprefix tailTrace_2744608
  have hstable : (prefixWord ++ tailWord_2744608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744608).length < 2 ^ (prefixWord ++ tailWord_2744608).sum := by decide
  have hdescent : baseEnd_2744608 < baseStart_2744608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744610 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_2744610 : Nat := 118140960795 + 2744610 * 2 ^ 59
def prefixEnd_2744610 : Nat := 4983230072969 + 3 ^ 40 * 2744610 * 2
def baseEnd_2744610 : Nat := 939536092757741289635183

theorem tailTrace_2744610 : CollatzResearch.WordTrace tailWord_2744610 prefixEnd_2744610 939536092757741289635183 := by
  unfold tailWord_2744610
  simp only [CollatzResearch.WordTrace]
  refine ⟨25026037646688546728661821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66736100391169457943098189 25026037646688546728661821)
  ·
    refine ⟨9384764117508205023248183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25026037646688546728661821 9384764117508205023248183)
    ·
      refine ⟨14077146176262307534872275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9384764117508205023248183 14077146176262307534872275)
      ·
        refine ⟨21115719264393461302308413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14077146176262307534872275 21115719264393461302308413)
        ·
          refine ⟨7918394724147547988365655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21115719264393461302308413 7918394724147547988365655)
          ·
            refine ⟨11877592086221321982548483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7918394724147547988365655 11877592086221321982548483)
            ·
              refine ⟨17816388129331982973822725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11877592086221321982548483 17816388129331982973822725)
              ·
                refine ⟨3340572774249746807591761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17816388129331982973822725 3340572774249746807591761)
                ·
                  refine ⟨2505429580687310105693821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3340572774249746807591761 2505429580687310105693821)
                  ·
                    refine ⟨939536092757741289635183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2505429580687310105693821 939536092757741289635183)
                    ·
                      rfl

theorem cell22_2744610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_2744610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744610 prefixEnd_2744610 := by exact prefixLift 2744610
  have htrace : WordTrace (prefixWord ++ tailWord_2744610) baseStart_2744610 baseEnd_2744610 := by
    simpa [prefixWord, tailWord_2744610, baseEnd_2744610] using wordTrace_append hprefix tailTrace_2744610
  have hstable : (prefixWord ++ tailWord_2744610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744610).length < 2 ^ (prefixWord ++ tailWord_2744610).sum := by decide
  have hdescent : baseEnd_2744610 < baseStart_2744610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744612 : List Nat := [2, 3, 1, 3, 1, 4, 2, 2, 4]
def baseStart_2744612 : Nat := 118140960795 + 2744612 * 2 ^ 59
def prefixEnd_2744612 : Nat := 4983230072969 + 3 ^ 40 * 2744612 * 2
def baseEnd_2744612 : Nat := 313178925799537983695059

theorem tailTrace_2744612 : CollatzResearch.WordTrace tailWord_2744612 prefixEnd_2744612 313178925799537983695059 := by
  unfold tailWord_2744612
  simp only [CollatzResearch.WordTrace]
  refine ⟨50052111766373470628110045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66736149021831294170813393 50052111766373470628110045)
  ·
    refine ⟨18769541912390051485541267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50052111766373470628110045 18769541912390051485541267)
    ·
      refine ⟨28154312868585077228311901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18769541912390051485541267 28154312868585077228311901)
      ·
        refine ⟨10557867325719403960616963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28154312868585077228311901 10557867325719403960616963)
        ·
          refine ⟨15836800988579105940925445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10557867325719403960616963 15836800988579105940925445)
          ·
            refine ⟨2969400185358582363923521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15836800988579105940925445 2969400185358582363923521)
            ·
              refine ⟨2227050139018936772942641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969400185358582363923521 2227050139018936772942641)
              ·
                refine ⟨1670287604264202579706981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2227050139018936772942641 1670287604264202579706981)
                ·
                  refine ⟨313178925799537983695059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1670287604264202579706981 313178925799537983695059)
                  ·
                    rfl

theorem cell22_2744612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_2744612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744612 prefixEnd_2744612 := by exact prefixLift 2744612
  have htrace : WordTrace (prefixWord ++ tailWord_2744612) baseStart_2744612 baseEnd_2744612 := by
    simpa [prefixWord, tailWord_2744612, baseEnd_2744612] using wordTrace_append hprefix tailTrace_2744612
  have hstable : (prefixWord ++ tailWord_2744612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744612).length < 2 ^ (prefixWord ++ tailWord_2744612).sum := by decide
  have hdescent : baseEnd_2744612 < baseStart_2744612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744636 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_2744636 : Nat := 118140960795 + 2744636 * 2 ^ 59
def prefixEnd_2744636 : Nat := 4983230072969 + 3 ^ 40 * 2744636 * 2
def baseEnd_2744636 : Nat := 939544993089085888485103

theorem tailTrace_2744636 : CollatzResearch.WordTrace tailWord_2744636 prefixEnd_2744636 939544993089085888485103 := by
  unfold tailWord_2744636
  simp only [CollatzResearch.WordTrace]
  refine ⟨50052549442329996677546881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66736732589773328903395841 50052549442329996677546881)
  ·
    refine ⟨37539412081747497508160161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50052549442329996677546881 37539412081747497508160161)
    ·
      refine ⟨28154559061310623131120121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37539412081747497508160161 28154559061310623131120121)
      ·
        refine ⟨21115919295982967348340091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28154559061310623131120121 21115919295982967348340091)
        ·
          refine ⟨31673878943974451022510137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21115919295982967348340091 31673878943974451022510137)
          ·
            refine ⟨23755409207980838266882603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31673878943974451022510137 23755409207980838266882603)
            ·
              refine ⟨35633113811971257400323905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23755409207980838266882603 35633113811971257400323905)
              ·
                refine ⟨26724835358978443050242929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35633113811971257400323905 26724835358978443050242929)
                ·
                  refine ⟨20043626519233832287682197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26724835358978443050242929 20043626519233832287682197)
                  ·
                    refine ⟨939544993089085888485103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20043626519233832287682197 939544993089085888485103)
                    ·
                      rfl

theorem cell22_2744636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_2744636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744636 prefixEnd_2744636 := by exact prefixLift 2744636
  have htrace : WordTrace (prefixWord ++ tailWord_2744636) baseStart_2744636 baseEnd_2744636 := by
    simpa [prefixWord, tailWord_2744636, baseEnd_2744636] using wordTrace_append hprefix tailTrace_2744636
  have hstable : (prefixWord ++ tailWord_2744636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744636).length < 2 ^ (prefixWord ++ tailWord_2744636).sum := by decide
  have hdescent : baseEnd_2744636 < baseStart_2744636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744685 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 5]
def baseStart_2744685 : Nat := 118140960795 + 2744685 * 2 ^ 59
def prefixEnd_2744685 : Nat := 4983230072969 + 3 ^ 40 * 2744685 * 2
def baseEnd_2744685 : Nat := 313187255596822031336651

theorem tailTrace_2744685 : CollatzResearch.WordTrace tailWord_2744685 prefixEnd_2744685 313187255596822031336651 := by
  unfold tailWord_2744685
  simp only [CollatzResearch.WordTrace]
  refine ⟨100106886061482474723627509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66737924040988316482418339 100106886061482474723627509)
  ·
    refine ⟨9385020568263982005340079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100106886061482474723627509 9385020568263982005340079)
    ·
      refine ⟨14077530852395973008010119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9385020568263982005340079 14077530852395973008010119)
      ·
        refine ⟨21116296278593959512015179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14077530852395973008010119 21116296278593959512015179)
        ·
          refine ⟨31674444417890939268022769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21116296278593959512015179 31674444417890939268022769)
          ·
            refine ⟨23755833313418204451017077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31674444417890939268022769 23755833313418204451017077)
            ·
              refine ⟨2227109373132956667282851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23755833313418204451017077 2227109373132956667282851)
              ·
                refine ⟨3340664059699435000924277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227109373132956667282851 3340664059699435000924277)
                ·
                  refine ⟨313187255596822031336651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3340664059699435000924277 313187255596822031336651)
                  ·
                    rfl

theorem cell22_2744685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_2744685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744685 prefixEnd_2744685 := by exact prefixLift 2744685
  have htrace : WordTrace (prefixWord ++ tailWord_2744685) baseStart_2744685 baseEnd_2744685 := by
    simpa [prefixWord, tailWord_2744685, baseEnd_2744685] using wordTrace_append hprefix tailTrace_2744685
  have hstable : (prefixWord ++ tailWord_2744685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744685).length < 2 ^ (prefixWord ++ tailWord_2744685).sum := by decide
  have hdescent : baseEnd_2744685 < baseStart_2744685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744730 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 6]
def baseStart_2744730 : Nat := 118140960795 + 2744730 * 2 ^ 59
def prefixEnd_2744730 : Nat := 4983230072969 + 3 ^ 40 * 2744730 * 2
def baseEnd_2744730 : Nat := 313192390403366992211605

theorem tailTrace_2744730 : CollatzResearch.WordTrace tailWord_2744730 prefixEnd_2744730 313192390403366992211605 := by
  unfold tailWord_2744730
  simp only [CollatzResearch.WordTrace]
  refine ⟨25027131836579861852253911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66739018230879631606010429 25027131836579861852253911)
  ·
    refine ⟨37540697754869792778380867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25027131836579861852253911 37540697754869792778380867)
    ·
      refine ⟨56311046632304689167571301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37540697754869792778380867 56311046632304689167571301)
      ·
        refine ⟨10558321243557129218919619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56311046632304689167571301 10558321243557129218919619)
        ·
          refine ⟨15837481865335693828379429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10558321243557129218919619 15837481865335693828379429)
          ·
            refine ⟨2969527849750442592821143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15837481865335693828379429 2969527849750442592821143)
            ·
              refine ⟨4454291774625663889231715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969527849750442592821143 4454291774625663889231715)
              ·
                refine ⟨6681437661938495833847573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4454291774625663889231715 6681437661938495833847573)
                ·
                  refine ⟨313192390403366992211605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6681437661938495833847573 313192390403366992211605)
                  ·
                    rfl

theorem cell22_2744730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_2744730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744730 prefixEnd_2744730 := by exact prefixLift 2744730
  have htrace : WordTrace (prefixWord ++ tailWord_2744730) baseStart_2744730 baseEnd_2744730 := by
    simpa [prefixWord, tailWord_2744730, baseEnd_2744730] using wordTrace_append hprefix tailTrace_2744730
  have hstable : (prefixWord ++ tailWord_2744730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744730).length < 2 ^ (prefixWord ++ tailWord_2744730).sum := by decide
  have hdescent : baseEnd_2744730 < baseStart_2744730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744749 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_2744749 : Nat := 118140960795 + 2744749 * 2 ^ 59
def prefixEnd_2744749 : Nat := 4983230072969 + 3 ^ 40 * 2744749 * 2
def baseEnd_2744749 : Nat := 939583675298391260409757

theorem tailTrace_2744749 : CollatzResearch.WordTrace tailWord_2744749 prefixEnd_2744749 939583675298391260409757 := by
  unfold tailWord_2744749
  simp only [CollatzResearch.WordTrace]
  refine ⟨100109220333250613653957301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66739480222167075769304867 100109220333250613653957301)
  ·
    refine ⟨9385239406242245030058497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100109220333250613653957301 9385239406242245030058497)
    ·
      refine ⟨7038929554681683772543873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9385239406242245030058497 7038929554681683772543873)
      ·
        refine ⟨5279197166011262829407905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7038929554681683772543873 5279197166011262829407905)
        ·
          refine ⟨3959397874508447122055929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5279197166011262829407905 3959397874508447122055929)
          ·
            refine ⟨2969548405881335341541947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3959397874508447122055929 2969548405881335341541947)
            ·
              refine ⟨4454322608822003012312921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969548405881335341541947 4454322608822003012312921)
              ·
                refine ⟨3340741956616502259234691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4454322608822003012312921 3340741956616502259234691)
                ·
                  refine ⟨5011112934924753388852037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340741956616502259234691 5011112934924753388852037)
                  ·
                    refine ⟨939583675298391260409757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5011112934924753388852037 939583675298391260409757)
                    ·
                      rfl

theorem cell22_2744749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_2744749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744749 prefixEnd_2744749 := by exact prefixLift 2744749
  have htrace : WordTrace (prefixWord ++ tailWord_2744749) baseStart_2744749 baseEnd_2744749 := by
    simpa [prefixWord, tailWord_2744749, baseEnd_2744749] using wordTrace_append hprefix tailTrace_2744749
  have hstable : (prefixWord ++ tailWord_2744749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744749).length < 2 ^ (prefixWord ++ tailWord_2744749).sum := by decide
  have hdescent : baseEnd_2744749 < baseStart_2744749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744852 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2744852 : Nat := 118140960795 + 2744852 * 2 ^ 59
def prefixEnd_2744852 : Nat := 4983230072969 + 3 ^ 40 * 2744852 * 2
def baseEnd_2744852 : Nat := 939618934303333325084441

theorem tailTrace_2744852 : CollatzResearch.WordTrace tailWord_2744852 prefixEnd_2744852 939618934303333325084441 := by
  unfold tailWord_2744852
  simp only [CollatzResearch.WordTrace]
  refine ⟨50056488525938731122478405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66741984701251641496637873 50056488525938731122478405)
  ·
    refine ⟨9385591598613512085464701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50056488525938731122478405 9385591598613512085464701)
    ·
      refine ⟨3519596849480067032049263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9385591598613512085464701 3519596849480067032049263)
      ·
        refine ⟨5279395274220100548073895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519596849480067032049263 5279395274220100548073895)
        ·
          refine ⟨7919092911330150822110843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5279395274220100548073895 7919092911330150822110843)
          ·
            refine ⟨11878639366995226233166265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7919092911330150822110843 11878639366995226233166265)
            ·
              refine ⟨8908979525246419674874699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11878639366995226233166265 8908979525246419674874699)
              ·
                refine ⟨13363469287869629512312049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8908979525246419674874699 13363469287869629512312049)
                ·
                  refine ⟨10022601965902222134234037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13363469287869629512312049 10022601965902222134234037)
                  ·
                    refine ⟨939618934303333325084441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10022601965902222134234037 939618934303333325084441)
                    ·
                      rfl

theorem cell22_2744852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2744852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744852 prefixEnd_2744852 := by exact prefixLift 2744852
  have htrace : WordTrace (prefixWord ++ tailWord_2744852) baseStart_2744852 baseEnd_2744852 := by
    simpa [prefixWord, tailWord_2744852, baseEnd_2744852] using wordTrace_append hprefix tailTrace_2744852
  have hstable : (prefixWord ++ tailWord_2744852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744852).length < 2 ^ (prefixWord ++ tailWord_2744852).sum := by decide
  have hdescent : baseEnd_2744852 < baseStart_2744852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744867 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 1, 4]
def baseStart_2744867 : Nat := 118140960795 + 2744867 * 2 ^ 59
def prefixEnd_2744867 : Nat := 4983230072969 + 3 ^ 40 * 2744867 * 2
def baseEnd_2744867 : Nat := 939624069109878285959395

theorem tailTrace_2744867 : CollatzResearch.WordTrace tailWord_2744867 prefixEnd_2744867 939624069109878285959395 := by
  unfold tailWord_2744867
  simp only [CollatzResearch.WordTrace]
  refine ⟨100113524146823119806752855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66742349431215413204501903 100113524146823119806752855)
  ·
    refine ⟨150170286220234679710129283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100113524146823119806752855 150170286220234679710129283)
    ·
      refine ⟨225255429330352019565193925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150170286220234679710129283 225255429330352019565193925)
      ·
        refine ⟨42235392999441003668473861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225255429330352019565193925 42235392999441003668473861)
        ·
          refine ⟨7919136187395188187838849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42235392999441003668473861 7919136187395188187838849)
          ·
            refine ⟨5939352140546391140879137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7919136187395188187838849 5939352140546391140879137)
            ·
              refine ⟨4454514105409793355659353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5939352140546391140879137 4454514105409793355659353)
              ·
                refine ⟨3340885579057345016744515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4454514105409793355659353 3340885579057345016744515)
                ·
                  refine ⟨5011328368586017525116773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340885579057345016744515 5011328368586017525116773)
                  ·
                    refine ⟨939624069109878285959395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5011328368586017525116773 939624069109878285959395)
                    ·
                      rfl

theorem cell22_2744867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 4].length) (baseStart_2744867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744867 prefixEnd_2744867 := by exact prefixLift 2744867
  have htrace : WordTrace (prefixWord ++ tailWord_2744867) baseStart_2744867 baseEnd_2744867 := by
    simpa [prefixWord, tailWord_2744867, baseEnd_2744867] using wordTrace_append hprefix tailTrace_2744867
  have hstable : (prefixWord ++ tailWord_2744867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744867).length < 2 ^ (prefixWord ++ tailWord_2744867).sum := by decide
  have hdescent : baseEnd_2744867 < baseStart_2744867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744880 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 4, 3]
def baseStart_2744880 : Nat := 118140960795 + 2744880 * 2 ^ 59
def prefixEnd_2744880 : Nat := 4983230072969 + 3 ^ 40 * 2744880 * 2
def baseEnd_2744880 : Nat := 939628519275550585384355

theorem tailTrace_2744880 : CollatzResearch.WordTrace tailWord_2744880 prefixEnd_2744880 939628519275550585384355 := by
  unfold tailWord_2744880
  simp only [CollatzResearch.WordTrace]
  refine ⟨50056999147888011513488047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66742665530517348684650729 50056999147888011513488047)
  ·
    refine ⟨75085498721832017270232071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50056999147888011513488047 75085498721832017270232071)
    ·
      refine ⟨112628248082748025905348107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75085498721832017270232071 112628248082748025905348107)
      ·
        refine ⟨168942372124122038858022161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112628248082748025905348107 168942372124122038858022161)
        ·
          refine ⟨126706779093091529143516621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168942372124122038858022161 126706779093091529143516621)
          ·
            refine ⟨47515042159909323428818733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126706779093091529143516621 47515042159909323428818733)
            ·
              refine ⟨17818140809965996285807025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47515042159909323428818733 17818140809965996285807025)
              ·
                refine ⟨13363605607474497214355269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17818140809965996285807025 13363605607474497214355269)
                ·
                  refine ⟨2505676051401468227691613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13363605607474497214355269 2505676051401468227691613)
                  ·
                    refine ⟨939628519275550585384355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2505676051401468227691613 939628519275550585384355)
                    ·
                      rfl

theorem cell22_2744880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4, 3].length) (baseStart_2744880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744880 prefixEnd_2744880 := by exact prefixLift 2744880
  have htrace : WordTrace (prefixWord ++ tailWord_2744880) baseStart_2744880 baseEnd_2744880 := by
    simpa [prefixWord, tailWord_2744880, baseEnd_2744880] using wordTrace_append hprefix tailTrace_2744880
  have hstable : (prefixWord ++ tailWord_2744880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744880).length < 2 ^ (prefixWord ++ tailWord_2744880).sum := by decide
  have hdescent : baseEnd_2744880 < baseStart_2744880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744882 : List Nat := [3, 2, 1, 1, 2, 1, 5, 3, 4]
def baseStart_2744882 : Nat := 118140960795 + 2744882 * 2 ^ 59
def prefixEnd_2744882 : Nat := 4983230072969 + 3 ^ 40 * 2744882 * 2
def baseEnd_2744882 : Nat := 313209734638807748944783

theorem tailTrace_2744882 : CollatzResearch.WordTrace tailWord_2744882 prefixEnd_2744882 313209734638807748944783 := by
  unfold tailWord_2744882
  simp only [CollatzResearch.WordTrace]
  refine ⟨25028517810442194342137225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66742714161179184912365933 25028517810442194342137225)
  ·
    refine ⟨18771388357831645756602919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25028517810442194342137225 18771388357831645756602919)
    ·
      refine ⟨28157082536747468634904379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18771388357831645756602919 28157082536747468634904379)
      ·
        refine ⟨42235623805121202952356569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28157082536747468634904379 42235623805121202952356569)
        ·
          refine ⟨31676717853840902214267427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42235623805121202952356569 31676717853840902214267427)
          ·
            refine ⟨47515076780761353321401141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31676717853840902214267427 47515076780761353321401141)
            ·
              refine ⟨4454538448196376873881357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47515076780761353321401141 4454538448196376873881357)
              ·
                refine ⟨1670451918073641327705509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4454538448196376873881357 1670451918073641327705509)
                ·
                  refine ⟨313209734638807748944783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1670451918073641327705509 313209734638807748944783)
                  ·
                    rfl

theorem cell22_2744882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_2744882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744882 prefixEnd_2744882 := by exact prefixLift 2744882
  have htrace : WordTrace (prefixWord ++ tailWord_2744882) baseStart_2744882 baseEnd_2744882 := by
    simpa [prefixWord, tailWord_2744882, baseEnd_2744882] using wordTrace_append hprefix tailTrace_2744882
  have hstable : (prefixWord ++ tailWord_2744882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744882).length < 2 ^ (prefixWord ++ tailWord_2744882).sum := by decide
  have hdescent : baseEnd_2744882 < baseStart_2744882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744895 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 2, 4]
def baseStart_2744895 : Nat := 118140960795 + 2744895 * 2 ^ 59
def prefixEnd_2744895 : Nat := 4983230072969 + 3 ^ 40 * 2744895 * 2
def baseEnd_2744895 : Nat := 939633654082095546259309

theorem tailTrace_2744895 : CollatzResearch.WordTrace tailWord_2744895 prefixEnd_2744895 939633654082095546259309 := by
  unfold tailWord_2744895
  simp only [CollatzResearch.WordTrace]
  refine ⟨100114545390721680588772139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66743030260481120392514759 100114545390721680588772139)
  ·
    refine ⟨150171818086082520883158209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100114545390721680588772139 150171818086082520883158209)
    ·
      refine ⟨112628863564561890662368657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150171818086082520883158209 112628863564561890662368657)
      ·
        refine ⟨84471647673421417996776493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112628863564561890662368657 84471647673421417996776493)
        ·
          refine ⟨31676867877533031748791185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84471647673421417996776493 31676867877533031748791185)
          ·
            refine ⟨23757650908149773811593389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31676867877533031748791185 23757650908149773811593389)
            ·
              refine ⟨8909119090556165179347521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23757650908149773811593389 8909119090556165179347521)
              ·
                refine ⟨6681839317917123884510641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8909119090556165179347521 6681839317917123884510641)
                ·
                  refine ⟨5011379488437842913382981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6681839317917123884510641 5011379488437842913382981)
                  ·
                    refine ⟨939633654082095546259309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5011379488437842913382981 939633654082095546259309)
                    ·
                      rfl

theorem cell22_2744895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_2744895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744895 prefixEnd_2744895 := by exact prefixLift 2744895
  have htrace : WordTrace (prefixWord ++ tailWord_2744895) baseStart_2744895 baseEnd_2744895 := by
    simpa [prefixWord, tailWord_2744895, baseEnd_2744895] using wordTrace_append hprefix tailTrace_2744895
  have hstable : (prefixWord ++ tailWord_2744895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744895).length < 2 ^ (prefixWord ++ tailWord_2744895).sum := by decide
  have hdescent : baseEnd_2744895 < baseStart_2744895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744897 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 4, 3]
def baseStart_2744897 : Nat := 118140960795 + 2744897 * 2 ^ 59
def prefixEnd_2744897 : Nat := 4983230072969 + 3 ^ 40 * 2744897 * 2
def baseEnd_2744897 : Nat := 939634338722968207709303

theorem tailTrace_2744897 : CollatzResearch.WordTrace tailWord_2744897 prefixEnd_2744897 939634338722968207709303 := by
  unfold tailWord_2744897
  simp only [CollatzResearch.WordTrace]
  refine ⟨100114618336714434930344945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66743078891142956620229963 100114618336714434930344945)
  ·
    refine ⟨75085963752535826197758709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100114618336714434930344945 75085963752535826197758709)
    ·
      refine ⟨7039309101800233706039879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75085963752535826197758709 7039309101800233706039879)
      ·
        refine ⟨10558963652700350559059819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7039309101800233706039879 10558963652700350559059819)
        ·
          refine ⟨15838445479050525838589729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10558963652700350559059819 15838445479050525838589729)
          ·
            refine ⟨11878834109287894378942297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15838445479050525838589729 11878834109287894378942297)
            ·
              refine ⟨8909125581965920784206723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11878834109287894378942297 8909125581965920784206723)
              ·
                refine ⟨13363688372948881176310085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8909125581965920784206723 13363688372948881176310085)
                ·
                  refine ⟨2505691569927915220558141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13363688372948881176310085 2505691569927915220558141)
                  ·
                    refine ⟨939634338722968207709303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2505691569927915220558141 939634338722968207709303)
                    ·
                      rfl

theorem cell22_2744897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_2744897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744897 prefixEnd_2744897 := by exact prefixLift 2744897
  have htrace : WordTrace (prefixWord ++ tailWord_2744897) baseStart_2744897 baseEnd_2744897 := by
    simpa [prefixWord, tailWord_2744897, baseEnd_2744897] using wordTrace_append hprefix tailTrace_2744897
  have hstable : (prefixWord ++ tailWord_2744897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744897).length < 2 ^ (prefixWord ++ tailWord_2744897).sum := by decide
  have hdescent : baseEnd_2744897 < baseStart_2744897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2744985 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 3, 4]
def baseStart_2744985 : Nat := 118140960795 + 2744985 * 2 ^ 59
def prefixEnd_2744985 : Nat := 4983230072969 + 3 ^ 40 * 2744985 * 2
def baseEnd_2744985 : Nat := 939664462921365311509033

theorem tailTrace_2744985 : CollatzResearch.WordTrace tailWord_2744985 prefixEnd_2744985 939664462921365311509033 := by
  unfold tailWord_2744985
  simp only [CollatzResearch.WordTrace]
  refine ⟨100117827960395625959548409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66745218640263750639698939 100117827960395625959548409)
  ·
    refine ⟨75088370970296719469661307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100117827960395625959548409 75088370970296719469661307)
    ·
      refine ⟨112632556455445079204491961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75088370970296719469661307 112632556455445079204491961)
      ·
        refine ⟨84474417341583809403368971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112632556455445079204491961 84474417341583809403368971)
        ·
          refine ⟨126711626012375714105053457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84474417341583809403368971 126711626012375714105053457)
          ·
            refine ⟨95033719509281785578790093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126711626012375714105053457 95033719509281785578790093)
            ·
              refine ⟨35637644815980669592046285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95033719509281785578790093 35637644815980669592046285)
              ·
                refine ⟨13364116805992751097017357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35637644815980669592046285 13364116805992751097017357)
                ·
                  refine ⟨5011543802247281661381509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13364116805992751097017357 5011543802247281661381509)
                  ·
                    refine ⟨939664462921365311509033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5011543802247281661381509 939664462921365311509033)
                    ·
                      rfl

theorem cell22_2744985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_2744985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2744985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2744985 prefixEnd_2744985 := by exact prefixLift 2744985
  have htrace : WordTrace (prefixWord ++ tailWord_2744985) baseStart_2744985 baseEnd_2744985 := by
    simpa [prefixWord, tailWord_2744985, baseEnd_2744985] using wordTrace_append hprefix tailTrace_2744985
  have hstable : (prefixWord ++ tailWord_2744985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2744985).length < 2 ^ (prefixWord ++ tailWord_2744985).sum := by decide
  have hdescent : baseEnd_2744985 < baseStart_2744985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2744985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745006 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_2745006 : Nat := 118140960795 + 2745006 * 2 ^ 59
def prefixEnd_2745006 : Nat := 4983230072969 + 3 ^ 40 * 2745006 * 2
def baseEnd_2745006 : Nat := 313223883883509418911323

theorem tailTrace_2745006 : CollatzResearch.WordTrace tailWord_2745006 prefixEnd_2745006 313223883883509418911323 := by
  unfold tailWord_2745006
  simp only [CollatzResearch.WordTrace]
  refine ⟨12514824236664943318257859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66745729262213031030708581 12514824236664943318257859)
  ·
    refine ⟨18772236354997414977386789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12514824236664943318257859 18772236354997414977386789)
    ·
      refine ⟨3519794316562015308260023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18772236354997414977386789 3519794316562015308260023)
      ·
        refine ⟨5279691474843022962390035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519794316562015308260023 5279691474843022962390035)
        ·
          refine ⟨7919537212264534443585053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5279691474843022962390035 7919537212264534443585053)
          ·
            refine ⟨2969826454599200416344395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7919537212264534443585053 2969826454599200416344395)
            ·
              refine ⟨4454739681898800624516593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969826454599200416344395 4454739681898800624516593)
              ·
                refine ⟨3341054761424100468387445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4454739681898800624516593 3341054761424100468387445)
                ·
                  refine ⟨313223883883509418911323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3341054761424100468387445 313223883883509418911323)
                  ·
                    rfl

theorem cell22_2745006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_2745006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745006 prefixEnd_2745006 := by exact prefixLift 2745006
  have htrace : WordTrace (prefixWord ++ tailWord_2745006) baseStart_2745006 baseEnd_2745006 := by
    simpa [prefixWord, tailWord_2745006, baseEnd_2745006] using wordTrace_append hprefix tailTrace_2745006
  have hstable : (prefixWord ++ tailWord_2745006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745006).length < 2 ^ (prefixWord ++ tailWord_2745006).sum := by decide
  have hdescent : baseEnd_2745006 < baseStart_2745006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745032 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 1, 5]
def baseStart_2745032 : Nat := 118140960795 + 2745032 * 2 ^ 59
def prefixEnd_2745032 : Nat := 4983230072969 + 3 ^ 40 * 2745032 * 2
def baseEnd_2745032 : Nat := 939680551981872855583889

theorem tailTrace_2745032 : CollatzResearch.WordTrace tailWord_2745032 prefixEnd_2745032 939680551981872855583889 := by
  unfold tailWord_2745032
  simp only [CollatzResearch.WordTrace]
  refine ⟨50059771095612676493254675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66746361460816901991006233 50059771095612676493254675)
  ·
    refine ⟨75089656643419014739882013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50059771095612676493254675 75089656643419014739882013)
    ·
      refine ⟨28158621241282130527455755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75089656643419014739882013 28158621241282130527455755)
      ·
        refine ⟨42237931861923195791183633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28158621241282130527455755 42237931861923195791183633)
        ·
          refine ⟨31678448896442396843387725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42237931861923195791183633 31678448896442396843387725)
          ·
            refine ⟨11879418336165898816270397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31678448896442396843387725 11879418336165898816270397)
            ·
              refine ⟨4454781876062212056101399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11879418336165898816270397 4454781876062212056101399)
              ·
                refine ⟨6682172814093318084152099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4454781876062212056101399 6682172814093318084152099)
                ·
                  refine ⟨10023259221139977126228149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6682172814093318084152099 10023259221139977126228149)
                  ·
                    refine ⟨939680551981872855583889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10023259221139977126228149 939680551981872855583889)
                    ·
                      rfl

theorem cell22_2745032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_2745032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745032 prefixEnd_2745032 := by exact prefixLift 2745032
  have htrace : WordTrace (prefixWord ++ tailWord_2745032) baseStart_2745032 baseEnd_2745032 := by
    simpa [prefixWord, tailWord_2745032, baseEnd_2745032] using wordTrace_append hprefix tailTrace_2745032
  have hstable : (prefixWord ++ tailWord_2745032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745032).length < 2 ^ (prefixWord ++ tailWord_2745032).sum := by decide
  have hdescent : baseEnd_2745032 < baseStart_2745032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745064 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 2, 4]
def baseStart_2745064 : Nat := 118140960795 + 2745064 * 2 ^ 59
def prefixEnd_2745064 : Nat := 4983230072969 + 3 ^ 40 * 2745064 * 2
def baseEnd_2745064 : Nat := 939691506235835438783791

theorem tailTrace_2745064 : CollatzResearch.WordTrace tailWord_2745064 prefixEnd_2745064 939691506235835438783791 := by
  unfold tailWord_2745064
  simp only [CollatzResearch.WordTrace]
  refine ⟨50060354663554711225837123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66747139551406281634449497 50060354663554711225837123)
  ·
    refine ⟨75090531995332066838755685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50060354663554711225837123 75090531995332066838755685)
    ·
      refine ⟨14079474749124762532266691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75090531995332066838755685 14079474749124762532266691)
      ·
        refine ⟨21119212123687143798400037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14079474749124762532266691 21119212123687143798400037)
        ·
          refine ⟨3959852273191339462200007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21119212123687143798400037 3959852273191339462200007)
          ·
            refine ⟨5939778409787009193300011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959852273191339462200007 5939778409787009193300011)
            ·
              refine ⟨8909667614680513789950017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5939778409787009193300011 8909667614680513789950017)
              ·
                refine ⟨6682250711010385342462513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8909667614680513789950017 6682250711010385342462513)
                ·
                  refine ⟨5011688033257789006846885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6682250711010385342462513 5011688033257789006846885)
                  ·
                    refine ⟨939691506235835438783791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5011688033257789006846885 939691506235835438783791)
                    ·
                      rfl

theorem cell22_2745064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_2745064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745064 prefixEnd_2745064 := by exact prefixLift 2745064
  have htrace : WordTrace (prefixWord ++ tailWord_2745064) baseStart_2745064 baseEnd_2745064 := by
    simpa [prefixWord, tailWord_2745064, baseEnd_2745064] using wordTrace_append hprefix tailTrace_2745064
  have hstable : (prefixWord ++ tailWord_2745064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745064).length < 2 ^ (prefixWord ++ tailWord_2745064).sum := by decide
  have hdescent : baseEnd_2745064 < baseStart_2745064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745075 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 2, 6]
def baseStart_2745075 : Nat := 118140960795 + 2745075 * 2 ^ 59
def prefixEnd_2745075 : Nat := 4983230072969 + 3 ^ 40 * 2745075 * 2
def baseEnd_2745075 : Nat := 939695271760635076758757

theorem tailTrace_2745075 : CollatzResearch.WordTrace tailWord_2745075 prefixEnd_2745075 939695271760635076758757 := by
  unfold tailWord_2745075
  simp only [CollatzResearch.WordTrace]
  refine ⟨100121110530069571330324679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66747407020046380886883119 100121110530069571330324679)
  ·
    refine ⟨150181665795104356995487019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100121110530069571330324679 150181665795104356995487019)
    ·
      refine ⟨225272498692656535493230529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150181665795104356995487019 225272498692656535493230529)
      ·
        refine ⟨168954374019492401619922897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225272498692656535493230529 168954374019492401619922897)
        ·
          refine ⟨126715780514619301214942173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168954374019492401619922897 126715780514619301214942173)
          ·
            refine ⟨47518417692982237955603315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126715780514619301214942173 47518417692982237955603315)
            ·
              refine ⟨71277626539473356933404973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47518417692982237955603315 71277626539473356933404973)
              ·
                refine ⟨26729109952302508850026865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71277626539473356933404973 26729109952302508850026865)
                ·
                  refine ⟨20046832464226881637520149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26729109952302508850026865 20046832464226881637520149)
                  ·
                    refine ⟨939695271760635076758757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20046832464226881637520149 939695271760635076758757)
                    ·
                      rfl

theorem cell22_2745075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_2745075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745075 prefixEnd_2745075 := by exact prefixLift 2745075
  have htrace : WordTrace (prefixWord ++ tailWord_2745075) baseStart_2745075 baseEnd_2745075 := by
    simpa [prefixWord, tailWord_2745075, baseEnd_2745075] using wordTrace_append hprefix tailTrace_2745075
  have hstable : (prefixWord ++ tailWord_2745075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745075).length < 2 ^ (prefixWord ++ tailWord_2745075).sum := by decide
  have hdescent : baseEnd_2745075 < baseStart_2745075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745137 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 5, 4]
def baseStart_2745137 : Nat := 118140960795 + 2745137 * 2 ^ 59
def prefixEnd_2745137 : Nat := 4983230072969 + 3 ^ 40 * 2745137 * 2
def baseEnd_2745137 : Nat := 939716495627687581708567

theorem tailTrace_2745137 : CollatzResearch.WordTrace tailWord_2745137 prefixEnd_2745137 939716495627687581708567 := by
  unfold tailWord_2745137
  simp only [CollatzResearch.WordTrace]
  refine ⟨100123371855844955919081665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66748914570563303946054443 100123371855844955919081665)
  ·
    refine ⟨75092528891883716939311249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100123371855844955919081665 75092528891883716939311249)
    ·
      refine ⟨56319396668912787704483437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75092528891883716939311249 56319396668912787704483437)
      ·
        refine ⟨21119773750842295389181289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56319396668912787704483437 21119773750842295389181289)
        ·
          refine ⟨15839830313131721541885967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21119773750842295389181289 15839830313131721541885967)
          ·
            refine ⟨23759745469697582312828951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15839830313131721541885967 23759745469697582312828951)
            ·
              refine ⟨35639618204546373469243427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23759745469697582312828951 35639618204546373469243427)
              ·
                refine ⟨53459427306819560203865141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35639618204546373469243427 53459427306819560203865141)
                ·
                  refine ⟨5011821310014333769112357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53459427306819560203865141 5011821310014333769112357)
                  ·
                    refine ⟨939716495627687581708567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5011821310014333769112357 939716495627687581708567)
                    ·
                      rfl

theorem cell22_2745137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_2745137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745137 prefixEnd_2745137 := by exact prefixLift 2745137
  have htrace : WordTrace (prefixWord ++ tailWord_2745137) baseStart_2745137 baseEnd_2745137 := by
    simpa [prefixWord, tailWord_2745137, baseEnd_2745137] using wordTrace_append hprefix tailTrace_2745137
  have hstable : (prefixWord ++ tailWord_2745137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745137).length < 2 ^ (prefixWord ++ tailWord_2745137).sum := by decide
  have hdescent : baseEnd_2745137 < baseStart_2745137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745184 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 4, 3]
def baseStart_2745184 : Nat := 118140960795 + 2745184 * 2 ^ 59
def prefixEnd_2745184 : Nat := 4983230072969 + 3 ^ 40 * 2745184 * 2
def baseEnd_2745184 : Nat := 939732584688195125783423

theorem tailTrace_2745184 : CollatzResearch.WordTrace tailWord_2745184 prefixEnd_2745184 939732584688195125783423 := by
  unfold tailWord_2745184
  simp only [CollatzResearch.WordTrace]
  refine ⟨50062543043337341473021303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66750057391116455297361737 50062543043337341473021303)
  ·
    refine ⟨75093814565006012209531955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50062543043337341473021303 75093814565006012209531955)
    ·
      refine ⟨112640721847509018314297933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75093814565006012209531955 112640721847509018314297933)
      ·
        refine ⟨42240270692815881867861725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112640721847509018314297933 42240270692815881867861725)
        ·
          refine ⟨15840101509805955700448147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42240270692815881867861725 15840101509805955700448147)
          ·
            refine ⟨23760152264708933550672221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15840101509805955700448147 23760152264708933550672221)
            ·
              refine ⟨8910057099265850081502083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23760152264708933550672221 8910057099265850081502083)
              ·
                refine ⟨13365085648898775122253125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8910057099265850081502083 13365085648898775122253125)
                ·
                  refine ⟨2505953559168520335422461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13365085648898775122253125 2505953559168520335422461)
                  ·
                    refine ⟨939732584688195125783423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2505953559168520335422461 939732584688195125783423)
                    ·
                      rfl

theorem cell22_2745184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4, 3].length) (baseStart_2745184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745184 prefixEnd_2745184 := by exact prefixLift 2745184
  have htrace : WordTrace (prefixWord ++ tailWord_2745184) baseStart_2745184 baseEnd_2745184 := by
    simpa [prefixWord, tailWord_2745184, baseEnd_2745184] using wordTrace_append hprefix tailTrace_2745184
  have hstable : (prefixWord ++ tailWord_2745184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745184).length < 2 ^ (prefixWord ++ tailWord_2745184).sum := by decide
  have hdescent : baseEnd_2745184 < baseStart_2745184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745186 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_2745186 : Nat := 118140960795 + 2745186 * 2 ^ 59
def prefixEnd_2745186 : Nat := 4983230072969 + 3 ^ 40 * 2745186 * 2
def baseEnd_2745186 : Nat := 313244423109689262411139

theorem tailTrace_2745186 : CollatzResearch.WordTrace tailWord_2745186 prefixEnd_2745186 313244423109689262411139 := by
  unfold tailWord_2745186
  simp only [CollatzResearch.WordTrace]
  refine ⟨25031289758166859321903853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66750106021778291525076941 25031289758166859321903853)
  ·
    refine ⟨9386733659312572245713945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25031289758166859321903853 9386733659312572245713945)
    ·
      refine ⟨7040050244484429184285459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9386733659312572245713945 7040050244484429184285459)
      ·
        refine ⟨10560075366726643776428189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7040050244484429184285459 10560075366726643776428189)
        ·
          refine ⟨3960028262522491416160571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10560075366726643776428189 3960028262522491416160571)
          ·
            refine ⟨5940042393783737124240857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3960028262522491416160571 5940042393783737124240857)
            ·
              refine ⟨4455031795337802843180643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5940042393783737124240857 4455031795337802843180643)
              ·
                refine ⟨6682547693006704264770965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4455031795337802843180643 6682547693006704264770965)
                ·
                  refine ⟨313244423109689262411139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6682547693006704264770965 313244423109689262411139)
                  ·
                    rfl

theorem cell22_2745186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_2745186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745186 prefixEnd_2745186 := by exact prefixLift 2745186
  have htrace : WordTrace (prefixWord ++ tailWord_2745186) baseStart_2745186 baseEnd_2745186 := by
    simpa [prefixWord, tailWord_2745186, baseEnd_2745186] using wordTrace_append hprefix tailTrace_2745186
  have hstable : (prefixWord ++ tailWord_2745186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745186).length < 2 ^ (prefixWord ++ tailWord_2745186).sum := by decide
  have hdescent : baseEnd_2745186 < baseStart_2745186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745197 : List Nat := [1, 5, 1, 1, 1, 1, 1, 11]
def baseStart_2745197 : Nat := 118140960795 + 2745197 * 2 ^ 59
def prefixEnd_2745197 : Nat := 4983230072969 + 3 ^ 40 * 2745197 * 2
def baseEnd_2745197 : Nat := 104415226094874158356487

theorem tailTrace_2745197 : CollatzResearch.WordTrace tailWord_2745197 prefixEnd_2745197 104415226094874158356487 := by
  unfold tailWord_2745197
  simp only [CollatzResearch.WordTrace]
  refine ⟨100125560235627586166265845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66750373490418390777510563 100125560235627586166265845)
  ·
    refine ⟨9386771272090086203087423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100125560235627586166265845 9386771272090086203087423)
    ·
      refine ⟨14080156908135129304631135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9386771272090086203087423 14080156908135129304631135)
      ·
        refine ⟨21120235362202693956946703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14080156908135129304631135 21120235362202693956946703)
        ·
          refine ⟨31680353043304040935420055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21120235362202693956946703 31680353043304040935420055)
          ·
            refine ⟨47520529564956061403130083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31680353043304040935420055 47520529564956061403130083)
            ·
              refine ⟨71280794347434092104695125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47520529564956061403130083 71280794347434092104695125)
              ·
                refine ⟨104415226094874158356487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 71280794347434092104695125 104415226094874158356487)
                ·
                  rfl

theorem cell22_2745197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 11].length) (baseStart_2745197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745197 prefixEnd_2745197 := by exact prefixLift 2745197
  have htrace : WordTrace (prefixWord ++ tailWord_2745197) baseStart_2745197 baseEnd_2745197 := by
    simpa [prefixWord, tailWord_2745197, baseEnd_2745197] using wordTrace_append hprefix tailTrace_2745197
  have hstable : (prefixWord ++ tailWord_2745197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745197).length < 2 ^ (prefixWord ++ tailWord_2745197).sum := by decide
  have hdescent : baseEnd_2745197 < baseStart_2745197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745257 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_2745257 : Nat := 118140960795 + 2745257 * 2 ^ 59
def prefixEnd_2745257 : Nat := 4983230072969 + 3 ^ 40 * 2745257 * 2
def baseEnd_2745257 : Nat := 939757574080047268708199

theorem tailTrace_2745257 : CollatzResearch.WordTrace tailWord_2745257 prefixEnd_2745257 939757574080047268708199 := by
  unfold tailWord_2745257
  simp only [CollatzResearch.WordTrace]
  refine ⟨100127748615410216413450025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66751832410273477608966683 100127748615410216413450025)
  ·
    refine ⟨75095811461557662310087519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100127748615410216413450025 75095811461557662310087519)
    ·
      refine ⟨112643717192336493465131279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75095811461557662310087519 112643717192336493465131279)
      ·
        refine ⟨168965575788504740197696919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112643717192336493465131279 168965575788504740197696919)
        ·
          refine ⟨253448363682757110296545379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168965575788504740197696919 253448363682757110296545379)
          ·
            refine ⟨380172545524135665444818069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253448363682757110296545379 380172545524135665444818069)
            ·
              refine ⟨17820588071443859317725847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 380172545524135665444818069 17820588071443859317725847)
              ·
                refine ⟨26730882107165788976588771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17820588071443859317725847 26730882107165788976588771)
                ·
                  refine ⟨40096323160748683464883157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26730882107165788976588771 40096323160748683464883157)
                  ·
                    refine ⟨939757574080047268708199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40096323160748683464883157 939757574080047268708199)
                    ·
                      rfl

theorem cell22_2745257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_2745257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745257 prefixEnd_2745257 := by exact prefixLift 2745257
  have htrace : WordTrace (prefixWord ++ tailWord_2745257) baseStart_2745257 baseEnd_2745257 := by
    simpa [prefixWord, tailWord_2745257, baseEnd_2745257] using wordTrace_append hprefix tailTrace_2745257
  have hstable : (prefixWord ++ tailWord_2745257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745257).length < 2 ^ (prefixWord ++ tailWord_2745257).sum := by decide
  have hdescent : baseEnd_2745257 < baseStart_2745257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745381 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 3, 3]
def baseStart_2745381 : Nat := 118140960795 + 2745381 * 2 ^ 59
def prefixEnd_2745381 : Nat := 4983230072969 + 3 ^ 40 * 2745381 * 2
def baseEnd_2745381 : Nat := 939800021814152278607819

theorem tailTrace_2745381 : CollatzResearch.WordTrace tailWord_2745381 prefixEnd_2745381 939800021814152278607819 := by
  unfold tailWord_2745381
  simp only [CollatzResearch.WordTrace]
  refine ⟨100132271266960985590963997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66754847511307323727309331 100132271266960985590963997)
  ·
    refine ⟨37549601725110369596611499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100132271266960985590963997 37549601725110369596611499)
    ·
      refine ⟨56324402587665554394917249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37549601725110369596611499 56324402587665554394917249)
      ·
        refine ⟨42243301940749165796187937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56324402587665554394917249 42243301940749165796187937)
        ·
          refine ⟨31682476455561874347140953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42243301940749165796187937 31682476455561874347140953)
          ·
            refine ⟨23761857341671405760355715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31682476455561874347140953 23761857341671405760355715)
            ·
              refine ⟨35642786012507108640533573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23761857341671405760355715 35642786012507108640533573)
              ·
                refine ⟨6683022377345082870100045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35642786012507108640533573 6683022377345082870100045)
                ·
                  refine ⟨2506133391504406076287517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6683022377345082870100045 2506133391504406076287517)
                  ·
                    refine ⟨939800021814152278607819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2506133391504406076287517 939800021814152278607819)
                    ·
                      rfl

theorem cell22_2745381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_2745381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745381 prefixEnd_2745381 := by exact prefixLift 2745381
  have htrace : WordTrace (prefixWord ++ tailWord_2745381) baseStart_2745381 baseEnd_2745381 := by
    simpa [prefixWord, tailWord_2745381, baseEnd_2745381] using wordTrace_append hprefix tailTrace_2745381
  have hstable : (prefixWord ++ tailWord_2745381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745381).length < 2 ^ (prefixWord ++ tailWord_2745381).sum := by decide
  have hdescent : baseEnd_2745381 < baseStart_2745381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745383 : List Nat := [1, 1, 7, 1, 1, 1, 4, 6]
def baseStart_2745383 : Nat := 118140960795 + 2745383 * 2 ^ 59
def prefixEnd_2745383 : Nat := 4983230072969 + 3 ^ 40 * 2745383 * 2
def baseEnd_2745383 : Nat := 104422300717224993339757

theorem tailTrace_2745383 : CollatzResearch.WordTrace tailWord_2745383 prefixEnd_2745383 104422300717224993339757 := by
  unfold tailWord_2745383
  simp only [CollatzResearch.WordTrace]
  refine ⟨100132344212953739932536803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66754896141969159955024535 100132344212953739932536803)
  ·
    refine ⟨150198516319430609898805205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100132344212953739932536803 150198516319430609898805205)
    ·
      refine ⟨3520277726236654919503247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 150198516319430609898805205 3520277726236654919503247)
      ·
        refine ⟨5280416589354982379254871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520277726236654919503247 5280416589354982379254871)
        ·
          refine ⟨7920624884032473568882307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5280416589354982379254871 7920624884032473568882307)
          ·
            refine ⟨11880937326048710353323461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7920624884032473568882307 11880937326048710353323461)
            ·
              refine ⟨2227675748634133191248149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11880937326048710353323461 2227675748634133191248149)
              ·
                refine ⟨104422300717224993339757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2227675748634133191248149 104422300717224993339757)
                ·
                  rfl

theorem cell22_2745383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 6].length) (baseStart_2745383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745383 prefixEnd_2745383 := by exact prefixLift 2745383
  have htrace : WordTrace (prefixWord ++ tailWord_2745383) baseStart_2745383 baseEnd_2745383 := by
    simpa [prefixWord, tailWord_2745383, baseEnd_2745383] using wordTrace_append hprefix tailTrace_2745383
  have hstable : (prefixWord ++ tailWord_2745383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745383).length < 2 ^ (prefixWord ++ tailWord_2745383).sum := by decide
  have hdescent : baseEnd_2745383 < baseStart_2745383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745394 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_2745394 : Nat := 118140960795 + 2745394 * 2 ^ 59
def prefixEnd_2745394 : Nat := 4983230072969 + 3 ^ 40 * 2745394 * 2
def baseEnd_2745394 : Nat := 313268157326608192677593

theorem tailTrace_2745394 : CollatzResearch.WordTrace tailWord_2745394 prefixEnd_2745394 313268157326608192677593 := by
  unfold tailWord_2745394
  simp only [CollatzResearch.WordTrace]
  refine ⟨25033186353978472202796809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66755163610609259207458157 25033186353978472202796809)
  ·
    refine ⟨18774889765483854152097607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25033186353978472202796809 18774889765483854152097607)
    ·
      refine ⟨28162334648225781228146411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18774889765483854152097607 28162334648225781228146411)
      ·
        refine ⟨42243501972338671842219617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28162334648225781228146411 42243501972338671842219617)
        ·
          refine ⟨31682626479254003881664713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42243501972338671842219617 31682626479254003881664713)
          ·
            refine ⟨23761969859440502911248535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31682626479254003881664713 23761969859440502911248535)
            ·
              refine ⟨35642954789160754366872803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23761969859440502911248535 35642954789160754366872803)
              ·
                refine ⟨53464432183741131550309205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35642954789160754366872803 53464432183741131550309205)
                ·
                  refine ⟨313268157326608192677593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53464432183741131550309205 313268157326608192677593)
                  ·
                    rfl

theorem cell22_2745394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_2745394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745394 prefixEnd_2745394 := by exact prefixLift 2745394
  have htrace : WordTrace (prefixWord ++ tailWord_2745394) baseStart_2745394 baseEnd_2745394 := by
    simpa [prefixWord, tailWord_2745394, baseEnd_2745394] using wordTrace_append hprefix tailTrace_2745394
  have hstable : (prefixWord ++ tailWord_2745394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745394).length < 2 ^ (prefixWord ++ tailWord_2745394).sum := by decide
  have hdescent : baseEnd_2745394 < baseStart_2745394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745428 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 5]
def baseStart_2745428 : Nat := 118140960795 + 2745428 * 2 ^ 59
def prefixEnd_2745428 : Nat := 4983230072969 + 3 ^ 40 * 2745428 * 2
def baseEnd_2745428 : Nat := 313272036958219940894225

theorem tailTrace_2745428 : CollatzResearch.WordTrace tailWord_2745428 prefixEnd_2745428 313272036958219940894225 := by
  unfold tailWord_2745428
  simp only [CollatzResearch.WordTrace]
  refine ⟨50066992748895356308962469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66755990331860475078616625 50066992748895356308962469)
  ·
    refine ⟨9387561140417879307930463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50066992748895356308962469 9387561140417879307930463)
    ·
      refine ⟨14081341710626818961895695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9387561140417879307930463 14081341710626818961895695)
      ·
        refine ⟨21122012565940228442843543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14081341710626818961895695 21122012565940228442843543)
        ·
          refine ⟨31683018848910342664265315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21122012565940228442843543 31683018848910342664265315)
          ·
            refine ⟨47524528273365513996397973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31683018848910342664265315 47524528273365513996397973)
            ·
              refine ⟨2227712262814008468581155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47524528273365513996397973 2227712262814008468581155)
              ·
                refine ⟨3341568394221012702871733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227712262814008468581155 3341568394221012702871733)
                ·
                  refine ⟨313272036958219940894225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3341568394221012702871733 313272036958219940894225)
                  ·
                    rfl

theorem cell22_2745428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_2745428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745428 prefixEnd_2745428 := by exact prefixLift 2745428
  have htrace : WordTrace (prefixWord ++ tailWord_2745428) baseStart_2745428 baseEnd_2745428 := by
    simpa [prefixWord, tailWord_2745428, baseEnd_2745428] using wordTrace_append hprefix tailTrace_2745428
  have hstable : (prefixWord ++ tailWord_2745428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745428).length < 2 ^ (prefixWord ++ tailWord_2745428).sum := by decide
  have hdescent : baseEnd_2745428 < baseStart_2745428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745439 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 8]
def baseStart_2745439 : Nat := 118140960795 + 2745439 * 2 ^ 59
def prefixEnd_2745439 : Nat := 4983230072969 + 3 ^ 40 * 2745439 * 2
def baseEnd_2745439 : Nat := 313273292133153153552547

theorem tailTrace_2745439 : CollatzResearch.WordTrace tailWord_2745439 prefixEnd_2745439 313273292133153153552547 := by
  unfold tailWord_2745439
  simp only [CollatzResearch.WordTrace]
  refine ⟨100134386700750861496575371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66756257800500574331050247 100134386700750861496575371)
  ·
    refine ⟨150201580051126292244863057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100134386700750861496575371 150201580051126292244863057)
    ·
      refine ⟨112651185038344719183647293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150201580051126292244863057 112651185038344719183647293)
      ·
        refine ⟨42244194389379269693867735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112651185038344719183647293 42244194389379269693867735)
        ·
          refine ⟨63366291584068904540801603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42244194389379269693867735 63366291584068904540801603)
          ·
            refine ⟨95049437376103356811202405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63366291584068904540801603 95049437376103356811202405)
            ·
              refine ⟨17821769508019379402100451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95049437376103356811202405 17821769508019379402100451)
              ·
                refine ⟨26732654262029069103150677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17821769508019379402100451 26732654262029069103150677)
                ·
                  refine ⟨313273292133153153552547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26732654262029069103150677 313273292133153153552547)
                  ·
                    rfl

theorem cell22_2745439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 8].length) (baseStart_2745439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745439 prefixEnd_2745439 := by exact prefixLift 2745439
  have htrace : WordTrace (prefixWord ++ tailWord_2745439) baseStart_2745439 baseEnd_2745439 := by
    simpa [prefixWord, tailWord_2745439, baseEnd_2745439] using wordTrace_append hprefix tailTrace_2745439
  have hstable : (prefixWord ++ tailWord_2745439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745439).length < 2 ^ (prefixWord ++ tailWord_2745439).sum := by decide
  have hdescent : baseEnd_2745439 < baseStart_2745439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745503 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 1, 6]
def baseStart_2745503 : Nat := 118140960795 + 2745503 * 2 ^ 59
def prefixEnd_2745503 : Nat := 4983230072969 + 3 ^ 40 * 2745503 * 2
def baseEnd_2745503 : Nat := 939841784907384627057445

theorem tailTrace_2745503 : CollatzResearch.WordTrace tailWord_2745503 prefixEnd_2745503 939841784907384627057445 := by
  unfold tailWord_2745503
  simp only [CollatzResearch.WordTrace]
  refine ⟨100136720972519000426905163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66757813981679333617936775 100136720972519000426905163)
  ·
    refine ⟨150205081458778500640357745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100136720972519000426905163 150205081458778500640357745)
    ·
      refine ⟨112653811094083875480268309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150205081458778500640357745 112653811094083875480268309)
      ·
        refine ⟨5280647395035181663137577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112653811094083875480268309 5280647395035181663137577)
        ·
          refine ⟨3960485546276386247353183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5280647395035181663137577 3960485546276386247353183)
          ·
            refine ⟨5940728319414579371029775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3960485546276386247353183 5940728319414579371029775)
            ·
              refine ⟨8911092479121869056544663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5940728319414579371029775 8911092479121869056544663)
              ·
                refine ⟨13366638718682803584816995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8911092479121869056544663 13366638718682803584816995)
                ·
                  refine ⟨20049958078024205377225493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13366638718682803584816995 20049958078024205377225493)
                  ·
                    refine ⟨939841784907384627057445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20049958078024205377225493 939841784907384627057445)
                    ·
                      rfl

theorem cell22_2745503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_2745503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745503 prefixEnd_2745503 := by exact prefixLift 2745503
  have htrace : WordTrace (prefixWord ++ tailWord_2745503) baseStart_2745503 baseEnd_2745503 := by
    simpa [prefixWord, tailWord_2745503, baseEnd_2745503] using wordTrace_append hprefix tailTrace_2745503
  have hstable : (prefixWord ++ tailWord_2745503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745503).length < 2 ^ (prefixWord ++ tailWord_2745503).sum := by decide
  have hdescent : baseEnd_2745503 < baseStart_2745503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745533 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_2745533 : Nat := 118140960795 + 2745533 * 2 ^ 59
def prefixEnd_2745533 : Nat := 4983230072969 + 3 ^ 40 * 2745533 * 2
def baseEnd_2745533 : Nat := 939852054520474548807353

theorem tailTrace_2745533 : CollatzResearch.WordTrace tailWord_2745533 prefixEnd_2745533 939852054520474548807353 := by
  unfold tailWord_2745533
  simp only [CollatzResearch.WordTrace]
  refine ⟨100137815162410315550497253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66758543441606877033664835 100137815162410315550497253)
  ·
    refine ⟨18775840342951934165718235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100137815162410315550497253 18775840342951934165718235)
    ·
      refine ⟨28163760514427901248577353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18775840342951934165718235 28163760514427901248577353)
      ·
        refine ⟨21122820385820925936433015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28163760514427901248577353 21122820385820925936433015)
        ·
          refine ⟨31684230578731388904649523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21122820385820925936433015 31684230578731388904649523)
          ·
            refine ⟨47526345868097083356974285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31684230578731388904649523 47526345868097083356974285)
            ·
              refine ⟨17822379700536406258865357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47526345868097083356974285 17822379700536406258865357)
              ·
                refine ⟨6683392387701152347074509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17822379700536406258865357 6683392387701152347074509)
                ·
                  refine ⟨2506272145387932130152941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6683392387701152347074509 2506272145387932130152941)
                  ·
                    refine ⟨939852054520474548807353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2506272145387932130152941 939852054520474548807353)
                    ·
                      rfl

theorem cell22_2745533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_2745533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745533 prefixEnd_2745533 := by exact prefixLift 2745533
  have htrace : WordTrace (prefixWord ++ tailWord_2745533) baseStart_2745533 baseEnd_2745533 := by
    simpa [prefixWord, tailWord_2745533, baseEnd_2745533] using wordTrace_append hprefix tailTrace_2745533
  have hstable : (prefixWord ++ tailWord_2745533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745533).length < 2 ^ (prefixWord ++ tailWord_2745533).sum := by decide
  have hdescent : baseEnd_2745533 < baseStart_2745533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745623 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 1, 5]
def baseStart_2745623 : Nat := 118140960795 + 2745623 * 2 ^ 59
def prefixEnd_2745623 : Nat := 4983230072969 + 3 ^ 40 * 2745623 * 2
def baseEnd_2745623 : Nat := 939882863359744314057077

theorem tailTrace_2745623 : CollatzResearch.WordTrace tailWord_2745623 prefixEnd_2745623 939882863359744314057077 := by
  unfold tailWord_2745623
  simp only [CollatzResearch.WordTrace]
  refine ⟨100141097732084260921273523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66760731821389507280849015 100141097732084260921273523)
  ·
    refine ⟨150211646598126391381910285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100141097732084260921273523 150211646598126391381910285)
    ·
      refine ⟨56329367474297396768216357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150211646598126391381910285 56329367474297396768216357)
      ·
        refine ⟨10561756401430761894040567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56329367474297396768216357 10561756401430761894040567)
        ·
          refine ⟨15842634602146142841060851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10561756401430761894040567 15842634602146142841060851)
          ·
            refine ⟨23763951903219214261591277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15842634602146142841060851 23763951903219214261591277)
            ·
              refine ⟨8911481963707205348096729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23763951903219214261591277 8911481963707205348096729)
              ·
                refine ⟨6683611472780404011072547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8911481963707205348096729 6683611472780404011072547)
                ·
                  refine ⟨10025417209170606016608821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6683611472780404011072547 10025417209170606016608821)
                  ·
                    refine ⟨939882863359744314057077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10025417209170606016608821 939882863359744314057077)
                    ·
                      rfl

theorem cell22_2745623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_2745623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745623 prefixEnd_2745623 := by exact prefixLift 2745623
  have htrace : WordTrace (prefixWord ++ tailWord_2745623) baseStart_2745623 baseEnd_2745623 := by
    simpa [prefixWord, tailWord_2745623, baseEnd_2745623] using wordTrace_append hprefix tailTrace_2745623
  have hstable : (prefixWord ++ tailWord_2745623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745623).length < 2 ^ (prefixWord ++ tailWord_2745623).sum := by decide
  have hdescent : baseEnd_2745623 < baseStart_2745623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745642 : List Nat := [3, 1, 4, 2, 1, 2, 1, 4, 4]
def baseStart_2745642 : Nat := 118140960795 + 2745642 * 2 ^ 59
def prefixEnd_2745642 : Nat := 4983230072969 + 3 ^ 40 * 2745642 * 2
def baseEnd_2745642 : Nat := 313296455816011532610673

theorem tailTrace_2745642 : CollatzResearch.WordTrace tailWord_2745642 prefixEnd_2745642 313296455816011532610673 := by
  unfold tailWord_2745642
  simp only [CollatzResearch.WordTrace]
  refine ⟨25035447679753856791553795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66761193812676951444143453 25035447679753856791553795)
  ·
    refine ⟨37553171519630785187330693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25035447679753856791553795 37553171519630785187330693)
    ·
      refine ⟨7041219659930772222624505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37553171519630785187330693 7041219659930772222624505)
      ·
        refine ⟨5280914744948079166968379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7041219659930772222624505 5280914744948079166968379)
        ·
          refine ⟨7921372117422118750452569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5280914744948079166968379 7921372117422118750452569)
          ·
            refine ⟨5941029088066589062839427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7921372117422118750452569 5941029088066589062839427)
            ·
              refine ⟨8911543632099883594259141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5941029088066589062839427 8911543632099883594259141)
              ·
                refine ⟨1670914431018728173923589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8911543632099883594259141 1670914431018728173923589)
                ·
                  refine ⟨313296455816011532610673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1670914431018728173923589 313296455816011532610673)
                  ·
                    rfl

theorem cell22_2745642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_2745642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745642 prefixEnd_2745642 := by exact prefixLift 2745642
  have htrace : WordTrace (prefixWord ++ tailWord_2745642) baseStart_2745642 baseEnd_2745642 := by
    simpa [prefixWord, tailWord_2745642, baseEnd_2745642] using wordTrace_append hprefix tailTrace_2745642
  have hstable : (prefixWord ++ tailWord_2745642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745642).length < 2 ^ (prefixWord ++ tailWord_2745642).sum := by decide
  have hdescent : baseEnd_2745642 < baseStart_2745642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745653 : List Nat := [1, 3, 3, 1, 2, 2, 3, 7]
def baseStart_2745653 : Nat := 118140960795 + 2745653 * 2 ^ 59
def prefixEnd_2745653 : Nat := 4983230072969 + 3 ^ 40 * 2745653 * 2
def baseEnd_2745653 : Nat := 104432570330314915089665

theorem tailTrace_2745653 : CollatzResearch.WordTrace tailWord_2745653 prefixEnd_2745653 104432570330314915089665 := by
  unfold tailWord_2745653
  simp only [CollatzResearch.WordTrace]
  refine ⟨100142191921975576044865613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66761461281317050696577075 100142191921975576044865613)
  ·
    refine ⟨37553321970740841016824605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100142191921975576044865613 37553321970740841016824605)
    ·
      refine ⟨14082495739027815381309227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37553321970740841016824605 14082495739027815381309227)
      ·
        refine ⟨21123743608541723071963841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14082495739027815381309227 21123743608541723071963841)
        ·
          refine ⟨15842807706406292303972881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21123743608541723071963841 15842807706406292303972881)
          ·
            refine ⟨11882105779804719227979661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15842807706406292303972881 11882105779804719227979661)
            ·
              refine ⟨4455789667426769710492373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11882105779804719227979661 4455789667426769710492373)
              ·
                refine ⟨104432570330314915089665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4455789667426769710492373 104432570330314915089665)
                ·
                  rfl

theorem cell22_2745653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 7].length) (baseStart_2745653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745653 prefixEnd_2745653 := by exact prefixLift 2745653
  have htrace : WordTrace (prefixWord ++ tailWord_2745653) baseStart_2745653 baseEnd_2745653 := by
    simpa [prefixWord, tailWord_2745653, baseEnd_2745653] using wordTrace_append hprefix tailTrace_2745653
  have hstable : (prefixWord ++ tailWord_2745653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745653).length < 2 ^ (prefixWord ++ tailWord_2745653).sum := by decide
  have hdescent : baseEnd_2745653 < baseStart_2745653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745713 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 2, 5]
def baseStart_2745713 : Nat := 118140960795 + 2745713 * 2 ^ 59
def prefixEnd_2745713 : Nat := 4983230072969 + 3 ^ 40 * 2745713 * 2
def baseEnd_2745713 : Nat := 939913672199014079306801

theorem tailTrace_2745713 : CollatzResearch.WordTrace tailWord_2745713 prefixEnd_2745713 939913672199014079306801 := by
  unfold tailWord_2745713
  simp only [CollatzResearch.WordTrace]
  refine ⟨100144380301758206292049793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66762920201172137528033195 100144380301758206292049793)
  ·
    refine ⟨75108285226318654719037345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100144380301758206292049793 75108285226318654719037345)
    ·
      refine ⟨56331213919738991039278009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75108285226318654719037345 56331213919738991039278009)
      ·
        refine ⟨42248410439804243279458507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56331213919738991039278009 42248410439804243279458507)
        ·
          refine ⟨63372615659706364919187761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42248410439804243279458507 63372615659706364919187761)
          ·
            refine ⟨47529461744779773689390821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63372615659706364919187761 47529461744779773689390821)
            ·
              refine ⟨8911774077146207566760779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47529461744779773689390821 8911774077146207566760779)
              ·
                refine ⟨13367661115719311350141169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8911774077146207566760779 13367661115719311350141169)
                ·
                  refine ⟨10025745836789483512605877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13367661115719311350141169 10025745836789483512605877)
                  ·
                    refine ⟨939913672199014079306801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10025745836789483512605877 939913672199014079306801)
                    ·
                      rfl

theorem cell22_2745713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_2745713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745713 prefixEnd_2745713 := by exact prefixLift 2745713
  have htrace : WordTrace (prefixWord ++ tailWord_2745713) baseStart_2745713 baseEnd_2745713 := by
    simpa [prefixWord, tailWord_2745713, baseEnd_2745713] using wordTrace_append hprefix tailTrace_2745713
  have hstable : (prefixWord ++ tailWord_2745713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745713).length < 2 ^ (prefixWord ++ tailWord_2745713).sum := by decide
  have hdescent : baseEnd_2745713 < baseStart_2745713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2745728 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 3, 4]
def baseStart_2745728 : Nat := 118140960795 + 2745728 * 2 ^ 59
def prefixEnd_2745728 : Nat := 4983230072969 + 3 ^ 40 * 2745728 * 2
def baseEnd_2745728 : Nat := 939918807005559040181755

theorem tailTrace_2745728 : CollatzResearch.WordTrace tailWord_2745728 prefixEnd_2745728 939918807005559040181755 := by
  unfold tailWord_2745728
  simp only [CollatzResearch.WordTrace]
  refine ⟨50072463698351931926922919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66763284931135909235897225 50072463698351931926922919)
  ·
    refine ⟨75108695547527897890384379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50072463698351931926922919 75108695547527897890384379)
    ·
      refine ⟨112663043321291846835576569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75108695547527897890384379 112663043321291846835576569)
      ·
        refine ⟨84497282490968885126682427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112663043321291846835576569 84497282490968885126682427)
        ·
          refine ⟨126745923736453327690023641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84497282490968885126682427 126745923736453327690023641)
          ·
            refine ⟨95059442802339995767517731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126745923736453327690023641 95059442802339995767517731)
            ·
              refine ⟨142589164203509993651276597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95059442802339995767517731 142589164203509993651276597)
              ·
                refine ⟨13367734144079061904807181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142589164203509993651276597 13367734144079061904807181)
                ·
                  refine ⟨5012900304029648214302693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13367734144079061904807181 5012900304029648214302693)
                  ·
                    refine ⟨939918807005559040181755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5012900304029648214302693 939918807005559040181755)
                    ·
                      rfl

theorem cell22_2745728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_2745728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2745728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2745728 prefixEnd_2745728 := by exact prefixLift 2745728
  have htrace : WordTrace (prefixWord ++ tailWord_2745728) baseStart_2745728 baseEnd_2745728 := by
    simpa [prefixWord, tailWord_2745728, baseEnd_2745728] using wordTrace_append hprefix tailTrace_2745728
  have hstable : (prefixWord ++ tailWord_2745728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2745728).length < 2 ^ (prefixWord ++ tailWord_2745728).sum := by decide
  have hdescent : baseEnd_2745728 < baseStart_2745728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2745728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746047 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 6]
def baseStart_2746047 : Nat := 118140960795 + 2746047 * 2 ^ 59
def prefixEnd_2746047 : Nat := 4983230072969 + 3 ^ 40 * 2746047 * 2
def baseEnd_2746047 : Nat := 313342669074916180485259

theorem tailTrace_2746047 : CollatzResearch.WordTrace tailWord_2746047 prefixEnd_2746047 313342669074916180485259 := by
  unfold tailWord_2746047
  simp only [CollatzResearch.WordTrace]
  refine ⟨100156562282548181334708395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66771041521698787556472263 100156562282548181334708395)
  ·
    refine ⟨150234843423822272002062593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100156562282548181334708395 150234843423822272002062593)
    ·
      refine ⟨112676132567866704001546945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150234843423822272002062593 112676132567866704001546945)
      ·
        refine ⟨84507099425900028001160209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112676132567866704001546945 84507099425900028001160209)
        ·
          refine ⟨63380324569425021000870157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84507099425900028001160209 63380324569425021000870157)
          ·
            refine ⟨23767621713534382875326309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63380324569425021000870157 23767621713534382875326309)
            ·
              refine ⟨4456429071287696789123683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23767621713534382875326309 4456429071287696789123683)
              ·
                refine ⟨6684643606931545183685525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4456429071287696789123683 6684643606931545183685525)
                ·
                  refine ⟨313342669074916180485259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6684643606931545183685525 313342669074916180485259)
                  ·
                    rfl

theorem cell22_2746047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 6].length) (baseStart_2746047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746047 prefixEnd_2746047 := by exact prefixLift 2746047
  have htrace : WordTrace (prefixWord ++ tailWord_2746047) baseStart_2746047 baseEnd_2746047 := by
    simpa [prefixWord, tailWord_2746047, baseEnd_2746047] using wordTrace_append hprefix tailTrace_2746047
  have hstable : (prefixWord ++ tailWord_2746047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746047).length < 2 ^ (prefixWord ++ tailWord_2746047).sum := by decide
  have hdescent : baseEnd_2746047 < baseStart_2746047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746066 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_2746066 : Nat := 118140960795 + 2746066 * 2 ^ 59
def prefixEnd_2746066 : Nat := 4983230072969 + 3 ^ 40 * 2746066 * 2
def baseEnd_2746066 : Nat := 940034511313038825230719

theorem tailTrace_2746066 : CollatzResearch.WordTrace tailWord_2746066 prefixEnd_2746066 940034511313038825230719 := by
  unfold tailWord_2746066
  simp only [CollatzResearch.WordTrace]
  refine ⟨25039313817369836894912513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66771503512986231719766701 25039313817369836894912513)
  ·
    refine ⟨18779485363027377671184385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25039313817369836894912513 18779485363027377671184385)
    ·
      refine ⟨14084614022270533253388289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18779485363027377671184385 14084614022270533253388289)
      ·
        refine ⟨10563460516702899940041217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14084614022270533253388289 10563460516702899940041217)
        ·
          refine ⟨7922595387527174955030913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10563460516702899940041217 7922595387527174955030913)
          ·
            refine ⟨5941946540645381216273185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7922595387527174955030913 5941946540645381216273185)
            ·
              refine ⟨4456459905484035912204889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5941946540645381216273185 4456459905484035912204889)
              ·
                refine ⟨3342344929113026934153667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4456459905484035912204889 3342344929113026934153667)
                ·
                  refine ⟨5013517393669540401230501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342344929113026934153667 5013517393669540401230501)
                  ·
                    refine ⟨940034511313038825230719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5013517393669540401230501 940034511313038825230719)
                    ·
                      rfl

theorem cell22_2746066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_2746066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746066 prefixEnd_2746066 := by exact prefixLift 2746066
  have htrace : WordTrace (prefixWord ++ tailWord_2746066) baseStart_2746066 baseEnd_2746066 := by
    simpa [prefixWord, tailWord_2746066, baseEnd_2746066] using wordTrace_append hprefix tailTrace_2746066
  have hstable : (prefixWord ++ tailWord_2746066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746066).length < 2 ^ (prefixWord ++ tailWord_2746066).sum := by decide
  have hdescent : baseEnd_2746066 < baseStart_2746066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746094 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_2746094 : Nat := 118140960795 + 2746094 * 2 ^ 59
def prefixEnd_2746094 : Nat := 4983230072969 + 3 ^ 40 * 2746094 * 2
def baseEnd_2746094 : Nat := 940044096285256085530633

theorem tailTrace_2746094 : CollatzResearch.WordTrace tailWord_2746094 prefixEnd_2746094 940044096285256085530633 := by
  unfold tailWord_2746094
  simp only [CollatzResearch.WordTrace]
  refine ⟨12519784564172238545208667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66772184342251938907779557 12519784564172238545208667)
  ·
    refine ⟨18779676846258357817813001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12519784564172238545208667 18779676846258357817813001)
    ·
      refine ⟨14084757634693768363359751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18779676846258357817813001 14084757634693768363359751)
      ·
        refine ⟨21127136452040652545039627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14084757634693768363359751 21127136452040652545039627)
        ·
          refine ⟨31690704678060978817559441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21127136452040652545039627 31690704678060978817559441)
          ·
            refine ⟨23768028508545734113169581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31690704678060978817559441 23768028508545734113169581)
            ·
              refine ⟨8913010690704650292438593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23768028508545734113169581 8913010690704650292438593)
              ·
                refine ⟨6684758018028487719328945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8913010690704650292438593 6684758018028487719328945)
                ·
                  refine ⟨5013568513521365789496709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6684758018028487719328945 5013568513521365789496709)
                  ·
                    refine ⟨940044096285256085530633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5013568513521365789496709 940044096285256085530633)
                    ·
                      rfl

theorem cell22_2746094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_2746094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746094 prefixEnd_2746094 := by exact prefixLift 2746094
  have htrace : WordTrace (prefixWord ++ tailWord_2746094) baseStart_2746094 baseEnd_2746094 := by
    simpa [prefixWord, tailWord_2746094, baseEnd_2746094] using wordTrace_append hprefix tailTrace_2746094
  have hstable : (prefixWord ++ tailWord_2746094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746094).length < 2 ^ (prefixWord ++ tailWord_2746094).sum := by decide
  have hdescent : baseEnd_2746094 < baseStart_2746094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746124 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 3, 3]
def baseStart_2746124 : Nat := 118140960795 + 2746124 * 2 ^ 59
def prefixEnd_2746124 : Nat := 4983230072969 + 3 ^ 40 * 2746124 * 2
def baseEnd_2746124 : Nat := 940054365898346007280541

theorem tailTrace_2746124 : CollatzResearch.WordTrace tailWord_2746124 prefixEnd_2746124 940054365898346007280541 := by
  unfold tailWord_2746124
  simp only [CollatzResearch.WordTrace]
  refine ⟨50079685351634611742630713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66772913802179482323507617 50079685351634611742630713)
  ·
    refine ⟨37559764013725958806973035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50079685351634611742630713 37559764013725958806973035)
    ·
      refine ⟨56339646020588938210459553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37559764013725958806973035 56339646020588938210459553)
      ·
        refine ⟨42254734515441703657844665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56339646020588938210459553 42254734515441703657844665)
        ·
          refine ⟨31691050886581277743383499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42254734515441703657844665 31691050886581277743383499)
          ·
            refine ⟨47536576329871916615075249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31691050886581277743383499 47536576329871916615075249)
            ·
              refine ⟨35652432247403937461306437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47536576329871916615075249 35652432247403937461306437)
              ·
                refine ⟨6684831046388238273994957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35652432247403937461306437 6684831046388238273994957)
                ·
                  refine ⟨2506811642395589352748109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6684831046388238273994957 2506811642395589352748109)
                  ·
                    refine ⟨940054365898346007280541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2506811642395589352748109 940054365898346007280541)
                    ·
                      rfl

theorem cell22_2746124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_2746124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746124 prefixEnd_2746124 := by exact prefixLift 2746124
  have htrace : WordTrace (prefixWord ++ tailWord_2746124) baseStart_2746124 baseEnd_2746124 := by
    simpa [prefixWord, tailWord_2746124, baseEnd_2746124] using wordTrace_append hprefix tailTrace_2746124
  have hstable : (prefixWord ++ tailWord_2746124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746124).length < 2 ^ (prefixWord ++ tailWord_2746124).sum := by decide
  have hdescent : baseEnd_2746124 < baseStart_2746124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746184 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 3, 4]
def baseStart_2746184 : Nat := 118140960795 + 2746184 * 2 ^ 59
def prefixEnd_2746184 : Nat := 4983230072969 + 3 ^ 40 * 2746184 * 2
def baseEnd_2746184 : Nat := 940074905124525850780357

theorem tailTrace_2746184 : CollatzResearch.WordTrace tailWord_2746184 prefixEnd_2746184 940074905124525850780357 := by
  unfold tailWord_2746184
  simp only [CollatzResearch.WordTrace]
  refine ⟨50080779541525926866222803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66774372722034569154963737 50080779541525926866222803)
  ·
    refine ⟨75121169312288890299334205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50080779541525926866222803 75121169312288890299334205)
    ·
      refine ⟨28170438492108333862250327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75121169312288890299334205 28170438492108333862250327)
      ·
        refine ⟨42255657738162500793375491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28170438492108333862250327 42255657738162500793375491)
        ·
          refine ⟨63383486607243751190063237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42255657738162500793375491 63383486607243751190063237)
          ·
            refine ⟨11884403738858203348136857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63383486607243751190063237 11884403738858203348136857)
            ·
              refine ⟨8913302804143652511102643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11884403738858203348136857 8913302804143652511102643)
              ·
                refine ⟨13369954206215478766653965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8913302804143652511102643 13369954206215478766653965)
                ·
                  refine ⟨5013732827330804537495237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13369954206215478766653965 5013732827330804537495237)
                  ·
                    refine ⟨940074905124525850780357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5013732827330804537495237 940074905124525850780357)
                    ·
                      rfl

theorem cell22_2746184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_2746184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746184 prefixEnd_2746184 := by exact prefixLift 2746184
  have htrace : WordTrace (prefixWord ++ tailWord_2746184) baseStart_2746184 baseEnd_2746184 := by
    simpa [prefixWord, tailWord_2746184, baseEnd_2746184] using wordTrace_append hprefix tailTrace_2746184
  have hstable : (prefixWord ++ tailWord_2746184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746184).length < 2 ^ (prefixWord ++ tailWord_2746184).sum := by decide
  have hdescent : baseEnd_2746184 < baseStart_2746184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746216 : List Nat := [2, 1, 4, 2, 1, 1, 1, 6, 4]
def baseStart_2746216 : Nat := 118140960795 + 2746216 * 2 ^ 59
def prefixEnd_2746216 : Nat := 4983230072969 + 3 ^ 40 * 2746216 * 2
def baseEnd_2746216 : Nat := 313361953126162811326753

theorem tailTrace_2746216 : CollatzResearch.WordTrace tailWord_2746216 prefixEnd_2746216 313361953126162811326753 := by
  unfold tailWord_2746216
  simp only [CollatzResearch.WordTrace]
  refine ⟨50081363109467961598805251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66775150812623948798407001 50081363109467961598805251)
  ·
    refine ⟨75122044664201942398207877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50081363109467961598805251 75122044664201942398207877)
    ·
      refine ⟨14085383374537864199663977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75122044664201942398207877 14085383374537864199663977)
      ·
        refine ⟨10564037530903398149747983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14085383374537864199663977 10564037530903398149747983)
        ·
          refine ⟨15846056296355097224621975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10564037530903398149747983 15846056296355097224621975)
          ·
            refine ⟨23769084444532645836932963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15846056296355097224621975 23769084444532645836932963)
            ·
              refine ⟨35653626666798968755399445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23769084444532645836932963 35653626666798968755399445)
              ·
                refine ⟨1671263750006201660409349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35653626666798968755399445 1671263750006201660409349)
                ·
                  refine ⟨313361953126162811326753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671263750006201660409349 313361953126162811326753)
                  ·
                    rfl

theorem cell22_2746216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 4].length) (baseStart_2746216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746216 prefixEnd_2746216 := by exact prefixLift 2746216
  have htrace : WordTrace (prefixWord ++ tailWord_2746216) baseStart_2746216 baseEnd_2746216 := by
    simpa [prefixWord, tailWord_2746216, baseEnd_2746216] using wordTrace_append hprefix tailTrace_2746216
  have hstable : (prefixWord ++ tailWord_2746216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746216).length < 2 ^ (prefixWord ++ tailWord_2746216).sum := by decide
  have hdescent : baseEnd_2746216 < baseStart_2746216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746227 : List Nat := [1, 1, 1, 2, 2, 1, 3, 11]
def baseStart_2746227 : Nat := 118140960795 + 2746227 * 2 ^ 59
def prefixEnd_2746227 : Nat := 4983230072969 + 3 ^ 40 * 2746227 * 2
def baseEnd_2746227 : Nat := 104454402767032007995025

theorem tailTrace_2746227 : CollatzResearch.WordTrace tailWord_2746227 prefixEnd_2746227 104454402767032007995025 := by
  unfold tailWord_2746227
  simp only [CollatzResearch.WordTrace]
  refine ⟨100163127421896072076260935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66775418281264048050840623 100163127421896072076260935)
  ·
    refine ⟨150244691132844108114391403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100163127421896072076260935 150244691132844108114391403)
    ·
      refine ⟨225367036699266162171587105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150244691132844108114391403 225367036699266162171587105)
      ·
        refine ⟨169025277524449621628690329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225367036699266162171587105 169025277524449621628690329)
        ·
          refine ⟨126768958143337216221517747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169025277524449621628690329 126768958143337216221517747)
          ·
            refine ⟨190153437215005824332276621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126768958143337216221517747 190153437215005824332276621)
            ·
              refine ⟨71307538955627184124603733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190153437215005824332276621 71307538955627184124603733)
              ·
                refine ⟨104454402767032007995025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 71307538955627184124603733 104454402767032007995025)
                ·
                  rfl

theorem cell22_2746227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 11].length) (baseStart_2746227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746227 prefixEnd_2746227 := by exact prefixLift 2746227
  have htrace : WordTrace (prefixWord ++ tailWord_2746227) baseStart_2746227 baseEnd_2746227 := by
    simpa [prefixWord, tailWord_2746227, baseEnd_2746227] using wordTrace_append hprefix tailTrace_2746227
  have hstable : (prefixWord ++ tailWord_2746227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746227).length < 2 ^ (prefixWord ++ tailWord_2746227).sum := by decide
  have hdescent : baseEnd_2746227 < baseStart_2746227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746229 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2746229 : Nat := 118140960795 + 2746229 * 2 ^ 59
def prefixEnd_2746229 : Nat := 4983230072969 + 3 ^ 40 * 2746229 * 2
def baseEnd_2746229 : Nat := 940090309544160733405219

theorem tailTrace_2746229 : CollatzResearch.WordTrace tailWord_2746229 prefixEnd_2746229 940090309544160733405219 := by
  unfold tailWord_2746229
  simp only [CollatzResearch.WordTrace]
  refine ⟨100163200367888826417833741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66775466911925884278555827 100163200367888826417833741)
  ·
    refine ⟨37561200137958309906687653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100163200367888826417833741 37561200137958309906687653)
    ·
      refine ⟨7042725025867183107503935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37561200137958309906687653 7042725025867183107503935)
      ·
        refine ⟨10564087538800774661255903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7042725025867183107503935 10564087538800774661255903)
        ·
          refine ⟨15846131308201161991883855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10564087538800774661255903 15846131308201161991883855)
          ·
            refine ⟨23769196962301742987825783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15846131308201161991883855 23769196962301742987825783)
            ·
              refine ⟨35653795443452614481738675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23769196962301742987825783 35653795443452614481738675)
              ·
                refine ⟨53480693165178921722608013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35653795443452614481738675 53480693165178921722608013)
                ·
                  refine ⟨20055259936942095645978005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53480693165178921722608013 20055259936942095645978005)
                  ·
                    refine ⟨940090309544160733405219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20055259936942095645978005 940090309544160733405219)
                    ·
                      rfl

theorem cell22_2746229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2746229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746229 prefixEnd_2746229 := by exact prefixLift 2746229
  have htrace : WordTrace (prefixWord ++ tailWord_2746229) baseStart_2746229 baseEnd_2746229 := by
    simpa [prefixWord, tailWord_2746229, baseEnd_2746229] using wordTrace_append hprefix tailTrace_2746229
  have hstable : (prefixWord ++ tailWord_2746229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746229).length < 2 ^ (prefixWord ++ tailWord_2746229).sum := by decide
  have hdescent : baseEnd_2746229 < baseStart_2746229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746250 : List Nat := [3, 1, 2, 4, 2, 2, 1, 3, 4]
def baseStart_2746250 : Nat := 118140960795 + 2746250 * 2 ^ 59
def prefixEnd_2746250 : Nat := 4983230072969 + 3 ^ 40 * 2746250 * 2
def baseEnd_2746250 : Nat := 313365832757774559543385

theorem tailTrace_2746250 : CollatzResearch.WordTrace tailWord_2746250 prefixEnd_2746250 313365832757774559543385 := by
  unfold tailWord_2746250
  simp only [CollatzResearch.WordTrace]
  refine ⟨25040991575203186751087051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66775977533875164669565469 25040991575203186751087051)
  ·
    refine ⟨37561487362804780126630577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25040991575203186751087051 37561487362804780126630577)
    ·
      refine ⟨28171115522103585094972933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37561487362804780126630577 28171115522103585094972933)
      ·
        refine ⟨5282084160394422205307425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28171115522103585094972933 5282084160394422205307425)
        ·
          refine ⟨3961563120295816653980569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5282084160394422205307425 3961563120295816653980569)
          ·
            refine ⟨2971172340221862490485427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3961563120295816653980569 2971172340221862490485427)
            ·
              refine ⟨4456758510332793735728141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971172340221862490485427 4456758510332793735728141)
              ·
                refine ⟨1671284441374797650898053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4456758510332793735728141 1671284441374797650898053)
                ·
                  refine ⟨313365832757774559543385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671284441374797650898053 313365832757774559543385)
                  ·
                    rfl

theorem cell22_2746250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_2746250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746250 prefixEnd_2746250 := by exact prefixLift 2746250
  have htrace : WordTrace (prefixWord ++ tailWord_2746250) baseStart_2746250 baseEnd_2746250 := by
    simpa [prefixWord, tailWord_2746250, baseEnd_2746250] using wordTrace_append hprefix tailTrace_2746250
  have hstable : (prefixWord ++ tailWord_2746250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746250).length < 2 ^ (prefixWord ++ tailWord_2746250).sum := by decide
  have hdescent : baseEnd_2746250 < baseStart_2746250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746379 : List Nat := [1, 1, 1, 1, 6, 1, 11]
def baseStart_2746379 : Nat := 118140960795 + 2746379 * 2 ^ 59
def prefixEnd_2746379 : Nat := 4983230072969 + 3 ^ 40 * 2746379 * 2
def baseEnd_2746379 : Nat := 34820061392948531190917

theorem tailTrace_2746379 : CollatzResearch.WordTrace tailWord_2746379 prefixEnd_2746379 34820061392948531190917 := by
  unfold tailWord_2746379
  simp only [CollatzResearch.WordTrace]
  refine ⟨100168671317345402035794191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66779114211563601357196127 100168671317345402035794191)
  ·
    refine ⟨150253006976018103053691287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100168671317345402035794191 150253006976018103053691287)
    ·
      refine ⟨225379510464027154580536931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150253006976018103053691287 225379510464027154580536931)
      ·
        refine ⟨338069265696040731870805397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225379510464027154580536931 338069265696040731870805397)
        ·
          refine ⟨15846996829501909306444003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 338069265696040731870805397 15846996829501909306444003)
          ·
            refine ⟨23770495244252863959666005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15846996829501909306444003 23770495244252863959666005)
            ·
              refine ⟨34820061392948531190917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23770495244252863959666005 34820061392948531190917)
              ·
                rfl

theorem cell22_2746379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 11].length) (baseStart_2746379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746379 prefixEnd_2746379 := by exact prefixLift 2746379
  have htrace : WordTrace (prefixWord ++ tailWord_2746379) baseStart_2746379 baseEnd_2746379 := by
    simpa [prefixWord, tailWord_2746379, baseEnd_2746379] using wordTrace_append hprefix tailTrace_2746379
  have hstable : (prefixWord ++ tailWord_2746379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746379).length < 2 ^ (prefixWord ++ tailWord_2746379).sum := by decide
  have hdescent : baseEnd_2746379 < baseStart_2746379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746409 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_2746409 : Nat := 118140960795 + 2746409 * 2 ^ 59
def prefixEnd_2746409 : Nat := 4983230072969 + 3 ^ 40 * 2746409 * 2
def baseEnd_2746409 : Nat := 940151927222700263904667

theorem tailTrace_2746409 : CollatzResearch.WordTrace tailWord_2746409 prefixEnd_2746409 940151927222700263904667 := by
  unfold tailWord_2746409
  simp only [CollatzResearch.WordTrace]
  refine ⟨100169765507236717159386281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66779843671491144772924187 100169765507236717159386281)
  ·
    refine ⟨75127324130427537869539711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100169765507236717159386281 75127324130427537869539711)
    ·
      refine ⟨112690986195641306804309567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75127324130427537869539711 112690986195641306804309567)
      ·
        refine ⟨169036479293461960206464351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112690986195641306804309567 169036479293461960206464351)
        ·
          refine ⟨253554718940192940309696527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169036479293461960206464351 253554718940192940309696527)
          ·
            refine ⟨380332078410289410464544791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253554718940192940309696527 380332078410289410464544791)
            ·
              refine ⟨570498117615434115696817187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380332078410289410464544791 570498117615434115696817187)
              ·
                refine ⟨855747176423151173545225781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570498117615434115696817187 855747176423151173545225781)
                ·
                  refine ⟨80226297789670422519864917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 855747176423151173545225781 80226297789670422519864917)
                  ·
                    refine ⟨940151927222700263904667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80226297789670422519864917 940151927222700263904667)
                    ·
                      rfl

theorem cell22_2746409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_2746409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746409 prefixEnd_2746409 := by exact prefixLift 2746409
  have htrace : WordTrace (prefixWord ++ tailWord_2746409) baseStart_2746409 baseEnd_2746409 := by
    simpa [prefixWord, tailWord_2746409, baseEnd_2746409] using wordTrace_append hprefix tailTrace_2746409
  have hstable : (prefixWord ++ tailWord_2746409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746409).length < 2 ^ (prefixWord ++ tailWord_2746409).sum := by decide
  have hdescent : baseEnd_2746409 < baseStart_2746409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746411 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 5, 3]
def baseStart_2746411 : Nat := 118140960795 + 2746411 * 2 ^ 59
def prefixEnd_2746411 : Nat := 4983230072969 + 3 ^ 40 * 2746411 * 2
def baseEnd_2746411 : Nat := 940152611863572925354661

theorem tailTrace_2746411 : CollatzResearch.WordTrace tailWord_2746411 prefixEnd_2746411 940152611863572925354661 := by
  unfold tailWord_2746411
  simp only [CollatzResearch.WordTrace]
  refine ⟨100169838453229471500959087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66779892302152981000639391 100169838453229471500959087)
  ·
    refine ⟨150254757679844207251438631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100169838453229471500959087 150254757679844207251438631)
    ·
      refine ⟨225382136519766310877157947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150254757679844207251438631 225382136519766310877157947)
      ·
        refine ⟨338073204779649466315736921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225382136519766310877157947 338073204779649466315736921)
        ·
          refine ⟨253554903584737099736802691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338073204779649466315736921 253554903584737099736802691)
          ·
            refine ⟨380332355377105649605204037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253554903584737099736802691 380332355377105649605204037)
            ·
              refine ⟨71312316633207309300975757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 380332355377105649605204037 71312316633207309300975757)
              ·
                refine ⟨26742118737452740987865909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71312316633207309300975757 26742118737452740987865909)
                ·
                  refine ⟨2507073631636194467612429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26742118737452740987865909 2507073631636194467612429)
                  ·
                    refine ⟨940152611863572925354661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507073631636194467612429 940152611863572925354661)
                    ·
                      rfl

theorem cell22_2746411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 3].length) (baseStart_2746411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746411 prefixEnd_2746411 := by exact prefixLift 2746411
  have htrace : WordTrace (prefixWord ++ tailWord_2746411) baseStart_2746411 baseEnd_2746411 := by
    simpa [prefixWord, tailWord_2746411, baseEnd_2746411] using wordTrace_append hprefix tailTrace_2746411
  have hstable : (prefixWord ++ tailWord_2746411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746411).length < 2 ^ (prefixWord ++ tailWord_2746411).sum := by decide
  have hdescent : baseEnd_2746411 < baseStart_2746411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746430 : List Nat := [4, 2, 1, 3, 3, 1, 8]
def baseStart_2746430 : Nat := 118140960795 + 2746430 * 2 ^ 59
def prefixEnd_2746430 : Nat := 4983230072969 + 3 ^ 40 * 2746430 * 2
def baseEnd_2746430 : Nat := 34820707998217155893689

theorem tailTrace_2746430 : CollatzResearch.WordTrace tailWord_2746430 prefixEnd_2746430 34820707998217155893689 := by
  unfold tailWord_2746430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12521316430020079718237593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66780354293440425163933829 12521316430020079718237593)
  ·
    refine ⟨9390987322515059788678195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12521316430020079718237593 9390987322515059788678195)
    ·
      refine ⟨14086480983772589683017293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9390987322515059788678195 14086480983772589683017293)
      ·
        refine ⟨5282430368914721131131485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14086480983772589683017293 5282430368914721131131485)
        ·
          refine ⟨1980911388343020424174307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5282430368914721131131485 1980911388343020424174307)
          ·
            refine ⟨2971367082514530636261461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980911388343020424174307 2971367082514530636261461)
            ·
              refine ⟨34820707998217155893689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2971367082514530636261461 34820707998217155893689)
              ·
                rfl

theorem cell22_2746430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 8].length) (baseStart_2746430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746430 prefixEnd_2746430 := by exact prefixLift 2746430
  have htrace : WordTrace (prefixWord ++ tailWord_2746430) baseStart_2746430 baseEnd_2746430 := by
    simpa [prefixWord, tailWord_2746430, baseEnd_2746430] using wordTrace_append hprefix tailTrace_2746430
  have hstable : (prefixWord ++ tailWord_2746430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746430).length < 2 ^ (prefixWord ++ tailWord_2746430).sum := by decide
  have hdescent : baseEnd_2746430 < baseStart_2746430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746441 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 5]
def baseStart_2746441 : Nat := 118140960795 + 2746441 * 2 ^ 59
def prefixEnd_2746441 : Nat := 4983230072969 + 3 ^ 40 * 2746441 * 2
def baseEnd_2746441 : Nat := 313387627158887615701523

theorem tailTrace_2746441 : CollatzResearch.WordTrace tailWord_2746441 prefixEnd_2746441 313387627158887615701523 := by
  unfold tailWord_2746441
  simp only [CollatzResearch.WordTrace]
  refine ⟨100170932643120786624551177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66780621762080524416367451 100170932643120786624551177)
  ·
    refine ⟨75128199482340589968413383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100170932643120786624551177 75128199482340589968413383)
    ·
      refine ⟨112692299223510884952620075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75128199482340589968413383 112692299223510884952620075)
      ·
        refine ⟨169038448835266327428930113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112692299223510884952620075 169038448835266327428930113)
        ·
          refine ⟨126778836626449745571697585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169038448835266327428930113 126778836626449745571697585)
          ·
            refine ⟨95084127469837309178773189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126778836626449745571697585 95084127469837309178773189)
            ·
              refine ⟨17828273900594495471019973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95084127469837309178773189 17828273900594495471019973)
              ·
                refine ⟨3342801356361467900816245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17828273900594495471019973 3342801356361467900816245)
                ·
                  refine ⟨313387627158887615701523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3342801356361467900816245 313387627158887615701523)
                  ·
                    rfl

theorem cell22_2746441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_2746441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746441 prefixEnd_2746441 := by exact prefixLift 2746441
  have htrace : WordTrace (prefixWord ++ tailWord_2746441) baseStart_2746441 baseEnd_2746441 := by
    simpa [prefixWord, tailWord_2746441, baseEnd_2746441] using wordTrace_append hprefix tailTrace_2746441
  have hstable : (prefixWord ++ tailWord_2746441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746441).length < 2 ^ (prefixWord ++ tailWord_2746441).sum := by decide
  have hdescent : baseEnd_2746441 < baseStart_2746441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746582 : List Nat := [5, 2, 1, 2, 1, 1, 4, 6]
def baseStart_2746582 : Nat := 118140960795 + 2746582 * 2 ^ 59
def prefixEnd_2746582 : Nat := 4983230072969 + 3 ^ 40 * 2746582 * 2
def baseEnd_2746582 : Nat := 104467905406465053258793

theorem tailTrace_2746582 : CollatzResearch.WordTrace tailWord_2746582 prefixEnd_2746582 104467905406465053258793 := by
  unfold tailWord_2746582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6261004708475622981589625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66784050223739978470289333 6261004708475622981589625)
  ·
    refine ⟨4695753531356717236192219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6261004708475622981589625 4695753531356717236192219)
    ·
      refine ⟨7043630297035075854288329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4695753531356717236192219 7043630297035075854288329)
      ·
        refine ⟨5282722722776306890716247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7043630297035075854288329 5282722722776306890716247)
        ·
          refine ⟨7924084084164460336074371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5282722722776306890716247 7924084084164460336074371)
          ·
            refine ⟨11886126126246690504111557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7924084084164460336074371 11886126126246690504111557)
            ·
              refine ⟨2228648648671254469520917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11886126126246690504111557 2228648648671254469520917)
              ·
                refine ⟨104467905406465053258793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2228648648671254469520917 104467905406465053258793)
                ·
                  rfl

theorem cell22_2746582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_2746582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746582 prefixEnd_2746582 := by exact prefixLift 2746582
  have htrace : WordTrace (prefixWord ++ tailWord_2746582) baseStart_2746582 baseEnd_2746582 := by
    simpa [prefixWord, tailWord_2746582, baseEnd_2746582] using wordTrace_append hprefix tailTrace_2746582
  have hstable : (prefixWord ++ tailWord_2746582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746582).length < 2 ^ (prefixWord ++ tailWord_2746582).sum := by decide
  have hdescent : baseEnd_2746582 < baseStart_2746582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746623 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 3, 4]
def baseStart_2746623 : Nat := 118140960795 + 2746623 * 2 ^ 59
def prefixEnd_2746623 : Nat := 4983230072969 + 3 ^ 40 * 2746623 * 2
def baseEnd_2746623 : Nat := 940225183796075039054011

theorem tailTrace_2746623 : CollatzResearch.WordTrace tailWord_2746623 prefixEnd_2746623 940225183796075039054011 := by
  unfold tailWord_2746623
  simp only [CollatzResearch.WordTrace]
  refine ⟨100177570728461431707676523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66785047152307621138451015 100177570728461431707676523)
  ·
    refine ⟨150266356092692147561514785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100177570728461431707676523 150266356092692147561514785)
    ·
      refine ⟨112699767069519110671136089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150266356092692147561514785 112699767069519110671136089)
      ·
        refine ⟨84524825302139333003352067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112699767069519110671136089 84524825302139333003352067)
        ·
          refine ⟨126787237953208999505028101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84524825302139333003352067 126787237953208999505028101)
          ·
            refine ⟨23772607116226687407192769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126787237953208999505028101 23772607116226687407192769)
            ·
              refine ⟨17829455337170015555394577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23772607116226687407192769 17829455337170015555394577)
              ·
                refine ⟨13372091502877511666545933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17829455337170015555394577 13372091502877511666545933)
                ·
                  refine ⟨5014534313579066874954725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13372091502877511666545933 5014534313579066874954725)
                  ·
                    refine ⟨940225183796075039054011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5014534313579066874954725 940225183796075039054011)
                    ·
                      rfl

theorem cell22_2746623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_2746623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746623 prefixEnd_2746623 := by exact prefixLift 2746623
  have htrace : WordTrace (prefixWord ++ tailWord_2746623) baseStart_2746623 baseEnd_2746623 := by
    simpa [prefixWord, tailWord_2746623, baseEnd_2746623] using wordTrace_append hprefix tailTrace_2746623
  have hstable : (prefixWord ++ tailWord_2746623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746623).length < 2 ^ (prefixWord ++ tailWord_2746623).sum := by decide
  have hdescent : baseEnd_2746623 < baseStart_2746623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746638 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_2746638 : Nat := 118140960795 + 2746638 * 2 ^ 59
def prefixEnd_2746638 : Nat := 4983230072969 + 3 ^ 40 * 2746638 * 2
def baseEnd_2746638 : Nat := 313410106200873333309655

theorem tailTrace_2746638 : CollatzResearch.WordTrace tailWord_2746638 prefixEnd_2746638 313410106200873333309655 := by
  unfold tailWord_2746638
  simp only [CollatzResearch.WordTrace]
  refine ⟨12522264727925886158684071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66785411882271392846315045 12522264727925886158684071)
  ·
    refine ⟨18783397091888829238026107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12522264727925886158684071 18783397091888829238026107)
    ·
      refine ⟨28175095637833243857039161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18783397091888829238026107 28175095637833243857039161)
      ·
        refine ⟨21131321728374932892779371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28175095637833243857039161 21131321728374932892779371)
        ·
          refine ⟨31696982592562399339169057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21131321728374932892779371 31696982592562399339169057)
          ·
            refine ⟨23772736944421799504376793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31696982592562399339169057 23772736944421799504376793)
            ·
              refine ⟨17829552708316349628282595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23772736944421799504376793 17829552708316349628282595)
              ·
                refine ⟨26744329062474524442423893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17829552708316349628282595 26744329062474524442423893)
                ·
                  refine ⟨313410106200873333309655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26744329062474524442423893 313410106200873333309655)
                  ·
                    rfl

theorem cell22_2746638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_2746638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746638 prefixEnd_2746638 := by exact prefixLift 2746638
  have htrace : WordTrace (prefixWord ++ tailWord_2746638) baseStart_2746638 baseEnd_2746638 := by
    simpa [prefixWord, tailWord_2746638, baseEnd_2746638] using wordTrace_append hprefix tailTrace_2746638
  have hstable : (prefixWord ++ tailWord_2746638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746638).length < 2 ^ (prefixWord ++ tailWord_2746638).sum := by decide
  have hdescent : baseEnd_2746638 < baseStart_2746638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746700 : List Nat := [2, 2, 1, 3, 2, 1, 5, 6]
def baseStart_2746700 : Nat := 118140960795 + 2746700 * 2 ^ 59
def prefixEnd_2746700 : Nat := 4983230072969 + 3 ^ 40 * 2746700 * 2
def baseEnd_2746700 : Nat := 104472393607741389430975

theorem tailTrace_2746700 : CollatzResearch.WordTrace tailWord_2746700 prefixEnd_2746700 104472393607741389430975 := by
  unfold tailWord_2746700
  simp only [CollatzResearch.WordTrace]
  refine ⟨50090189574591236929114777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66786919432788315905486369 50090189574591236929114777)
  ·
    refine ⟨37567642180943427696836083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50090189574591236929114777 37567642180943427696836083)
    ·
      refine ⟨56351463271415141545254125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37567642180943427696836083 56351463271415141545254125)
      ·
        refine ⟨21131798726780678079470297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56351463271415141545254125 21131798726780678079470297)
        ·
          refine ⟨15848849045085508559602723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21131798726780678079470297 15848849045085508559602723)
          ·
            refine ⟨23773273567628262839404085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15848849045085508559602723 23773273567628262839404085)
            ·
              refine ⟨2228744396965149641194133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23773273567628262839404085 2228744396965149641194133)
              ·
                refine ⟨104472393607741389430975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2228744396965149641194133 104472393607741389430975)
                ·
                  rfl

theorem cell22_2746700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 6].length) (baseStart_2746700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746700 prefixEnd_2746700 := by exact prefixLift 2746700
  have htrace : WordTrace (prefixWord ++ tailWord_2746700) baseStart_2746700 baseEnd_2746700 := by
    simpa [prefixWord, tailWord_2746700, baseEnd_2746700] using wordTrace_append hprefix tailTrace_2746700
  have hstable : (prefixWord ++ tailWord_2746700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746700).length < 2 ^ (prefixWord ++ tailWord_2746700).sum := by decide
  have hdescent : baseEnd_2746700 < baseStart_2746700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746743 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 1, 7]
def baseStart_2746743 : Nat := 118140960795 + 2746743 * 2 ^ 59
def prefixEnd_2746743 : Nat := 4983230072969 + 3 ^ 40 * 2746743 * 2
def baseEnd_2746743 : Nat := 940266262248434726053643

theorem tailTrace_2746743 : CollatzResearch.WordTrace tailWord_2746743 prefixEnd_2746743 940266262248434726053643 := by
  unfold tailWord_2746743
  simp only [CollatzResearch.WordTrace]
  refine ⟨100181947488026692202044883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66787964992017794801363255 100181947488026692202044883)
  ·
    refine ⟨150272921232040038303067325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100181947488026692202044883 150272921232040038303067325)
    ·
      refine ⟨56352345462015014363650247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150272921232040038303067325 56352345462015014363650247)
      ·
        refine ⟨84528518193022521545475371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56352345462015014363650247 84528518193022521545475371)
        ·
          refine ⟨126792777289533782318213057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84528518193022521545475371 126792777289533782318213057)
          ·
            refine ⟨95094582967150336738659793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126792777289533782318213057 95094582967150336738659793)
            ·
              refine ⟨71320937225362752553994845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95094582967150336738659793 71320937225362752553994845)
              ·
                refine ⟨26745351459511032207748067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71320937225362752553994845 26745351459511032207748067)
                ·
                  refine ⟨40118027189266548311622101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26745351459511032207748067 40118027189266548311622101)
                  ·
                    refine ⟨940266262248434726053643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40118027189266548311622101 940266262248434726053643)
                    ·
                      rfl

theorem cell22_2746743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_2746743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746743 prefixEnd_2746743 := by exact prefixLift 2746743
  have htrace : WordTrace (prefixWord ++ tailWord_2746743) baseStart_2746743 baseEnd_2746743 := by
    simpa [prefixWord, tailWord_2746743, baseEnd_2746743] using wordTrace_append hprefix tailTrace_2746743
  have hstable : (prefixWord ++ tailWord_2746743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746743).length < 2 ^ (prefixWord ++ tailWord_2746743).sum := by decide
  have hdescent : baseEnd_2746743 < baseStart_2746743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746766 : List Nat := [4, 1, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_2746766 : Nat := 118140960795 + 2746766 * 2 ^ 59
def prefixEnd_2746766 : Nat := 4983230072969 + 3 ^ 40 * 2746766 * 2
def baseEnd_2746766 : Nat := 940274135618470332728573

theorem tailTrace_2746766 : CollatzResearch.WordTrace tailWord_2746766 prefixEnd_2746766 940274135618470332728573 := by
  unfold tailWord_2746766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12522848295867920891266519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66788524244628911420088101 12522848295867920891266519)
  ·
    refine ⟨18784272443801881336899779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12522848295867920891266519 18784272443801881336899779)
    ·
      refine ⟨28176408665702822005349669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18784272443801881336899779 28176408665702822005349669)
      ·
        refine ⟨5283076624819279126003063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28176408665702822005349669 5283076624819279126003063)
        ·
          refine ⟨7924614937228918689004595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283076624819279126003063 7924614937228918689004595)
          ·
            refine ⟨11886922405843378033506893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7924614937228918689004595 11886922405843378033506893)
            ·
              refine ⟨4457595902191266762565085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11886922405843378033506893 4457595902191266762565085)
              ·
                refine ⟨1671598463321725035961907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4457595902191266762565085 1671598463321725035961907)
                ·
                  refine ⟨2507397694982587553942861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671598463321725035961907 2507397694982587553942861)
                  ·
                    refine ⟨940274135618470332728573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507397694982587553942861 940274135618470332728573)
                    ·
                      rfl

theorem cell22_2746766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_2746766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746766 prefixEnd_2746766 := by exact prefixLift 2746766
  have htrace : WordTrace (prefixWord ++ tailWord_2746766) baseStart_2746766 baseEnd_2746766 := by
    simpa [prefixWord, tailWord_2746766, baseEnd_2746766] using wordTrace_append hprefix tailTrace_2746766
  have hstable : (prefixWord ++ tailWord_2746766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746766).length < 2 ^ (prefixWord ++ tailWord_2746766).sum := by decide
  have hdescent : baseEnd_2746766 < baseStart_2746766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746809 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 1, 4]
def baseStart_2746809 : Nat := 118140960795 + 2746809 * 2 ^ 59
def prefixEnd_2746809 : Nat := 4983230072969 + 3 ^ 40 * 2746809 * 2
def baseEnd_2746809 : Nat := 940288855397232553903441

theorem tailTrace_2746809 : CollatzResearch.WordTrace tailWord_2746809 prefixEnd_2746809 940288855397232553903441 := by
  unfold tailWord_2746809
  simp only [CollatzResearch.WordTrace]
  refine ⟨100184354705787585473947481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66789569803858390315964987 100184354705787585473947481)
  ·
    refine ⟨75138266029340689105460611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100184354705787585473947481 75138266029340689105460611)
    ·
      refine ⟨112707399044011033658190917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75138266029340689105460611 112707399044011033658190917)
      ·
        refine ⟨21132637320752068810910797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112707399044011033658190917 21132637320752068810910797)
        ·
          refine ⟨7924738995282025804091549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21132637320752068810910797 7924738995282025804091549)
          ·
            refine ⟨2971777123230759676534331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7924738995282025804091549 2971777123230759676534331)
            ·
              refine ⟨4457665684846139514801497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2971777123230759676534331 4457665684846139514801497)
              ·
                refine ⟨3343249263634604636101123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4457665684846139514801497 3343249263634604636101123)
                ·
                  refine ⟨5014873895451906954151685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343249263634604636101123 5014873895451906954151685)
                  ·
                    refine ⟨940288855397232553903441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5014873895451906954151685 940288855397232553903441)
                    ·
                      rfl

theorem cell22_2746809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 4].length) (baseStart_2746809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746809 prefixEnd_2746809 := by exact prefixLift 2746809
  have htrace : WordTrace (prefixWord ++ tailWord_2746809) baseStart_2746809 baseEnd_2746809 := by
    simpa [prefixWord, tailWord_2746809, baseEnd_2746809] using wordTrace_append hprefix tailTrace_2746809
  have hstable : (prefixWord ++ tailWord_2746809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746809).length < 2 ^ (prefixWord ++ tailWord_2746809).sum := by decide
  have hdescent : baseEnd_2746809 < baseStart_2746809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746837 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2746837 : Nat := 118140960795 + 2746837 * 2 ^ 59
def prefixEnd_2746837 : Nat := 4983230072969 + 3 ^ 40 * 2746837 * 2
def baseEnd_2746837 : Nat := 940298440369449814203355

theorem tailTrace_2746837 : CollatzResearch.WordTrace tailWord_2746837 prefixEnd_2746837 940298440369449814203355 := by
  unfold tailWord_2746837
  simp only [CollatzResearch.WordTrace]
  refine ⟨100185375949686146255966765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66790250633124097503977843 100185375949686146255966765)
  ·
    refine ⟨37569515981132304845987537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100185375949686146255966765 37569515981132304845987537)
    ·
      refine ⟨28177136985849228634490653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37569515981132304845987537 28177136985849228634490653)
      ·
        refine ⟨10566426369693460737933995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28177136985849228634490653 10566426369693460737933995)
        ·
          refine ⟨15849639554540191106900993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10566426369693460737933995 15849639554540191106900993)
          ·
            refine ⟨11887229665905143330175745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15849639554540191106900993 11887229665905143330175745)
            ·
              refine ⟨8915422249428857497631809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11887229665905143330175745 8915422249428857497631809)
              ·
                refine ⟨6686566687071643123223857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8915422249428857497631809 6686566687071643123223857)
                ·
                  refine ⟨5014925015303732342417893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6686566687071643123223857 5014925015303732342417893)
                  ·
                    refine ⟨940298440369449814203355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5014925015303732342417893 940298440369449814203355)
                    ·
                      rfl

theorem cell22_2746837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2746837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746837 prefixEnd_2746837 := by exact prefixLift 2746837
  have htrace : WordTrace (prefixWord ++ tailWord_2746837) baseStart_2746837 baseEnd_2746837 := by
    simpa [prefixWord, tailWord_2746837, baseEnd_2746837] using wordTrace_append hprefix tailTrace_2746837
  have hstable : (prefixWord ++ tailWord_2746837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746837).length < 2 ^ (prefixWord ++ tailWord_2746837).sum := by decide
  have hdescent : baseEnd_2746837 < baseStart_2746837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746865 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_2746865 : Nat := 118140960795 + 2746865 * 2 ^ 59
def prefixEnd_2746865 : Nat := 4983230072969 + 3 ^ 40 * 2746865 * 2
def baseEnd_2746865 : Nat := 940308025341667074503269

theorem tailTrace_2746865 : CollatzResearch.WordTrace tailWord_2746865 prefixEnd_2746865 940308025341667074503269 := by
  unfold tailWord_2746865
  simp only [CollatzResearch.WordTrace]
  refine ⟨100186397193584707037986049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66790931462389804691990699 100186397193584707037986049)
  ·
    refine ⟨75139797895188530278489537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100186397193584707037986049 75139797895188530278489537)
    ·
      refine ⟨56354848421391397708867153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75139797895188530278489537 56354848421391397708867153)
      ·
        refine ⟨42266136316043548281650365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56354848421391397708867153 42266136316043548281650365)
        ·
          refine ⟨15849801118516330605618887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42266136316043548281650365 15849801118516330605618887)
          ·
            refine ⟨23774701677774495908428331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15849801118516330605618887 23774701677774495908428331)
            ·
              refine ⟨35662052516661743862642497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23774701677774495908428331 35662052516661743862642497)
              ·
                refine ⟨26746539387496307896981873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35662052516661743862642497 26746539387496307896981873)
                ·
                  refine ⟨20059904540622230922736405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26746539387496307896981873 20059904540622230922736405)
                  ·
                    refine ⟨940308025341667074503269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20059904540622230922736405 940308025341667074503269)
                    ·
                      rfl

theorem cell22_2746865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_2746865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746865 prefixEnd_2746865 := by exact prefixLift 2746865
  have htrace : WordTrace (prefixWord ++ tailWord_2746865) baseStart_2746865 baseEnd_2746865 := by
    simpa [prefixWord, tailWord_2746865, baseEnd_2746865] using wordTrace_append hprefix tailTrace_2746865
  have hstable : (prefixWord ++ tailWord_2746865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746865).length < 2 ^ (prefixWord ++ tailWord_2746865).sum := by decide
  have hdescent : baseEnd_2746865 < baseStart_2746865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746867 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 3, 3]
def baseStart_2746867 : Nat := 118140960795 + 2746867 * 2 ^ 59
def prefixEnd_2746867 : Nat := 4983230072969 + 3 ^ 40 * 2746867 * 2
def baseEnd_2746867 : Nat := 940308709982539735953263

theorem tailTrace_2746867 : CollatzResearch.WordTrace tailWord_2746867 prefixEnd_2746867 940308709982539735953263 := by
  unfold tailWord_2746867
  simp only [CollatzResearch.WordTrace]
  refine ⟨100186470139577461379558855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66790980093051640919705903 100186470139577461379558855)
  ·
    refine ⟨150279705209366192069338283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100186470139577461379558855 150279705209366192069338283)
    ·
      refine ⟨225419557814049288104007425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150279705209366192069338283 225419557814049288104007425)
      ·
        refine ⟨169064668360536966078005569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225419557814049288104007425 169064668360536966078005569)
        ·
          refine ⟨126798501270402724558504177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169064668360536966078005569 126798501270402724558504177)
          ·
            refine ⟨95098875952802043418878133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126798501270402724558504177 95098875952802043418878133)
            ·
              refine ⟨8915519620575191570519825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95098875952802043418878133 8915519620575191570519825)
              ·
                refine ⟨6686639715431393677889869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8915519620575191570519825 6686639715431393677889869)
                ·
                  refine ⟨2507489893286772629208701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6686639715431393677889869 2507489893286772629208701)
                  ·
                    refine ⟨940308709982539735953263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507489893286772629208701 940308709982539735953263)
                    ·
                      rfl

theorem cell22_2746867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 3].length) (baseStart_2746867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746867 prefixEnd_2746867 := by exact prefixLift 2746867
  have htrace : WordTrace (prefixWord ++ tailWord_2746867) baseStart_2746867 baseEnd_2746867 := by
    simpa [prefixWord, tailWord_2746867, baseEnd_2746867] using wordTrace_append hprefix tailTrace_2746867
  have hstable : (prefixWord ++ tailWord_2746867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746867).length < 2 ^ (prefixWord ++ tailWord_2746867).sum := by decide
  have hdescent : baseEnd_2746867 < baseStart_2746867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746886 : List Nat := [6, 2, 1, 1, 1, 2, 9]
def baseStart_2746886 : Nat := 118140960795 + 2746886 * 2 ^ 59
def prefixEnd_2746886 : Nat := 4983230072969 + 3 ^ 40 * 2746886 * 2
def baseEnd_2746886 : Nat := 34826489410030741471415

theorem tailTrace_2746886 : CollatzResearch.WordTrace tailWord_2746886 prefixEnd_2746886 34826489410030741471415 := by
  unfold tailWord_2746886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3130848847703394613265641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66791442084339085083000341 3130848847703394613265641)
  ·
    refine ⟨2348136635777545959949231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3130848847703394613265641 2348136635777545959949231)
    ·
      refine ⟨3522204953666318939923847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2348136635777545959949231 3522204953666318939923847)
      ·
        refine ⟨5283307430499478409885771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3522204953666318939923847 5283307430499478409885771)
        ·
          refine ⟨7924961145749217614828657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283307430499478409885771 7924961145749217614828657)
          ·
            refine ⟨5943720859311913211121493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7924961145749217614828657 5943720859311913211121493)
            ·
              refine ⟨34826489410030741471415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5943720859311913211121493 34826489410030741471415)
              ·
                rfl

theorem cell22_2746886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 9].length) (baseStart_2746886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746886 prefixEnd_2746886 := by exact prefixLift 2746886
  have htrace : WordTrace (prefixWord ++ tailWord_2746886) baseStart_2746886 baseEnd_2746886 := by
    simpa [prefixWord, tailWord_2746886, baseEnd_2746886] using wordTrace_append hprefix tailTrace_2746886
  have hstable : (prefixWord ++ tailWord_2746886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746886).length < 2 ^ (prefixWord ++ tailWord_2746886).sum := by decide
  have hdescent : baseEnd_2746886 < baseStart_2746886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746895 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 2, 5]
def baseStart_2746895 : Nat := 118140960795 + 2746895 * 2 ^ 59
def prefixEnd_2746895 : Nat := 4983230072969 + 3 ^ 40 * 2746895 * 2
def baseEnd_2746895 : Nat := 940318294954756996253177

theorem tailTrace_2746895 : CollatzResearch.WordTrace tailWord_2746895 prefixEnd_2746895 940318294954756996253177 := by
  unfold tailWord_2746895
  simp only [CollatzResearch.WordTrace]
  refine ⟨100187491383476022161578139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66791660922317348107718759 100187491383476022161578139)
  ·
    refine ⟨150281237075214033242367209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100187491383476022161578139 150281237075214033242367209)
    ·
      refine ⟨112710927806410524931775407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150281237075214033242367209 112710927806410524931775407)
      ·
        refine ⟨169066391709615787397663111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112710927806410524931775407 169066391709615787397663111)
        ·
          refine ⟨253599587564423681096494667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169066391709615787397663111 253599587564423681096494667)
          ·
            refine ⟨380399381346635521644742001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253599587564423681096494667 380399381346635521644742001)
            ·
              refine ⟨285299536009976641233556501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380399381346635521644742001 285299536009976641233556501)
              ·
                refine ⟨13373415750467655057822961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 285299536009976641233556501 13373415750467655057822961)
                ·
                  refine ⟨10030061812850741293367221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13373415750467655057822961 10030061812850741293367221)
                  ·
                    refine ⟨940318294954756996253177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10030061812850741293367221 940318294954756996253177)
                    ·
                      rfl

theorem cell22_2746895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_2746895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746895 prefixEnd_2746895 := by exact prefixLift 2746895
  have htrace : WordTrace (prefixWord ++ tailWord_2746895) baseStart_2746895 baseEnd_2746895 := by
    simpa [prefixWord, tailWord_2746895, baseEnd_2746895] using wordTrace_append hprefix tailTrace_2746895
  have hstable : (prefixWord ++ tailWord_2746895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746895).length < 2 ^ (prefixWord ++ tailWord_2746895).sum := by decide
  have hdescent : baseEnd_2746895 < baseStart_2746895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2746989 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_2746989 : Nat := 118140960795 + 2746989 * 2 ^ 59
def prefixEnd_2746989 : Nat := 4983230072969 + 3 ^ 40 * 2746989 * 2
def baseEnd_2746989 : Nat := 940350473075772084402889

theorem tailTrace_2746989 : CollatzResearch.WordTrace tailWord_2746989 prefixEnd_2746989 940350473075772084402889 := by
  unfold tailWord_2746989
  simp only [CollatzResearch.WordTrace]
  refine ⟨100190919845135476215500021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66793946563423650810333347 100190919845135476215500021)
  ·
    refine ⟨9392898735481450895203127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100190919845135476215500021 9392898735481450895203127)
    ·
      refine ⟨14089348103222176342804691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9392898735481450895203127 14089348103222176342804691)
      ·
        refine ⟨21134022154833264514207037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14089348103222176342804691 21134022154833264514207037)
        ·
          refine ⟨7925258308062474192827639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21134022154833264514207037 7925258308062474192827639)
          ·
            refine ⟨11887887462093711289241459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7925258308062474192827639 11887887462093711289241459)
            ·
              refine ⟨17831831193140566933862189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11887887462093711289241459 17831831193140566933862189)
              ·
                refine ⟨6686936697427712600198321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17831831193140566933862189 6686936697427712600198321)
                ·
                  refine ⟨5015202523070784450148741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6686936697427712600198321 5015202523070784450148741)
                  ·
                    refine ⟨940350473075772084402889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5015202523070784450148741 940350473075772084402889)
                    ·
                      rfl

theorem cell22_2746989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_2746989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2746989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2746989 prefixEnd_2746989 := by exact prefixLift 2746989
  have htrace : WordTrace (prefixWord ++ tailWord_2746989) baseStart_2746989 baseEnd_2746989 := by
    simpa [prefixWord, tailWord_2746989, baseEnd_2746989] using wordTrace_append hprefix tailTrace_2746989
  have hstable : (prefixWord ++ tailWord_2746989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2746989).length < 2 ^ (prefixWord ++ tailWord_2746989).sum := by decide
  have hdescent : baseEnd_2746989 < baseStart_2746989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2746989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747036 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 3, 3]
def baseStart_2747036 : Nat := 118140960795 + 2747036 * 2 ^ 59
def prefixEnd_2747036 : Nat := 4983230072969 + 3 ^ 40 * 2747036 * 2
def baseEnd_2747036 : Nat := 940366562136279628477745

theorem tailTrace_2747036 : CollatzResearch.WordTrace tailWord_2747036 prefixEnd_2747036 940366562136279628477745 := by
  unfold tailWord_2747036
  simp only [CollatzResearch.WordTrace]
  refine ⟨50096317037982601621230481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66795089383976802161640641 50096317037982601621230481)
  ·
    refine ⟨37572237778486951215922861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50096317037982601621230481 37572237778486951215922861)
    ·
      refine ⟨14089589166932606705971073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37572237778486951215922861 14089589166932606705971073)
      ·
        refine ⟨10567191875199455029478305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14089589166932606705971073 10567191875199455029478305)
        ·
          refine ⟨7925393906399591272108729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10567191875199455029478305 7925393906399591272108729)
          ·
            refine ⟨5944045429799693454081547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7925393906399591272108729 5944045429799693454081547)
            ·
              refine ⟨8916068144699540181122321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5944045429799693454081547 8916068144699540181122321)
              ·
                refine ⟨6687051108524655135841741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8916068144699540181122321 6687051108524655135841741)
                ·
                  refine ⟨2507644165696745675940653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6687051108524655135841741 2507644165696745675940653)
                  ·
                    refine ⟨940366562136279628477745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507644165696745675940653 940366562136279628477745)
                    ·
                      rfl

theorem cell22_2747036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_2747036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747036 prefixEnd_2747036 := by exact prefixLift 2747036
  have htrace : WordTrace (prefixWord ++ tailWord_2747036) baseStart_2747036 baseEnd_2747036 := by
    simpa [prefixWord, tailWord_2747036, baseEnd_2747036] using wordTrace_append hprefix tailTrace_2747036
  have hstable : (prefixWord ++ tailWord_2747036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747036).length < 2 ^ (prefixWord ++ tailWord_2747036).sum := by decide
  have hdescent : baseEnd_2747036 < baseStart_2747036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747053 : List Nat := [1, 5, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_2747053 : Nat := 118140960795 + 2747053 * 2 ^ 59
def prefixEnd_2747053 : Nat := 4983230072969 + 3 ^ 40 * 2747053 * 2
def baseEnd_2747053 : Nat := 940372381583697250802693

theorem tailTrace_2747053 : CollatzResearch.WordTrace tailWord_2747053 prefixEnd_2747053 940372381583697250802693 := by
  unfold tailWord_2747053
  simp only [CollatzResearch.WordTrace]
  refine ⟨100193254116903615145829813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66795502744602410097219875 100193254116903615145829813)
  ·
    refine ⟨9393117573459713919921545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100193254116903615145829813 9393117573459713919921545)
    ·
      refine ⟨7044838180094785439941159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9393117573459713919921545 7044838180094785439941159)
      ·
        refine ⟨10567257270142178159911739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7044838180094785439941159 10567257270142178159911739)
        ·
          refine ⟨15850885905213267239867609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10567257270142178159911739 15850885905213267239867609)
          ·
            refine ⟨11888164428909950429900707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15850885905213267239867609 11888164428909950429900707)
            ·
              refine ⟨17832246643364925644851061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11888164428909950429900707 17832246643364925644851061)
              ·
                refine ⟨1671773122815461779204787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17832246643364925644851061 1671773122815461779204787)
                ·
                  refine ⟨2507659684223192668807181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671773122815461779204787 2507659684223192668807181)
                  ·
                    refine ⟨940372381583697250802693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507659684223192668807181 940372381583697250802693)
                    ·
                      rfl

theorem cell22_2747053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_2747053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747053 prefixEnd_2747053 := by exact prefixLift 2747053
  have htrace : WordTrace (prefixWord ++ tailWord_2747053) baseStart_2747053 baseEnd_2747053 := by
    simpa [prefixWord, tailWord_2747053, baseEnd_2747053] using wordTrace_append hprefix tailTrace_2747053
  have hstable : (prefixWord ++ tailWord_2747053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747053).length < 2 ^ (prefixWord ++ tailWord_2747053).sum := by decide
  have hdescent : baseEnd_2747053 < baseStart_2747053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747096 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 1, 4]
def baseStart_2747096 : Nat := 118140960795 + 2747096 * 2 ^ 59
def prefixEnd_2747096 : Nat := 4983230072969 + 3 ^ 40 * 2747096 * 2
def baseEnd_2747096 : Nat := 940387101362459471977561

theorem tailTrace_2747096 : CollatzResearch.WordTrace tailWord_2747096 prefixEnd_2747096 940387101362459471977561 := by
  unfold tailWord_2747096
  simp only [CollatzResearch.WordTrace]
  refine ⟨50097411227873916744822571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66796548303831888993096761 50097411227873916744822571)
  ·
    refine ⟨75146116841810875117233857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50097411227873916744822571 75146116841810875117233857)
    ·
      refine ⟨56359587631358156337925393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75146116841810875117233857 56359587631358156337925393)
      ·
        refine ⟨42269690723518617253444045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56359587631358156337925393 42269690723518617253444045)
        ·
          refine ⟨15851134021319481470041517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42269690723518617253444045 15851134021319481470041517)
          ·
            refine ⟨5944175257994805551265569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15851134021319481470041517 5944175257994805551265569)
            ·
              refine ⟨4458131443496104163449177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5944175257994805551265569 4458131443496104163449177)
              ·
                refine ⟨3343598582622078122586883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4458131443496104163449177 3343598582622078122586883)
                ·
                  refine ⟨5015397873933117183880325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343598582622078122586883 5015397873933117183880325)
                  ·
                    refine ⟨940387101362459471977561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5015397873933117183880325 940387101362459471977561)
                    ·
                      rfl

theorem cell22_2747096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_2747096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747096 prefixEnd_2747096 := by exact prefixLift 2747096
  have htrace : WordTrace (prefixWord ++ tailWord_2747096) baseStart_2747096 baseEnd_2747096 := by
    simpa [prefixWord, tailWord_2747096, baseEnd_2747096] using wordTrace_append hprefix tailTrace_2747096
  have hstable : (prefixWord ++ tailWord_2747096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747096).length < 2 ^ (prefixWord ++ tailWord_2747096).sum := by decide
  have hdescent : baseEnd_2747096 < baseStart_2747096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747126 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_2747126 : Nat := 118140960795 + 2747126 * 2 ^ 59
def prefixEnd_2747126 : Nat := 4983230072969 + 3 ^ 40 * 2747126 * 2
def baseEnd_2747126 : Nat := 940397370975549393727469

theorem tailTrace_2747126 : CollatzResearch.WordTrace tailWord_2747126 prefixEnd_2747126 940397370975549393727469 := by
  unfold tailWord_2747126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262244790352446788327327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66797277763759432408824821 6262244790352446788327327)
  ·
    refine ⟨9393367185528670182490991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6262244790352446788327327 9393367185528670182490991)
    ·
      refine ⟨14090050778293005273736487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9393367185528670182490991 14090050778293005273736487)
      ·
        refine ⟨21135076167439507910604731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14090050778293005273736487 21135076167439507910604731)
        ·
          refine ⟨31702614251159261865907097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21135076167439507910604731 31702614251159261865907097)
          ·
            refine ⟨23776960688369446399430323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31702614251159261865907097 23776960688369446399430323)
            ·
              refine ⟨35665441032554169599145485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23776960688369446399430323 35665441032554169599145485)
              ·
                refine ⟨13374540387207813599679557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35665441032554169599145485 13374540387207813599679557)
                ·
                  refine ⟨2507726322601465049939917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13374540387207813599679557 2507726322601465049939917)
                  ·
                    refine ⟨940397370975549393727469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507726322601465049939917 940397370975549393727469)
                    ·
                      rfl

theorem cell22_2747126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_2747126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747126 prefixEnd_2747126 := by exact prefixLift 2747126
  have htrace : WordTrace (prefixWord ++ tailWord_2747126) baseStart_2747126 baseEnd_2747126 := by
    simpa [prefixWord, tailWord_2747126, baseEnd_2747126] using wordTrace_append hprefix tailTrace_2747126
  have hstable : (prefixWord ++ tailWord_2747126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747126).length < 2 ^ (prefixWord ++ tailWord_2747126).sum := by decide
  have hdescent : baseEnd_2747126 < baseStart_2747126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747143 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 2, 3]
def baseStart_2747143 : Nat := 118140960795 + 2747143 * 2 ^ 59
def prefixEnd_2747143 : Nat := 4983230072969 + 3 ^ 40 * 2747143 * 2
def baseEnd_2747143 : Nat := 940403190422967016052417

theorem tailTrace_2747143 : CollatzResearch.WordTrace tailWord_2747143 prefixEnd_2747143 940403190422967016052417 := by
  unfold tailWord_2747143
  simp only [CollatzResearch.WordTrace]
  refine ⟨100196536686577560516606083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66797691124385040344404055 100196536686577560516606083)
  ·
    refine ⟨150294805029866340774909125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100196536686577560516606083 150294805029866340774909125)
    ·
      refine ⟨28180275943099938895295461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150294805029866340774909125 28180275943099938895295461)
      ·
        refine ⟨5283801739331238542867899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28180275943099938895295461 5283801739331238542867899)
        ·
          refine ⟨7925702608996857814301849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5283801739331238542867899 7925702608996857814301849)
          ·
            refine ⟨5944276956747643360726387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7925702608996857814301849 5944276956747643360726387)
            ·
              refine ⟨8916415435121465041089581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5944276956747643360726387 8916415435121465041089581)
              ·
                refine ⟨3343655788170549390408593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8916415435121465041089581 3343655788170549390408593)
                ·
                  refine ⟨2507741841127912042806445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3343655788170549390408593 2507741841127912042806445)
                  ·
                    refine ⟨940403190422967016052417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507741841127912042806445 940403190422967016052417)
                    ·
                      rfl

theorem cell22_2747143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_2747143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747143 prefixEnd_2747143 := by exact prefixLift 2747143
  have htrace : WordTrace (prefixWord ++ tailWord_2747143) baseStart_2747143 baseEnd_2747143 := by
    simpa [prefixWord, tailWord_2747143, baseEnd_2747143] using wordTrace_append hprefix tailTrace_2747143
  have hstable : (prefixWord ++ tailWord_2747143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747143).length < 2 ^ (prefixWord ++ tailWord_2747143).sum := by decide
  have hdescent : baseEnd_2747143 < baseStart_2747143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747190 : List Nat := [5, 1, 2, 2, 3, 1, 1, 7]
def baseStart_2747190 : Nat := 118140960795 + 2747190 * 2 ^ 59
def prefixEnd_2747190 : Nat := 4983230072969 + 3 ^ 40 * 2747190 * 2
def baseEnd_2747190 : Nat := 104491031053719395569697

theorem tailTrace_2747190 : CollatzResearch.WordTrace tailWord_2747190 prefixEnd_2747190 104491031053719395569697 := by
  unfold tailWord_2747190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262390682337955471472939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66798833944938191695711349 6262390682337955471472939)
  ·
    refine ⟨9393586023506933207209409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6262390682337955471472939 9393586023506933207209409)
    ·
      refine ⟨7045189517630199905407057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9393586023506933207209409 7045189517630199905407057)
      ·
        refine ⟨5283892138222649929055293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7045189517630199905407057 5283892138222649929055293)
        ·
          refine ⟨1981459551833493723395735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5283892138222649929055293 1981459551833493723395735)
          ·
            refine ⟨2972189327750240585093603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1981459551833493723395735 2972189327750240585093603)
            ·
              refine ⟨4458283991625360877640405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2972189327750240585093603 4458283991625360877640405)
              ·
                refine ⟨104491031053719395569697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4458283991625360877640405 104491031053719395569697)
                ·
                  rfl

theorem cell22_2747190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_2747190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747190 prefixEnd_2747190 := by exact prefixLift 2747190
  have htrace : WordTrace (prefixWord ++ tailWord_2747190) baseStart_2747190 baseEnd_2747190 := by
    simpa [prefixWord, tailWord_2747190, baseEnd_2747190] using wordTrace_append hprefix tailTrace_2747190
  have hstable : (prefixWord ++ tailWord_2747190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747190).length < 2 ^ (prefixWord ++ tailWord_2747190).sum := by decide
  have hdescent : baseEnd_2747190 < baseStart_2747190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747199 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 1, 7]
def baseStart_2747199 : Nat := 118140960795 + 2747199 * 2 ^ 59
def prefixEnd_2747199 : Nat := 4983230072969 + 3 ^ 40 * 2747199 * 2
def baseEnd_2747199 : Nat := 940422360367401536652245

theorem tailTrace_2747199 : CollatzResearch.WordTrace tailWord_2747199 prefixEnd_2747199 940422360367401536652245 := by
  unfold tailWord_2747199
  simp only [CollatzResearch.WordTrace]
  refine ⟨100198579174374682080644651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66799052782916454720429767 100198579174374682080644651)
  ·
    refine ⟨150297868761562023120966977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100198579174374682080644651 150297868761562023120966977)
    ·
      refine ⟨112723401571171517340725233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150297868761562023120966977 112723401571171517340725233)
      ·
        refine ⟨84542551178378638005543925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112723401571171517340725233 84542551178378638005543925)
        ·
          refine ⟨7925864172972997313019743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84542551178378638005543925 7925864172972997313019743)
          ·
            refine ⟨11888796259459495969529615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7925864172972997313019743 11888796259459495969529615)
            ·
              refine ⟨17833194389189243954294423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11888796259459495969529615 17833194389189243954294423)
              ·
                refine ⟨26749791583783865931441635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17833194389189243954294423 26749791583783865931441635)
                ·
                  refine ⟨40124687375675798897162453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26749791583783865931441635 40124687375675798897162453)
                  ·
                    refine ⟨940422360367401536652245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40124687375675798897162453 940422360367401536652245)
                    ·
                      rfl

theorem cell22_2747199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_2747199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747199 prefixEnd_2747199 := by exact prefixLift 2747199
  have htrace : WordTrace (prefixWord ++ tailWord_2747199) baseStart_2747199 baseEnd_2747199 := by
    simpa [prefixWord, tailWord_2747199, baseEnd_2747199] using wordTrace_append hprefix tailTrace_2747199
  have hstable : (prefixWord ++ tailWord_2747199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747199).length < 2 ^ (prefixWord ++ tailWord_2747199).sum := by decide
  have hdescent : baseEnd_2747199 < baseStart_2747199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747231 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 1, 4]
def baseStart_2747231 : Nat := 118140960795 + 2747231 * 2 ^ 59
def prefixEnd_2747231 : Nat := 4983230072969 + 3 ^ 40 * 2747231 * 2
def baseEnd_2747231 : Nat := 940433314621364119852147

theorem tailTrace_2747231 : CollatzResearch.WordTrace tailWord_2747231 prefixEnd_2747231 940433314621364119852147 := by
  unfold tailWord_2747231
  simp only [CollatzResearch.WordTrace]
  refine ⟨100199746310258751545809547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66799830873505834363873031 100199746310258751545809547)
  ·
    refine ⟨150299619465388127318714321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100199746310258751545809547 150299619465388127318714321)
    ·
      refine ⟨112724714599041095489035741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150299619465388127318714321 112724714599041095489035741)
      ·
        refine ⟨42271767974640410808388403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112724714599041095489035741 42271767974640410808388403)
        ·
          refine ⟨63407651961960616212582605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42271767974640410808388403 63407651961960616212582605)
          ·
            refine ⟨23777869485735231079718477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63407651961960616212582605 23777869485735231079718477)
            ·
              refine ⟨8916701057150711654894429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23777869485735231079718477 8916701057150711654894429)
              ·
                refine ⟨3343762896431516870585411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8916701057150711654894429 3343762896431516870585411)
                ·
                  refine ⟨5015644344647275305878117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343762896431516870585411 5015644344647275305878117)
                  ·
                    refine ⟨940433314621364119852147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5015644344647275305878117 940433314621364119852147)
                    ·
                      rfl

theorem cell22_2747231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_2747231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747231 prefixEnd_2747231 := by exact prefixLift 2747231
  have htrace : WordTrace (prefixWord ++ tailWord_2747231) baseStart_2747231 baseEnd_2747231 := by
    simpa [prefixWord, tailWord_2747231, baseEnd_2747231] using wordTrace_append hprefix tailTrace_2747231
  have hstable : (prefixWord ++ tailWord_2747231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747231).length < 2 ^ (prefixWord ++ tailWord_2747231).sum := by decide
  have hdescent : baseEnd_2747231 < baseStart_2747231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747259 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 1, 6]
def baseStart_2747259 : Nat := 118140960795 + 2747259 * 2 ^ 59
def prefixEnd_2747259 : Nat := 4983230072969 + 3 ^ 40 * 2747259 * 2
def baseEnd_2747259 : Nat := 940442899593581380152061

theorem tailTrace_2747259 : CollatzResearch.WordTrace tailWord_2747259 prefixEnd_2747259 940442899593581380152061 := by
  unfold tailWord_2747259
  simp only [CollatzResearch.WordTrace]
  refine ⟨100200767554157312327828831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66800511702771541551885887 100200767554157312327828831)
  ·
    refine ⟨150301151331235968491743247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100200767554157312327828831 150301151331235968491743247)
    ·
      refine ⟨225451726996853952737614871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150301151331235968491743247 225451726996853952737614871)
      ·
        refine ⟨338177590495280929106422307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225451726996853952737614871 338177590495280929106422307)
        ·
          refine ⟨507266385742921393659633461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338177590495280929106422307 507266385742921393659633461)
          ·
            refine ⟨47556223663398880655590637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 507266385742921393659633461 47556223663398880655590637)
            ·
              refine ⟨17833583873774580245846489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47556223663398880655590637 17833583873774580245846489)
              ·
                refine ⟨13375187905330935184384867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17833583873774580245846489 13375187905330935184384867)
                ·
                  refine ⟨20062781857996402776577301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13375187905330935184384867 20062781857996402776577301)
                  ·
                    refine ⟨940442899593581380152061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20062781857996402776577301 940442899593581380152061)
                    ·
                      rfl

theorem cell22_2747259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_2747259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747259 prefixEnd_2747259 := by exact prefixLift 2747259
  have htrace : WordTrace (prefixWord ++ tailWord_2747259) baseStart_2747259 baseEnd_2747259 := by
    simpa [prefixWord, tailWord_2747259, baseEnd_2747259] using wordTrace_append hprefix tailTrace_2747259
  have hstable : (prefixWord ++ tailWord_2747259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747259).length < 2 ^ (prefixWord ++ tailWord_2747259).sum := by decide
  have hdescent : baseEnd_2747259 < baseStart_2747259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747261 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_2747261 : Nat := 118140960795 + 2747261 * 2 ^ 59
def prefixEnd_2747261 : Nat := 4983230072969 + 3 ^ 40 * 2747261 * 2
def baseEnd_2747261 : Nat := 940443584234454041602055

theorem tailTrace_2747261 : CollatzResearch.WordTrace tailWord_2747261 prefixEnd_2747261 940443584234454041602055 := by
  unfold tailWord_2747261
  simp only [CollatzResearch.WordTrace]
  refine ⟨100200840500150066669401637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66800560333433377779601091 100200840500150066669401637)
  ·
    refine ⟨18787657593778137500512807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100200840500150066669401637 18787657593778137500512807)
    ·
      refine ⟨28181486390667206250769211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18787657593778137500512807 28181486390667206250769211)
      ·
        refine ⟨42272229586000809376153817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28181486390667206250769211 42272229586000809376153817)
        ·
          refine ⟨31704172189500607032115363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42272229586000809376153817 31704172189500607032115363)
          ·
            refine ⟨47556258284250910548173045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31704172189500607032115363 47556258284250910548173045)
            ·
              refine ⟨4458399214148522863891223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47556258284250910548173045 4458399214148522863891223)
              ·
                refine ⟨6687598821222784295836835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458399214148522863891223 6687598821222784295836835)
                ·
                  refine ⟨10031398231834176443755253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6687598821222784295836835 10031398231834176443755253)
                  ·
                    refine ⟨940443584234454041602055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10031398231834176443755253 940443584234454041602055)
                    ·
                      rfl

theorem cell22_2747261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_2747261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747261 prefixEnd_2747261 := by exact prefixLift 2747261
  have htrace : WordTrace (prefixWord ++ tailWord_2747261) baseStart_2747261 baseEnd_2747261 := by
    simpa [prefixWord, tailWord_2747261, baseEnd_2747261] using wordTrace_append hprefix tailTrace_2747261
  have hstable : (prefixWord ++ tailWord_2747261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747261).length < 2 ^ (prefixWord ++ tailWord_2747261).sum := by decide
  have hdescent : baseEnd_2747261 < baseStart_2747261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747340 : List Nat := [2, 2, 1, 4, 1, 1, 2, 5, 1, 3]
def baseStart_2747340 : Nat := 118140960795 + 2747340 * 2 ^ 59
def prefixEnd_2747340 : Nat := 4983230072969 + 3 ^ 40 * 2747340 * 2
def baseEnd_2747340 : Nat := 940470627548924168876813

theorem tailTrace_2747340 : CollatzResearch.WordTrace tailWord_2747340 prefixEnd_2747340 940470627548924168876813 := by
  unfold tailWord_2747340
  simp only [CollatzResearch.WordTrace]
  refine ⟨50101860933431931580763737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66802481244575908774351649 50101860933431931580763737)
  ·
    refine ⟨37576395700073948685572803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50101860933431931580763737 37576395700073948685572803)
    ·
      refine ⟨56364593550110923028359205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37576395700073948685572803 56364593550110923028359205)
      ·
        refine ⟨10568361290645798067817351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56364593550110923028359205 10568361290645798067817351)
        ·
          refine ⟨15852541935968697101726027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10568361290645798067817351 15852541935968697101726027)
          ·
            refine ⟨23778812903953045652589041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15852541935968697101726027 23778812903953045652589041)
            ·
              refine ⟨17834109677964784239441781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23778812903953045652589041 17834109677964784239441781)
              ·
                refine ⟨1671947782309198522447667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17834109677964784239441781 1671947782309198522447667)
                ·
                  refine ⟨2507921673463797783671501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671947782309198522447667 2507921673463797783671501)
                  ·
                    refine ⟨940470627548924168876813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507921673463797783671501 940470627548924168876813)
                    ·
                      rfl

theorem cell22_2747340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_2747340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747340 prefixEnd_2747340 := by exact prefixLift 2747340
  have htrace : WordTrace (prefixWord ++ tailWord_2747340) baseStart_2747340 baseEnd_2747340 := by
    simpa [prefixWord, tailWord_2747340, baseEnd_2747340] using wordTrace_append hprefix tailTrace_2747340
  have hstable : (prefixWord ++ tailWord_2747340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747340).length < 2 ^ (prefixWord ++ tailWord_2747340).sum := by decide
  have hdescent : baseEnd_2747340 < baseStart_2747340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747353 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 5]
def baseStart_2747353 : Nat := 118140960795 + 2747353 * 2 ^ 59
def prefixEnd_2747353 : Nat := 4983230072969 + 3 ^ 40 * 2747353 * 2
def baseEnd_2747353 : Nat := 313491692571532156100591

theorem tailTrace_2747353 : CollatzResearch.WordTrace tailWord_2747353 prefixEnd_2747353 313491692571532156100591 := by
  unfold tailWord_2747353
  simp only [CollatzResearch.WordTrace]
  refine ⟨100204196015816766381750713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66802797343877844254500475 100204196015816766381750713)
  ·
    refine ⟨75153147011862574786313035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100204196015816766381750713 75153147011862574786313035)
    ·
      refine ⟨112729720517793862179469553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75153147011862574786313035 112729720517793862179469553)
      ·
        refine ⟨84547290388345396634602165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112729720517793862179469553 84547290388345396634602165)
        ·
          refine ⟨7926308473907380934493953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84547290388345396634602165 7926308473907380934493953)
          ·
            refine ⟨5944731355430535700870465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7926308473907380934493953 5944731355430535700870465)
            ·
              refine ⟨4458548516572901775652849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5944731355430535700870465 4458548516572901775652849)
              ·
                refine ⟨3343911387429676331739637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4458548516572901775652849 3343911387429676331739637)
                ·
                  refine ⟨313491692571532156100591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3343911387429676331739637 313491692571532156100591)
                  ·
                    rfl

theorem cell22_2747353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_2747353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747353 prefixEnd_2747353 := by exact prefixLift 2747353
  have htrace : WordTrace (prefixWord ++ tailWord_2747353) baseStart_2747353 baseEnd_2747353 := by
    simpa [prefixWord, tailWord_2747353, baseEnd_2747353] using wordTrace_append hprefix tailTrace_2747353
  have hstable : (prefixWord ++ tailWord_2747353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747353).length < 2 ^ (prefixWord ++ tailWord_2747353).sum := by decide
  have hdescent : baseEnd_2747353 < baseStart_2747353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747357 : List Nat := [1, 4, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_2747357 : Nat := 118140960795 + 2747357 * 2 ^ 59
def prefixEnd_2747357 : Nat := 4983230072969 + 3 ^ 40 * 2747357 * 2
def baseEnd_2747357 : Nat := 940476446996341791201761

theorem tailTrace_2747357 : CollatzResearch.WordTrace tailWord_2747357 prefixEnd_2747357 940476446996341791201761 := by
  unfold tailWord_2747357
  simp only [CollatzResearch.WordTrace]
  refine ⟨100204341907802275064896325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66802894605201516709930883 100204341907802275064896325)
  ·
    refine ⟨18788314107712926574668061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100204341907802275064896325 18788314107712926574668061)
    ·
      refine ⟨7045617790392347465500523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18788314107712926574668061 7045617790392347465500523)
      ·
        refine ⟨10568426685588521198250785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7045617790392347465500523 10568426685588521198250785)
        ·
          refine ⟨7926320014191390898688089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10568426685588521198250785 7926320014191390898688089)
          ·
            refine ⟨5944740010643543174016067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7926320014191390898688089 5944740010643543174016067)
            ·
              refine ⟨8917110015965314761024101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5944740010643543174016067 8917110015965314761024101)
              ·
                refine ⟨1671958127993496517692019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8917110015965314761024101 1671958127993496517692019)
                ·
                  refine ⟨2507937191990244776538029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671958127993496517692019 2507937191990244776538029)
                  ·
                    refine ⟨940476446996341791201761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2507937191990244776538029 940476446996341791201761)
                    ·
                      rfl

theorem cell22_2747357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_2747357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747357 prefixEnd_2747357 := by exact prefixLift 2747357
  have htrace : WordTrace (prefixWord ++ tailWord_2747357) baseStart_2747357 baseEnd_2747357 := by
    simpa [prefixWord, tailWord_2747357, baseEnd_2747357] using wordTrace_append hprefix tailTrace_2747357
  have hstable : (prefixWord ++ tailWord_2747357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747357).length < 2 ^ (prefixWord ++ tailWord_2747357).sum := by decide
  have hdescent : baseEnd_2747357 < baseStart_2747357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747400 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 1, 4]
def baseStart_2747400 : Nat := 118140960795 + 2747400 * 2 ^ 59
def prefixEnd_2747400 : Nat := 4983230072969 + 3 ^ 40 * 2747400 * 2
def baseEnd_2747400 : Nat := 940491166775104012376629

theorem tailTrace_2747400 : CollatzResearch.WordTrace tailWord_2747400 prefixEnd_2747400 940491166775104012376629 := by
  unfold tailWord_2747400
  simp only [CollatzResearch.WordTrace]
  refine ⟨50102955123323246704355827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66803940164430995605807769 50102955123323246704355827)
  ·
    refine ⟨75154432684984870056533741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50102955123323246704355827 75154432684984870056533741)
    ·
      refine ⟨28182912256869326271200153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75154432684984870056533741 28182912256869326271200153)
      ·
        refine ⟨21137184192651994703400115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28182912256869326271200153 21137184192651994703400115)
        ·
          refine ⟨31705776288977992055100173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21137184192651994703400115 31705776288977992055100173)
          ·
            refine ⟨11889666108366747020662565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31705776288977992055100173 11889666108366747020662565)
            ·
              refine ⟨2229312395318765066374231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11889666108366747020662565 2229312395318765066374231)
              ·
                refine ⟨3343968592978147599561347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229312395318765066374231 3343968592978147599561347)
                ·
                  refine ⟨5015952889467221399342021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3343968592978147599561347 5015952889467221399342021)
                  ·
                    refine ⟨940491166775104012376629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5015952889467221399342021 940491166775104012376629)
                    ·
                      rfl

theorem cell22_2747400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_2747400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747400 prefixEnd_2747400 := by exact prefixLift 2747400
  have htrace : WordTrace (prefixWord ++ tailWord_2747400) baseStart_2747400 baseEnd_2747400 := by
    simpa [prefixWord, tailWord_2747400, baseEnd_2747400] using wordTrace_append hprefix tailTrace_2747400
  have hstable : (prefixWord ++ tailWord_2747400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747400).length < 2 ^ (prefixWord ++ tailWord_2747400).sum := by decide
  have hdescent : baseEnd_2747400 < baseStart_2747400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747411 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 4, 4]
def baseStart_2747411 : Nat := 118140960795 + 2747411 * 2 ^ 59
def prefixEnd_2747411 : Nat := 4983230072969 + 3 ^ 40 * 2747411 * 2
def baseEnd_2747411 : Nat := 940494932299903650351595

theorem tailTrace_2747411 : CollatzResearch.WordTrace tailWord_2747411 prefixEnd_2747411 940494932299903650351595 := by
  unfold tailWord_2747411
  simp only [CollatzResearch.WordTrace]
  refine ⟨100206311449606642287362087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66804207633071094858241391 100206311449606642287362087)
  ·
    refine ⟨150309467174409963431043131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100206311449606642287362087 150309467174409963431043131)
    ·
      refine ⟨225464200761614945146564697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150309467174409963431043131 225464200761614945146564697)
      ·
        refine ⟨169098150571211208859923523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225464200761614945146564697 169098150571211208859923523)
        ·
          refine ⟨253647225856816813289885285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169098150571211208859923523 253647225856816813289885285)
          ·
            refine ⟨47558854848153152491853491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253647225856816813289885285 47558854848153152491853491)
            ·
              refine ⟨71338282272229728737780237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47558854848153152491853491 71338282272229728737780237)
              ·
                refine ⟨26751855852086148276667589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71338282272229728737780237 26751855852086148276667589)
                ·
                  refine ⟨5015972972266152801875173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26751855852086148276667589 5015972972266152801875173)
                  ·
                    refine ⟨940494932299903650351595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5015972972266152801875173 940494932299903650351595)
                    ·
                      rfl

theorem cell22_2747411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 4].length) (baseStart_2747411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747411 prefixEnd_2747411 := by exact prefixLift 2747411
  have htrace : WordTrace (prefixWord ++ tailWord_2747411) baseStart_2747411 baseEnd_2747411 := by
    simpa [prefixWord, tailWord_2747411, baseEnd_2747411] using wordTrace_append hprefix tailTrace_2747411
  have hstable : (prefixWord ++ tailWord_2747411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747411).length < 2 ^ (prefixWord ++ tailWord_2747411).sum := by decide
  have hdescent : baseEnd_2747411 < baseStart_2747411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747415 : List Nat := [1, 1, 3, 5, 1, 1, 2, 4, 4]
def baseStart_2747415 : Nat := 118140960795 + 2747415 * 2 ^ 59
def prefixEnd_2747415 : Nat := 4983230072969 + 3 ^ 40 * 2747415 * 2
def baseEnd_2747415 : Nat := 313498767193882991083861

theorem tailTrace_2747415 : CollatzResearch.WordTrace tailWord_2747415 prefixEnd_2747415 313498767193882991083861 := by
  unfold tailWord_2747415
  simp only [CollatzResearch.WordTrace]
  refine ⟨100206457341592150970507699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66804304894394767313671799 100206457341592150970507699)
  ·
    refine ⟨150309686012388226455761549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100206457341592150970507699 150309686012388226455761549)
    ·
      refine ⟨56366132254645584920910581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150309686012388226455761549 56366132254645584920910581)
      ·
        refine ⟨5284324898873023586335367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56366132254645584920910581 5284324898873023586335367)
        ·
          refine ⟨7926487348309535379503051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5284324898873023586335367 7926487348309535379503051)
          ·
            refine ⟨11889731022464303069254577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7926487348309535379503051 11889731022464303069254577)
            ·
              refine ⟨8917298266848227301940933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11889731022464303069254577 8917298266848227301940933)
              ·
                refine ⟨1671993425034042619113925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8917298266848227301940933 1671993425034042619113925)
                ·
                  refine ⟨313498767193882991083861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671993425034042619113925 313498767193882991083861)
                  ·
                    rfl

theorem cell22_2747415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 4].length) (baseStart_2747415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747415 prefixEnd_2747415 := by exact prefixLift 2747415
  have htrace : WordTrace (prefixWord ++ tailWord_2747415) baseStart_2747415 baseEnd_2747415 := by
    simpa [prefixWord, tailWord_2747415, baseEnd_2747415] using wordTrace_append hprefix tailTrace_2747415
  have hstable : (prefixWord ++ tailWord_2747415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747415).length < 2 ^ (prefixWord ++ tailWord_2747415).sum := by decide
  have hdescent : baseEnd_2747415 < baseStart_2747415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747428 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_2747428 : Nat := 118140960795 + 2747428 * 2 ^ 59
def prefixEnd_2747428 : Nat := 4983230072969 + 3 ^ 40 * 2747428 * 2
def baseEnd_2747428 : Nat := 940500751747321272676543

theorem tailTrace_2747428 : CollatzResearch.WordTrace tailWord_2747428 prefixEnd_2747428 940500751747321272676543 := by
  unfold tailWord_2747428
  simp only [CollatzResearch.WordTrace]
  refine ⟨50103465745272527095365469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66804620993696702793820625 50103465745272527095365469)
  ·
    refine ⟨18788799654477197660762051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50103465745272527095365469 18788799654477197660762051)
    ·
      refine ⟨28183199481715796491143077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18788799654477197660762051 28183199481715796491143077)
      ·
        refine ⟨5284349902821711842089327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28183199481715796491143077 5284349902821711842089327)
        ·
          refine ⟨7926524854232567763133991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5284349902821711842089327 7926524854232567763133991)
          ·
            refine ⟨11889787281348851644700987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7926524854232567763133991 11889787281348851644700987)
            ·
              refine ⟨17834680922023277467051481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11889787281348851644700987 17834680922023277467051481)
              ·
                refine ⟨13376010691517458100288611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17834680922023277467051481 13376010691517458100288611)
                ·
                  refine ⟨20064016037276187150432917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13376010691517458100288611 20064016037276187150432917)
                  ·
                    refine ⟨940500751747321272676543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20064016037276187150432917 940500751747321272676543)
                    ·
                      rfl

theorem cell22_2747428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_2747428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747428 prefixEnd_2747428 := by exact prefixLift 2747428
  have htrace : WordTrace (prefixWord ++ tailWord_2747428) baseStart_2747428 baseEnd_2747428 := by
    simpa [prefixWord, tailWord_2747428, baseEnd_2747428] using wordTrace_append hprefix tailTrace_2747428
  have hstable : (prefixWord ++ tailWord_2747428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747428).length < 2 ^ (prefixWord ++ tailWord_2747428).sum := by decide
  have hdescent : baseEnd_2747428 < baseStart_2747428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747441 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_2747441 : Nat := 118140960795 + 2747441 * 2 ^ 59
def prefixEnd_2747441 : Nat := 4983230072969 + 3 ^ 40 * 2747441 * 2
def baseEnd_2747441 : Nat := 940505201912993572101503

theorem tailTrace_2747441 : CollatzResearch.WordTrace tailWord_2747441 prefixEnd_2747441 940505201912993572101503 := by
  unfold tailWord_2747441
  simp only [CollatzResearch.WordTrace]
  refine ⟨100207405639497957410954177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66804937092998638273969451 100207405639497957410954177)
  ·
    refine ⟨75155554229623468058215633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100207405639497957410954177 75155554229623468058215633)
    ·
      refine ⟨56366665672217601043661725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75155554229623468058215633 56366665672217601043661725)
      ·
        refine ⟨21137499627081600391373147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56366665672217601043661725 21137499627081600391373147)
        ·
          refine ⟨31706249440622400587059721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21137499627081600391373147 31706249440622400587059721)
          ·
            refine ⟨23779687080466800440294791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31706249440622400587059721 23779687080466800440294791)
            ·
              refine ⟨35669530620700200660442187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23779687080466800440294791 35669530620700200660442187)
              ·
                refine ⟨53504295931050300990663281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35669530620700200660442187 53504295931050300990663281)
                ·
                  refine ⟨40128221948287725742997461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53504295931050300990663281 40128221948287725742997461)
                  ·
                    refine ⟨940505201912993572101503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40128221948287725742997461 940505201912993572101503)
                    ·
                      rfl

theorem cell22_2747441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_2747441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747441 prefixEnd_2747441 := by exact prefixLift 2747441
  have htrace : WordTrace (prefixWord ++ tailWord_2747441) baseStart_2747441 baseEnd_2747441 := by
    simpa [prefixWord, tailWord_2747441, baseEnd_2747441] using wordTrace_append hprefix tailTrace_2747441
  have hstable : (prefixWord ++ tailWord_2747441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747441).length < 2 ^ (prefixWord ++ tailWord_2747441).sum := by decide
  have hdescent : baseEnd_2747441 < baseStart_2747441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747462 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2747462 : Nat := 118140960795 + 2747462 * 2 ^ 59
def prefixEnd_2747462 : Nat := 4983230072969 + 3 ^ 40 * 2747462 * 2
def baseEnd_2747462 : Nat := 940512390642156517326439

theorem tailTrace_2747462 : CollatzResearch.WordTrace tailWord_2747462 prefixEnd_2747462 940512390642156517326439 := by
  unfold tailWord_2747462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131505361638183687420895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66805447714947918664979093 3131505361638183687420895)
  ·
    refine ⟨4697258042457275531131343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3131505361638183687420895 4697258042457275531131343)
    ·
      refine ⟨7045887063685913296697015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4697258042457275531131343 7045887063685913296697015)
      ·
        refine ⟨10568830595528869945045523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7045887063685913296697015 10568830595528869945045523)
        ·
          refine ⟨15853245893293304917568285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10568830595528869945045523 15853245893293304917568285)
          ·
            refine ⟨5944967209984989344088107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15853245893293304917568285 5944967209984989344088107)
            ·
              refine ⟨8917450814977484016132161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5944967209984989344088107 8917450814977484016132161)
              ·
                refine ⟨6688088111233113012099121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8917450814977484016132161 6688088111233113012099121)
                ·
                  refine ⟨5016066083424834759074341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6688088111233113012099121 5016066083424834759074341)
                  ·
                    refine ⟨940512390642156517326439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5016066083424834759074341 940512390642156517326439)
                    ·
                      rfl

theorem cell22_2747462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2747462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747462 prefixEnd_2747462 := by exact prefixLift 2747462
  have htrace : WordTrace (prefixWord ++ tailWord_2747462) baseStart_2747462 baseEnd_2747462 := by
    simpa [prefixWord, tailWord_2747462, baseEnd_2747462] using wordTrace_append hprefix tailTrace_2747462
  have hstable : (prefixWord ++ tailWord_2747462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747462).length < 2 ^ (prefixWord ++ tailWord_2747462).sum := by decide
  have hdescent : baseEnd_2747462 < baseStart_2747462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747488 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 5]
def baseStart_2747488 : Nat := 118140960795 + 2747488 * 2 ^ 59
def prefixEnd_2747488 : Nat := 4983230072969 + 3 ^ 40 * 2747488 * 2
def baseEnd_2747488 : Nat := 313507096991167038725453

theorem tailTrace_2747488 : CollatzResearch.WordTrace tailWord_2747488 prefixEnd_2747488 313507096991167038725453 := by
  unfold tailWord_2747488
  simp only [CollatzResearch.WordTrace]
  refine ⟨50104559935163842218957559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66806079913551789625276745 50104559935163842218957559)
  ·
    refine ⟨75156839902745763328436339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50104559935163842218957559 75156839902745763328436339)
    ·
      refine ⟨112735259854118644992654509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75156839902745763328436339 112735259854118644992654509)
      ·
        refine ⟨42275722445294491872245441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112735259854118644992654509 42275722445294491872245441)
        ·
          refine ⟨31706791833970868904184081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42275722445294491872245441 31706791833970868904184081)
          ·
            refine ⟨23780093875478151678138061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31706791833970868904184081 23780093875478151678138061)
            ·
              refine ⟨8917535203304306879301773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23780093875478151678138061 8917535203304306879301773)
              ·
                refine ⟨3344075701239115079738165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8917535203304306879301773 3344075701239115079738165)
                ·
                  refine ⟨313507096991167038725453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3344075701239115079738165 313507096991167038725453)
                  ·
                    rfl

theorem cell22_2747488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_2747488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747488 prefixEnd_2747488 := by exact prefixLift 2747488
  have htrace : WordTrace (prefixWord ++ tailWord_2747488) baseStart_2747488 baseEnd_2747488 := by
    simpa [prefixWord, tailWord_2747488, baseEnd_2747488] using wordTrace_append hprefix tailTrace_2747488
  have hstable : (prefixWord ++ tailWord_2747488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747488).length < 2 ^ (prefixWord ++ tailWord_2747488).sum := by decide
  have hdescent : baseEnd_2747488 < baseStart_2747488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2747550 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_2747550 : Nat := 118140960795 + 2747550 * 2 ^ 59
def prefixEnd_2747550 : Nat := 4983230072969 + 3 ^ 40 * 2747550 * 2
def baseEnd_2747550 : Nat := 313514171613517873708723

theorem tailTrace_2747550 : CollatzResearch.WordTrace tailWord_2747550 prefixEnd_2747550 313514171613517873708723 := by
  unfold tailWord_2747550
  simp only [CollatzResearch.WordTrace]
  refine ⟨12526422649512883628334013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66807587464068712684448069 12526422649512883628334013)
  ·
    refine ⟨4697408493567331360625255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12526422649512883628334013 4697408493567331360625255)
    ·
      refine ⟨7046112740350997040937883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4697408493567331360625255 7046112740350997040937883)
      ·
        refine ⟨10569169110526495561406825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7046112740350997040937883 10569169110526495561406825)
        ·
          refine ⟨7926876832894871671055119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10569169110526495561406825 7926876832894871671055119)
          ·
            refine ⟨11890315249342307506582679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7926876832894871671055119 11890315249342307506582679)
            ·
              refine ⟨17835472874013461259874019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11890315249342307506582679 17835472874013461259874019)
              ·
                refine ⟨26753209311020191889811029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17835472874013461259874019 26753209311020191889811029)
                ·
                  refine ⟨313514171613517873708723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26753209311020191889811029 313514171613517873708723)
                  ·
                    rfl

theorem cell22_2747550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_2747550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2747550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2747550 prefixEnd_2747550 := by exact prefixLift 2747550
  have htrace : WordTrace (prefixWord ++ tailWord_2747550) baseStart_2747550 baseEnd_2747550 := by
    simpa [prefixWord, tailWord_2747550, baseEnd_2747550] using wordTrace_append hprefix tailTrace_2747550
  have hstable : (prefixWord ++ tailWord_2747550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2747550).length < 2 ^ (prefixWord ++ tailWord_2747550).sum := by decide
  have hdescent : baseEnd_2747550 < baseStart_2747550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2747550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
