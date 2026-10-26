import V185TrunkScan23Chunk0253

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1502492 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_1502492 : Nat := 118140960795 + 1502492 * 2 ^ 59
def prefixEnd_1502492 : Nat := 4983230072969 + 3 ^ 40 * 1502492 * 2
def baseEnd_1502492 : Nat := 771500575535240726840171

theorem tailTrace_1502492 : CollatzResearch.WordTrace tailWord_1502492 prefixEnd_1502492 771500575535240726840171 := by
  unfold tailWord_1502492
  simp only [CollatzResearch.WordTrace]
  refine ⟨27400192636367782024662865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36533590181823709366217153 27400192636367782024662865)
  ·
    refine ⟨20550144477275836518497149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27400192636367782024662865 20550144477275836518497149)
    ·
      refine ⟨7706304178978438694436431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20550144477275836518497149 7706304178978438694436431)
      ·
        refine ⟨11559456268467658041654647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7706304178978438694436431 11559456268467658041654647)
        ·
          refine ⟨17339184402701487062481971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11559456268467658041654647 17339184402701487062481971)
          ·
            refine ⟨26008776604052230593722957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17339184402701487062481971 26008776604052230593722957)
            ·
              refine ⟨9753291226519586472646109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26008776604052230593722957 9753291226519586472646109)
              ·
                refine ⟨3657484209944844927242291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9753291226519586472646109 3657484209944844927242291)
                ·
                  refine ⟨5486226314917267390863437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3657484209944844927242291 5486226314917267390863437)
                  ·
                    refine ⟨2057334868093975271573789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5486226314917267390863437 2057334868093975271573789)
                    ·
                      refine ⟨771500575535240726840171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2057334868093975271573789 771500575535240726840171)
                      ·
                        rfl

theorem cell23_1502492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_1502492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502492 prefixEnd_1502492 := by exact prefixLift 1502492
  have htrace : WordTrace (prefixWord ++ tailWord_1502492) baseStart_1502492 baseEnd_1502492 := by
    simpa [prefixWord, tailWord_1502492, baseEnd_1502492] using wordTrace_append hprefix tailTrace_1502492
  have hstable : (prefixWord ++ tailWord_1502492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502492).length < 2 ^ (prefixWord ++ tailWord_1502492).sum := by decide
  have hdescent : baseEnd_1502492 < baseStart_1502492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502550 : List Nat := [5, 2, 3, 1, 1, 2, 2, 7]
def baseStart_1502550 : Nat := 118140960795 + 1502550 * 2 ^ 59
def prefixEnd_1502550 : Nat := 4983230072969 + 3 ^ 40 * 1502550 * 2
def baseEnd_1502550 : Nat := 28575198422711166663515

theorem tailTrace_1502550 : CollatzResearch.WordTrace tailWord_1502550 prefixEnd_1502550 28575198422711166663515 := by
  unfold tailWord_1502550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3425156294157839997183569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36535000471016959969958069 3425156294157839997183569)
  ·
    refine ⟨2568867220618379997887677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3425156294157839997183569 2568867220618379997887677)
    ·
      refine ⟨963325207731892499207879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2568867220618379997887677 963325207731892499207879)
      ·
        refine ⟨1444987811597838748811819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963325207731892499207879 1444987811597838748811819)
        ·
          refine ⟨2167481717396758123217729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444987811597838748811819 2167481717396758123217729)
          ·
            refine ⟨1625611288047568592413297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2167481717396758123217729 1625611288047568592413297)
            ·
              refine ⟨1219208466035676444309973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1625611288047568592413297 1219208466035676444309973)
              ·
                refine ⟨28575198422711166663515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1219208466035676444309973 28575198422711166663515)
                ·
                  rfl

theorem cell23_1502550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_1502550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502550 prefixEnd_1502550 := by exact prefixLift 1502550
  have htrace : WordTrace (prefixWord ++ tailWord_1502550) baseStart_1502550 baseEnd_1502550 := by
    simpa [prefixWord, tailWord_1502550, baseEnd_1502550] using wordTrace_append hprefix tailTrace_1502550
  have hstable : (prefixWord ++ tailWord_1502550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502550).length < 2 ^ (prefixWord ++ tailWord_1502550).sum := by decide
  have hdescent : baseEnd_1502550 < baseStart_1502550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502600 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 2, 2, 2]
def baseStart_1502600 : Nat := 118140960795 + 1502600 * 2 ^ 59
def prefixEnd_1502600 : Nat := 4983230072969 + 3 ^ 40 * 1502600 * 2
def baseEnd_1502600 : Nat := 771556031445926304289675

theorem tailTrace_1502600 : CollatzResearch.WordTrace tailWord_1502600 prefixEnd_1502600 771556031445926304289675 := by
  unfold tailWord_1502600
  simp only [CollatzResearch.WordTrace]
  refine ⟨27402162178172149247128627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36536216237562865662838169 27402162178172149247128627)
  ·
    refine ⟨41103243267258223870692941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27402162178172149247128627 41103243267258223870692941)
    ·
      refine ⟨15413716225221833951509853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41103243267258223870692941 15413716225221833951509853)
      ·
        refine ⟨5780143584458187731816195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15413716225221833951509853 5780143584458187731816195)
        ·
          refine ⟨8670215376687281597724293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5780143584458187731816195 8670215376687281597724293)
          ·
            refine ⟨1625665383128865299573305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8670215376687281597724293 1625665383128865299573305)
            ·
              refine ⟨1219249037346648974679979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1625665383128865299573305 1219249037346648974679979)
              ·
                refine ⟨1828873556019973462019969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1219249037346648974679979 1828873556019973462019969)
                ·
                  refine ⟨1371655167014980096514977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1828873556019973462019969 1371655167014980096514977)
                  ·
                    refine ⟨1028741375261235072386233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1371655167014980096514977 1028741375261235072386233)
                    ·
                      refine ⟨771556031445926304289675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1028741375261235072386233 771556031445926304289675)
                      ·
                        rfl

theorem cell23_1502600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_1502600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502600 prefixEnd_1502600 := by exact prefixLift 1502600
  have htrace : WordTrace (prefixWord ++ tailWord_1502600) baseStart_1502600 baseEnd_1502600 := by
    simpa [prefixWord, tailWord_1502600, baseEnd_1502600] using wordTrace_append hprefix tailTrace_1502600
  have hstable : (prefixWord ++ tailWord_1502600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502600).length < 2 ^ (prefixWord ++ tailWord_1502600).sum := by decide
  have hdescent : baseEnd_1502600 < baseStart_1502600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502672 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 3]
def baseStart_1502672 : Nat := 118140960795 + 1502672 * 2 ^ 59
def prefixEnd_1502672 : Nat := 4983230072969 + 3 ^ 40 * 1502672 * 2
def baseEnd_1502672 : Nat := 771593002053050022589343

theorem tailTrace_1502672 : CollatzResearch.WordTrace tailWord_1502672 prefixEnd_1502672 771593002053050022589343 := by
  unfold tailWord_1502672
  simp only [CollatzResearch.WordTrace]
  refine ⟨27403475206041727395439135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36537966941388969860585513 27403475206041727395439135)
  ·
    refine ⟨41105212809062591093158703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27403475206041727395439135 41105212809062591093158703)
    ·
      refine ⟨61657819213593886639738055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41105212809062591093158703 61657819213593886639738055)
      ·
        refine ⟨92486728820390829959607083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61657819213593886639738055 92486728820390829959607083)
        ·
          refine ⟨138730093230586244939410625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92486728820390829959607083 138730093230586244939410625)
          ·
            refine ⟨104047569922939683704557969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138730093230586244939410625 104047569922939683704557969)
            ·
              refine ⟨78035677442204762778418477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104047569922939683704557969 78035677442204762778418477)
              ·
                refine ⟨29263379040826786041906929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78035677442204762778418477 29263379040826786041906929)
                ·
                  refine ⟨21947534280620089531430197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29263379040826786041906929 21947534280620089531430197)
                  ·
                    refine ⟨2057581338808133393571581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21947534280620089531430197 2057581338808133393571581)
                    ·
                      refine ⟨771593002053050022589343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2057581338808133393571581 771593002053050022589343)
                      ·
                        rfl

theorem cell23_1502672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 3].length) (baseStart_1502672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502672 prefixEnd_1502672 := by exact prefixLift 1502672
  have htrace : WordTrace (prefixWord ++ tailWord_1502672) baseStart_1502672 baseEnd_1502672 := by
    simpa [prefixWord, tailWord_1502672, baseEnd_1502672] using wordTrace_append hprefix tailTrace_1502672
  have hstable : (prefixWord ++ tailWord_1502672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502672).length < 2 ^ (prefixWord ++ tailWord_1502672).sum := by decide
  have hdescent : baseEnd_1502672 < baseStart_1502672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502676 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1502676 : Nat := 118140960795 + 1502676 * 2 ^ 59
def prefixEnd_1502676 : Nat := 4983230072969 + 3 ^ 40 * 1502676 * 2
def baseEnd_1502676 : Nat := 771595055975668006939325

theorem tailTrace_1502676 : CollatzResearch.WordTrace tailWord_1502676 prefixEnd_1502676 771595055975668006939325 := by
  unfold tailWord_1502676
  simp only [CollatzResearch.WordTrace]
  refine ⟨27403548152034481737011941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36538064202712642316015921 27403548152034481737011941)
  ·
    refine ⟨5138165278506465325689739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27403548152034481737011941 5138165278506465325689739)
    ·
      refine ⟨7707247917759697988534609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5138165278506465325689739 7707247917759697988534609)
      ·
        refine ⟨5780435938319773491400957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7707247917759697988534609 5780435938319773491400957)
        ·
          refine ⟨2167663476869915059275359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5780435938319773491400957 2167663476869915059275359)
          ·
            refine ⟨3251495215304872588913039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167663476869915059275359 3251495215304872588913039)
            ·
              refine ⟨4877242822957308883369559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3251495215304872588913039 4877242822957308883369559)
              ·
                refine ⟨7315864234435963325054339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877242822957308883369559 7315864234435963325054339)
                ·
                  refine ⟨10973796351653944987581509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7315864234435963325054339 10973796351653944987581509)
                  ·
                    refine ⟨2057586815935114685171533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10973796351653944987581509 2057586815935114685171533)
                    ·
                      refine ⟨771595055975668006939325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2057586815935114685171533 771595055975668006939325)
                      ·
                        rfl

theorem cell23_1502676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1502676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502676 prefixEnd_1502676 := by exact prefixLift 1502676
  have htrace : WordTrace (prefixWord ++ tailWord_1502676) baseStart_1502676 baseEnd_1502676 := by
    simpa [prefixWord, tailWord_1502676, baseEnd_1502676] using wordTrace_append hprefix tailTrace_1502676
  have hstable : (prefixWord ++ tailWord_1502676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502676).length < 2 ^ (prefixWord ++ tailWord_1502676).sum := by decide
  have hdescent : baseEnd_1502676 < baseStart_1502676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502729 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 2, 6, 2]
def baseStart_1502729 : Nat := 118140960795 + 1502729 * 2 ^ 59
def prefixEnd_1502729 : Nat := 4983230072969 + 3 ^ 40 * 1502729 * 2
def baseEnd_1502729 : Nat := 771622270450356299576581

theorem tailTrace_1502729 : CollatzResearch.WordTrace tailWord_1502729 prefixEnd_1502729 771622270450356299576581 := by
  unfold tailWord_1502729
  simp only [CollatzResearch.WordTrace]
  refine ⟨54809029372876953525703241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36539352915251302350468827 54809029372876953525703241)
  ·
    refine ⟨41106772029657715144277431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54809029372876953525703241 41106772029657715144277431)
    ·
      refine ⟨61660158044486572716416147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41106772029657715144277431 61660158044486572716416147)
      ·
        refine ⟨92490237066729859074624221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61660158044486572716416147 92490237066729859074624221)
        ·
          refine ⟨34683838900023697152984083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92490237066729859074624221 34683838900023697152984083)
          ·
            refine ⟨52025758350035545729476125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34683838900023697152984083 52025758350035545729476125)
            ·
              refine ⟨19509659381263329648553547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52025758350035545729476125 19509659381263329648553547)
              ·
                refine ⟨29264489071894994472830321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19509659381263329648553547 29264489071894994472830321)
                ·
                  refine ⟨21948366803921245854622741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29264489071894994472830321 21948366803921245854622741)
                  ·
                    refine ⟨1028829693933808399435441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21948366803921245854622741 1028829693933808399435441)
                    ·
                      refine ⟨771622270450356299576581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1028829693933808399435441 771622270450356299576581)
                      ·
                        rfl

theorem cell23_1502729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 6, 2].length) (baseStart_1502729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502729 prefixEnd_1502729 := by exact prefixLift 1502729
  have htrace : WordTrace (prefixWord ++ tailWord_1502729) baseStart_1502729 baseEnd_1502729 := by
    simpa [prefixWord, tailWord_1502729, baseEnd_1502729] using wordTrace_append hprefix tailTrace_1502729
  have hstable : (prefixWord ++ tailWord_1502729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502729).length < 2 ^ (prefixWord ++ tailWord_1502729).sum := by decide
  have hdescent : baseEnd_1502729 < baseStart_1502729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502739 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 4, 4]
def baseStart_1502739 : Nat := 118140960795 + 1502739 * 2 ^ 59
def prefixEnd_1502739 : Nat := 4983230072969 + 3 ^ 40 * 1502739 * 2
def baseEnd_1502739 : Nat := 257209135085633753483845

theorem tailTrace_1502739 : CollatzResearch.WordTrace tailWord_1502739 prefixEnd_1502739 257209135085633753483845 := by
  unfold tailWord_1502739
  simp only [CollatzResearch.WordTrace]
  refine ⟨54809394102840725233567271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36539596068560483489044847 54809394102840725233567271)
  ·
    refine ⟨82214091154261087850350907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54809394102840725233567271 82214091154261087850350907)
    ·
      refine ⟨123321136731391631775526361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82214091154261087850350907 123321136731391631775526361)
      ·
        refine ⟨92490852548543723831644771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123321136731391631775526361 92490852548543723831644771)
        ·
          refine ⟨138736278822815585747467157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92490852548543723831644771 138736278822815585747467157)
          ·
            refine ⟨6503263069819480581912523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 138736278822815585747467157 6503263069819480581912523)
            ·
              refine ⟨9754894604729220872868785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6503263069819480581912523 9754894604729220872868785)
              ·
                refine ⟨7316170953546915654651589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9754894604729220872868785 7316170953546915654651589)
                ·
                  refine ⟨1371782053790046685247173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7316170953546915654651589 1371782053790046685247173)
                  ·
                    refine ⟨257209135085633753483845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1371782053790046685247173 257209135085633753483845)
                    ·
                      rfl

theorem cell23_1502739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 4].length) (baseStart_1502739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502739 prefixEnd_1502739 := by exact prefixLift 1502739
  have htrace : WordTrace (prefixWord ++ tailWord_1502739) baseStart_1502739 baseEnd_1502739 := by
    simpa [prefixWord, tailWord_1502739, baseEnd_1502739] using wordTrace_append hprefix tailTrace_1502739
  have hstable : (prefixWord ++ tailWord_1502739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502739).length < 2 ^ (prefixWord ++ tailWord_1502739).sum := by decide
  have hdescent : baseEnd_1502739 < baseStart_1502739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502766 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1502766 : Nat := 118140960795 + 1502766 * 2 ^ 59
def prefixEnd_1502766 : Nat := 4983230072969 + 3 ^ 40 * 1502766 * 2
def baseEnd_1502766 : Nat := 771641269234572654813911

theorem tailTrace_1502766 : CollatzResearch.WordTrace tailWord_1502766 prefixEnd_1502766 771641269234572654813911 := by
  unfold tailWord_1502766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6851297359217863605600019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36540252582495272563200101 6851297359217863605600019)
  ·
    refine ⟨10276946038826795408400029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6851297359217863605600019 10276946038826795408400029)
    ·
      refine ⟨3853854764560048278150011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10276946038826795408400029 3853854764560048278150011)
      ·
        refine ⟨5780782146840072417225017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3853854764560048278150011 5780782146840072417225017)
        ·
          refine ⟨4335586610130054312918763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5780782146840072417225017 4335586610130054312918763)
          ·
            refine ⟨6503379915195081469378145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335586610130054312918763 6503379915195081469378145)
            ·
              refine ⟨4877534936396311102033609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6503379915195081469378145 4877534936396311102033609)
              ·
                refine ⟨3658151202297233326525207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4877534936396311102033609 3658151202297233326525207)
                ·
                  refine ⟨5487226803445849989787811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658151202297233326525207 5487226803445849989787811)
                  ·
                    refine ⟨8230840205168774984681717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5487226803445849989787811 8230840205168774984681717)
                    ·
                      refine ⟨771641269234572654813911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8230840205168774984681717 771641269234572654813911)
                      ·
                        rfl

theorem cell23_1502766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1502766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502766 prefixEnd_1502766 := by exact prefixLift 1502766
  have htrace : WordTrace (prefixWord ++ tailWord_1502766) baseStart_1502766 baseEnd_1502766 := by
    simpa [prefixWord, tailWord_1502766, baseEnd_1502766] using wordTrace_append hprefix tailTrace_1502766
  have hstable : (prefixWord ++ tailWord_1502766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502766).length < 2 ^ (prefixWord ++ tailWord_1502766).sum := by decide
  have hdescent : baseEnd_1502766 < baseStart_1502766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502773 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1502773 : Nat := 118140960795 + 1502773 * 2 ^ 59
def prefixEnd_1502773 : Nat := 4983230072969 + 3 ^ 40 * 1502773 * 2
def baseEnd_1502773 : Nat := 257214954533051375808793

theorem tailTrace_1502773 : CollatzResearch.WordTrace tailWord_1502773 prefixEnd_1502773 257214954533051375808793 := by
  unfold tailWord_1502773
  simp only [CollatzResearch.WordTrace]
  refine ⟨54810634184717549040304973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36540422789811699360203315 54810634184717549040304973)
  ·
    refine ⟨20553987819269080890114365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54810634184717549040304973 20553987819269080890114365)
    ·
      refine ⟨7707745432225905333792887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20553987819269080890114365 7707745432225905333792887)
      ·
        refine ⟨11561618148338858000689331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7707745432225905333792887 11561618148338858000689331)
        ·
          refine ⟨17342427222508287001033997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11561618148338858000689331 17342427222508287001033997)
          ·
            refine ⟨6503410208440607625387749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17342427222508287001033997 6503410208440607625387749)
            ·
              refine ⟨1219389414082613929760203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6503410208440607625387749 1219389414082613929760203)
              ·
                refine ⟨1829084121123920894640305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1219389414082613929760203 1829084121123920894640305)
                ·
                  refine ⟨1371813090842940670980229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1829084121123920894640305 1371813090842940670980229)
                  ·
                    refine ⟨257214954533051375808793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1371813090842940670980229 257214954533051375808793)
                    ·
                      rfl

theorem cell23_1502773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1502773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502773 prefixEnd_1502773 := by exact prefixLift 1502773
  have htrace : WordTrace (prefixWord ++ tailWord_1502773) baseStart_1502773 baseEnd_1502773 := by
    simpa [prefixWord, tailWord_1502773, baseEnd_1502773] using wordTrace_append hprefix tailTrace_1502773
  have hstable : (prefixWord ++ tailWord_1502773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502773).length < 2 ^ (prefixWord ++ tailWord_1502773).sum := by decide
  have hdescent : baseEnd_1502773 < baseStart_1502773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502780 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 1, 1, 4]
def baseStart_1502780 : Nat := 118140960795 + 1502780 * 2 ^ 59
def prefixEnd_1502780 : Nat := 4983230072969 + 3 ^ 40 * 1502780 * 2
def baseEnd_1502780 : Nat := 771648457963735600038847

theorem tailTrace_1502780 : CollatzResearch.WordTrace tailWord_1502780 prefixEnd_1502780 771648457963735600038847 := by
  unfold tailWord_1502780
  simp only [CollatzResearch.WordTrace]
  refine ⟨27405444747846094617904897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36540592997128126157206529 27405444747846094617904897)
  ·
    refine ⟨20554083560884570963428673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27405444747846094617904897 20554083560884570963428673)
    ·
      refine ⟨15415562670663428222571505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20554083560884570963428673 15415562670663428222571505)
      ·
        refine ⟨11561672002997571166928629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15415562670663428222571505 11561672002997571166928629)
        ·
          refine ⟨1083906750281022296899559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11561672002997571166928629 1083906750281022296899559)
          ·
            refine ⟨1625860125421533445349339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083906750281022296899559 1625860125421533445349339)
            ·
              refine ⟨2438790188132300168024009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625860125421533445349339 2438790188132300168024009)
              ·
                refine ⟨1829092641099225126018007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2438790188132300168024009 1829092641099225126018007)
                ·
                  refine ⟨2743638961648837689027011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829092641099225126018007 2743638961648837689027011)
                  ·
                    refine ⟨4115458442473256533540517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2743638961648837689027011 4115458442473256533540517)
                    ·
                      refine ⟨771648457963735600038847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4115458442473256533540517 771648457963735600038847)
                      ·
                        rfl

theorem cell23_1502780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_1502780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502780 prefixEnd_1502780 := by exact prefixLift 1502780
  have htrace : WordTrace (prefixWord ++ tailWord_1502780) baseStart_1502780 baseEnd_1502780 := by
    simpa [prefixWord, tailWord_1502780, baseEnd_1502780] using wordTrace_append hprefix tailTrace_1502780
  have hstable : (prefixWord ++ tailWord_1502780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502780).length < 2 ^ (prefixWord ++ tailWord_1502780).sum := by decide
  have hdescent : baseEnd_1502780 < baseStart_1502780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502783 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 1, 2, 3]
def baseStart_1502783 : Nat := 118140960795 + 1502783 * 2 ^ 59
def prefixEnd_1502783 : Nat := 4983230072969 + 3 ^ 40 * 1502783 * 2
def baseEnd_1502783 : Nat := 771649998405699088301333

theorem tailTrace_1502783 : CollatzResearch.WordTrace tailWord_1502783 prefixEnd_1502783 771649998405699088301333 := by
  unfold tailWord_1502783
  simp only [CollatzResearch.WordTrace]
  refine ⟨54810998914681320748169003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36540665943120880498779335 54810998914681320748169003)
  ·
    refine ⟨82216498372021981122253505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54810998914681320748169003 82216498372021981122253505)
    ·
      refine ⟨61662373779016485841690129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82216498372021981122253505 61662373779016485841690129)
      ·
        refine ⟨46246780334262364381267597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61662373779016485841690129 46246780334262364381267597)
        ·
          refine ⟨17342542625348386642975349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46246780334262364381267597 17342542625348386642975349)
          ·
            refine ⟨1625863371126411247778939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17342542625348386642975349 1625863371126411247778939)
            ·
              refine ⟨2438795056689616871668409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625863371126411247778939 2438795056689616871668409)
              ·
                refine ⟨1829096292517212653751307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2438795056689616871668409 1829096292517212653751307)
                ·
                  refine ⟨2743644438775818980626961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829096292517212653751307 2743644438775818980626961)
                  ·
                    refine ⟨2057733329081864235470221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2743644438775818980626961 2057733329081864235470221)
                    ·
                      refine ⟨771649998405699088301333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2057733329081864235470221 771649998405699088301333)
                      ·
                        rfl

theorem cell23_1502783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_1502783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502783 prefixEnd_1502783 := by exact prefixLift 1502783
  have htrace : WordTrace (prefixWord ++ tailWord_1502783) baseStart_1502783 baseEnd_1502783 := by
    simpa [prefixWord, tailWord_1502783, baseEnd_1502783] using wordTrace_append hprefix tailTrace_1502783
  have hstable : (prefixWord ++ tailWord_1502783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502783).length < 2 ^ (prefixWord ++ tailWord_1502783).sum := by decide
  have hdescent : baseEnd_1502783 < baseStart_1502783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502796 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 1, 3, 3]
def baseStart_1502796 : Nat := 118140960795 + 1502796 * 2 ^ 59
def prefixEnd_1502796 : Nat := 4983230072969 + 3 ^ 40 * 1502796 * 2
def baseEnd_1502796 : Nat := 771656673654207537438773

theorem tailTrace_1502796 : CollatzResearch.WordTrace tailWord_1502796 prefixEnd_1502796 771656673654207537438773 := by
  unfold tailWord_1502796
  simp only [CollatzResearch.WordTrace]
  refine ⟨27405736531817111984196121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36540982042422815978928161 27405736531817111984196121)
  ·
    refine ⟨20554302398862833988147091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27405736531817111984196121 20554302398862833988147091)
    ·
      refine ⟨30831453598294250982220637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20554302398862833988147091 30831453598294250982220637)
      ·
        refine ⟨11561795099360344118332739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30831453598294250982220637 11561795099360344118332739)
        ·
          refine ⟨17342692649040516177499109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11561795099360344118332739 17342692649040516177499109)
          ·
            refine ⟨3251754871695096783281083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17342692649040516177499109 3251754871695096783281083)
            ·
              refine ⟨4877632307542645174921625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3251754871695096783281083 4877632307542645174921625)
              ·
                refine ⟨3658224230656983881191219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4877632307542645174921625 3658224230656983881191219)
                ·
                  refine ⟨5487336345985475821786829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658224230656983881191219 5487336345985475821786829)
                  ·
                    refine ⟨2057751129744553433170061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5487336345985475821786829 2057751129744553433170061)
                    ·
                      refine ⟨771656673654207537438773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2057751129744553433170061 771656673654207537438773)
                      ·
                        rfl

theorem cell23_1502796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_1502796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502796 prefixEnd_1502796 := by exact prefixLift 1502796
  have htrace : WordTrace (prefixWord ++ tailWord_1502796) baseStart_1502796 baseEnd_1502796 := by
    simpa [prefixWord, tailWord_1502796, baseEnd_1502796] using wordTrace_append hprefix tailTrace_1502796
  have hstable : (prefixWord ++ tailWord_1502796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502796).length < 2 ^ (prefixWord ++ tailWord_1502796).sum := by decide
  have hdescent : baseEnd_1502796 < baseStart_1502796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502819 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1502819 : Nat := 118140960795 + 1502819 * 2 ^ 59
def prefixEnd_1502819 : Nat := 4983230072969 + 3 ^ 40 * 1502819 * 2
def baseEnd_1502819 : Nat := 771668483709260947451167

theorem tailTrace_1502819 : CollatzResearch.WordTrace tailWord_1502819 prefixEnd_1502819 771668483709260947451167 := by
  unfold tailWord_1502819
  simp only [CollatzResearch.WordTrace]
  refine ⟨54812311942550898896479511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36541541295033932597653007 54812311942550898896479511)
  ·
    refine ⟨82218467913826348344719267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54812311942550898896479511 82218467913826348344719267)
    ·
      refine ⟨123327701870739522517078901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82218467913826348344719267 123327701870739522517078901)
      ·
        refine ⟨11561972050381830235976147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123327701870739522517078901 11561972050381830235976147)
        ·
          refine ⟨17342958075572745353964221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11561972050381830235976147 17342958075572745353964221)
          ·
            refine ⟨6503609278339779507736583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17342958075572745353964221 6503609278339779507736583)
            ·
              refine ⟨9755413917509669261604875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6503609278339779507736583 9755413917509669261604875)
              ·
                refine ⟨14633120876264503892407313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9755413917509669261604875 14633120876264503892407313)
                ·
                  refine ⟨10974840657198377919305485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14633120876264503892407313 10974840657198377919305485)
                  ·
                    refine ⟨4115565246449391719739557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10974840657198377919305485 4115565246449391719739557)
                    ·
                      refine ⟨771668483709260947451167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4115565246449391719739557 771668483709260947451167)
                      ·
                        rfl

theorem cell23_1502819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1502819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502819 prefixEnd_1502819 := by exact prefixLift 1502819
  have htrace : WordTrace (prefixWord ++ tailWord_1502819) baseStart_1502819 baseEnd_1502819 := by
    simpa [prefixWord, tailWord_1502819, baseEnd_1502819] using wordTrace_append hprefix tailTrace_1502819
  have hstable : (prefixWord ++ tailWord_1502819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502819).length < 2 ^ (prefixWord ++ tailWord_1502819).sum := by decide
  have hdescent : baseEnd_1502819 < baseStart_1502819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502839 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 3]
def baseStart_1502839 : Nat := 118140960795 + 1502839 * 2 ^ 59
def prefixEnd_1502839 : Nat := 4983230072969 + 3 ^ 40 * 1502839 * 2
def baseEnd_1502839 : Nat := 771678753322350869201075

theorem tailTrace_1502839 : CollatzResearch.WordTrace tailWord_1502839 prefixEnd_1502839 771678753322350869201075 := by
  unfold tailWord_1502839
  simp only [CollatzResearch.WordTrace]
  refine ⟨54813041402478442312207571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36542027601652294874805047 54813041402478442312207571)
  ·
    refine ⟨82219562103717663468311357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54813041402478442312207571 82219562103717663468311357)
    ·
      refine ⟨30832335788894123800616759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82219562103717663468311357 30832335788894123800616759)
      ·
        refine ⟨46248503683341185700925139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30832335788894123800616759 46248503683341185700925139)
        ·
          refine ⟨69372755525011778551387709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46248503683341185700925139 69372755525011778551387709)
          ·
            refine ⟨26014783321879416956770391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69372755525011778551387709 26014783321879416956770391)
            ·
              refine ⟨39022174982819125435155587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26014783321879416956770391 39022174982819125435155587)
              ·
                refine ⟨58533262474228688152733381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39022174982819125435155587 58533262474228688152733381)
                ·
                  refine ⟨10974986713917879028637509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58533262474228688152733381 10974986713917879028637509)
                  ·
                    refine ⟨2057810008859602317869533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10974986713917879028637509 2057810008859602317869533)
                    ·
                      refine ⟨771678753322350869201075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2057810008859602317869533 771678753322350869201075)
                      ·
                        rfl

theorem cell23_1502839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_1502839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502839 prefixEnd_1502839 := by exact prefixLift 1502839
  have htrace : WordTrace (prefixWord ++ tailWord_1502839) baseStart_1502839 baseEnd_1502839 := by
    simpa [prefixWord, tailWord_1502839, baseEnd_1502839] using wordTrace_append hprefix tailTrace_1502839
  have hstable : (prefixWord ++ tailWord_1502839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502839).length < 2 ^ (prefixWord ++ tailWord_1502839).sum := by decide
  have hdescent : baseEnd_1502839 < baseStart_1502839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502853 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 4, 2, 2]
def baseStart_1502853 : Nat := 118140960795 + 1502853 * 2 ^ 59
def prefixEnd_1502853 : Nat := 4983230072969 + 3 ^ 40 * 1502853 * 2
def baseEnd_1502853 : Nat := 771685942051513814426011

theorem tailTrace_1502853 : CollatzResearch.WordTrace tailWord_1502853 prefixEnd_1502853 771685942051513814426011 := by
  unfold tailWord_1502853
  simp only [CollatzResearch.WordTrace]
  refine ⟨54813552024427722703217213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36542368016285148468811475 54813552024427722703217213)
  ·
    refine ⟨20555082009160396013706455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54813552024427722703217213 20555082009160396013706455)
    ·
      refine ⟨30832623013740594020559683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20555082009160396013706455 30832623013740594020559683)
      ·
        refine ⟨46248934520610891030839525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30832623013740594020559683 46248934520610891030839525)
        ·
          refine ⟨8671675222614542068282411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46248934520610891030839525 8671675222614542068282411)
          ·
            refine ⟨13007512833921813102423617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671675222614542068282411 13007512833921813102423617)
            ·
              refine ⟨9755634625441359826817713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13007512833921813102423617 9755634625441359826817713)
              ·
                refine ⟨7316725969081019870113285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9755634625441359826817713 7316725969081019870113285)
                ·
                  refine ⟨1371886119202691225646241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7316725969081019870113285 1371886119202691225646241)
                  ·
                    refine ⟨1028914589402018419234681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1371886119202691225646241 1028914589402018419234681)
                    ·
                      refine ⟨771685942051513814426011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1028914589402018419234681 771685942051513814426011)
                      ·
                        rfl

theorem cell23_1502853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 2, 2].length) (baseStart_1502853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502853 prefixEnd_1502853 := by exact prefixLift 1502853
  have htrace : WordTrace (prefixWord ++ tailWord_1502853) baseStart_1502853 baseEnd_1502853 := by
    simpa [prefixWord, tailWord_1502853, baseEnd_1502853] using wordTrace_append hprefix tailTrace_1502853
  have hstable : (prefixWord ++ tailWord_1502853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502853).length < 2 ^ (prefixWord ++ tailWord_1502853).sum := by decide
  have hdescent : baseEnd_1502853 < baseStart_1502853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502896 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 2, 5, 2]
def baseStart_1502896 : Nat := 118140960795 + 1502896 * 2 ^ 59
def prefixEnd_1502896 : Nat := 4983230072969 + 3 ^ 40 * 1502896 * 2
def baseEnd_1502896 : Nat := 771708021719657146188313

theorem tailTrace_1502896 : CollatzResearch.WordTrace tailWord_1502896 prefixEnd_1502896 771708021719657146188313 := by
  unfold tailWord_1502896
  simp only [CollatzResearch.WordTrace]
  refine ⟨27407560181635970523516271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36543413575514627364688361 27407560181635970523516271)
  ·
    refine ⟨41111340272453955785274407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27407560181635970523516271 41111340272453955785274407)
    ·
      refine ⟨61667010408680933677911611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41111340272453955785274407 61667010408680933677911611)
      ·
        refine ⟨92500515613021400516867417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61667010408680933677911611 92500515613021400516867417)
        ·
          refine ⟨69375386709766050387650563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92500515613021400516867417 69375386709766050387650563)
          ·
            refine ⟨104063080064649075581475845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69375386709766050387650563 104063080064649075581475845)
            ·
              refine ⟨19511827512121701671526721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104063080064649075581475845 19511827512121701671526721)
              ·
                refine ⟨14633870634091276253645041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19511827512121701671526721 14633870634091276253645041)
                ·
                  refine ⟨10975402975568457190233781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14633870634091276253645041 10975402975568457190233781)
                  ·
                    refine ⟨1028944028959542861584417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10975402975568457190233781 1028944028959542861584417)
                    ·
                      refine ⟨771708021719657146188313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1028944028959542861584417 771708021719657146188313)
                      ·
                        rfl

theorem cell23_1502896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 5, 2].length) (baseStart_1502896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502896 prefixEnd_1502896 := by exact prefixLift 1502896
  have htrace : WordTrace (prefixWord ++ tailWord_1502896) baseStart_1502896 baseEnd_1502896 := by
    simpa [prefixWord, tailWord_1502896, baseEnd_1502896] using wordTrace_append hprefix tailTrace_1502896
  have hstable : (prefixWord ++ tailWord_1502896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502896).length < 2 ^ (prefixWord ++ tailWord_1502896).sum := by decide
  have hdescent : baseEnd_1502896 < baseStart_1502896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502910 : List Nat := [4, 2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_1502910 : Nat := 118140960795 + 1502910 * 2 ^ 59
def prefixEnd_1502910 : Nat := 4983230072969 + 3 ^ 40 * 1502910 * 2
def baseEnd_1502910 : Nat := 85746134494313343490361

theorem tailTrace_1502910 : CollatzResearch.WordTrace tailWord_1502910 prefixEnd_1502910 85746134494313343490361 := by
  unfold tailWord_1502910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6851953873152652679755273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36543753990147480958694789 6851953873152652679755273)
  ·
    refine ⟨5138965404864489509816455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6851953873152652679755273 5138965404864489509816455)
    ·
      refine ⟨7708448107296734264724683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5138965404864489509816455 7708448107296734264724683)
      ·
        refine ⟨11562672160945101397087025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7708448107296734264724683 11562672160945101397087025)
        ·
          refine ⟨8672004120708826047815269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11562672160945101397087025 8672004120708826047815269)
          ·
            refine ⟨1626000772632904883965363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8672004120708826047815269 1626000772632904883965363)
            ·
              refine ⟨2439001158949357325948045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626000772632904883965363 2439001158949357325948045)
              ·
                refine ⟨914625434606008997230517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2439001158949357325948045 914625434606008997230517)
                ·
                  refine ⟨85746134494313343490361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 914625434606008997230517 85746134494313343490361)
                  ·
                    rfl

theorem cell23_1502910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_1502910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502910 prefixEnd_1502910 := by exact prefixLift 1502910
  have htrace : WordTrace (prefixWord ++ tailWord_1502910) baseStart_1502910 baseEnd_1502910 := by
    simpa [prefixWord, tailWord_1502910, baseEnd_1502910] using wordTrace_append hprefix tailTrace_1502910
  have hstable : (prefixWord ++ tailWord_1502910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502910).length < 2 ^ (prefixWord ++ tailWord_1502910).sum := by decide
  have hdescent : baseEnd_1502910 < baseStart_1502910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502916 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1502916 : Nat := 118140960795 + 1502916 * 2 ^ 59
def prefixEnd_1502916 : Nat := 4983230072969 + 3 ^ 40 * 1502916 * 2
def baseEnd_1502916 : Nat := 771718291332747067938221

theorem tailTrace_1502916 : CollatzResearch.WordTrace tailWord_1502916 prefixEnd_1502916 771718291332747067938221 := by
  unfold tailWord_1502916
  simp only [CollatzResearch.WordTrace]
  refine ⟨27407924911599742231380301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36543899882132989641840401 27407924911599742231380301)
  ·
    refine ⟨10277971841849903336767613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27407924911599742231380301 10277971841849903336767613)
    ·
      refine ⟨3854239440693713751287855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10277971841849903336767613 3854239440693713751287855)
      ·
        refine ⟨5781359161040570626931783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3854239440693713751287855 5781359161040570626931783)
        ·
          refine ⟨8672038741560855940397675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5781359161040570626931783 8672038741560855940397675)
          ·
            refine ⟨13008058112341283910596513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8672038741560855940397675 13008058112341283910596513)
            ·
              refine ⟨9756043584255962932947385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13008058112341283910596513 9756043584255962932947385)
              ·
                refine ⟨7317032688191972199710539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9756043584255962932947385 7317032688191972199710539)
                ·
                  refine ⟨10975549032287958299565809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7317032688191972199710539 10975549032287958299565809)
                  ·
                    refine ⟨8231661774215968724674357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10975549032287958299565809 8231661774215968724674357)
                    ·
                      refine ⟨771718291332747067938221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8231661774215968724674357 771718291332747067938221)
                      ·
                        rfl

theorem cell23_1502916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1502916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502916 prefixEnd_1502916 := by exact prefixLift 1502916
  have htrace : WordTrace (prefixWord ++ tailWord_1502916) baseStart_1502916 baseEnd_1502916 := by
    simpa [prefixWord, tailWord_1502916, baseEnd_1502916] using wordTrace_append hprefix tailTrace_1502916
  have hstable : (prefixWord ++ tailWord_1502916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502916).length < 2 ^ (prefixWord ++ tailWord_1502916).sum := by decide
  have hdescent : baseEnd_1502916 < baseStart_1502916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502969 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_1502969 : Nat := 118140960795 + 1502969 * 2 ^ 59
def prefixEnd_1502969 : Nat := 4983230072969 + 3 ^ 40 * 1502969 * 2
def baseEnd_1502969 : Nat := 771745505807435360575477

theorem tailTrace_1502969 : CollatzResearch.WordTrace tailWord_1502969 prefixEnd_1502969 771745505807435360575477 := by
  unfold tailWord_1502969
  simp only [CollatzResearch.WordTrace]
  refine ⟨54817782892007474514439961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36545188594671649676293307 54817782892007474514439961)
  ·
    refine ⟨41113337169005605885829971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54817782892007474514439961 41113337169005605885829971)
    ·
      refine ⟨61670005753508408828744957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41113337169005605885829971 61670005753508408828744957)
      ·
        refine ⟨23126252157565653310779359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61670005753508408828744957 23126252157565653310779359)
        ·
          refine ⟨34689378236348479966169039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23126252157565653310779359 34689378236348479966169039)
          ·
            refine ⟨52034067354522719949253559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34689378236348479966169039 52034067354522719949253559)
            ·
              refine ⟨78051101031784079923880339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52034067354522719949253559 78051101031784079923880339)
              ·
                refine ⟨117076651547676119885820509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78051101031784079923880339 117076651547676119885820509)
                ·
                  refine ⟨43903744330378544957182691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117076651547676119885820509 43903744330378544957182691)
                  ·
                    refine ⟨65855616495567817435774037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43903744330378544957182691 65855616495567817435774037)
                    ·
                      refine ⟨771745505807435360575477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 65855616495567817435774037 771745505807435360575477)
                      ·
                        rfl

theorem cell23_1502969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_1502969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502969 prefixEnd_1502969 := by exact prefixLift 1502969
  have htrace : WordTrace (prefixWord ++ tailWord_1502969) baseStart_1502969 baseEnd_1502969 := by
    simpa [prefixWord, tailWord_1502969, baseEnd_1502969] using wordTrace_append hprefix tailTrace_1502969
  have hstable : (prefixWord ++ tailWord_1502969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502969).length < 2 ^ (prefixWord ++ tailWord_1502969).sum := by decide
  have hdescent : baseEnd_1502969 < baseStart_1502969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502993 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 3, 1, 3]
def baseStart_1502993 : Nat := 118140960795 + 1502993 * 2 ^ 59
def prefixEnd_1502993 : Nat := 4983230072969 + 3 ^ 40 * 1502993 * 2
def baseEnd_1502993 : Nat := 771757829343143266675367

theorem tailTrace_1502993 : CollatzResearch.WordTrace tailWord_1502993 prefixEnd_1502993 771757829343143266675367 := by
  unfold tailWord_1502993
  simp only [CollatzResearch.WordTrace]
  refine ⟨54818658243920526613313633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36545772162613684408875755 54818658243920526613313633)
  ·
    refine ⟨41113993682940394959985225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54818658243920526613313633 41113993682940394959985225)
    ·
      refine ⟨30835495262205296219988919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41113993682940394959985225 30835495262205296219988919)
      ·
        refine ⟨46253242893307944329983379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30835495262205296219988919 46253242893307944329983379)
        ·
          refine ⟨69379864339961916494975069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46253242893307944329983379 69379864339961916494975069)
          ·
            refine ⟨26017449127485718685615651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69379864339961916494975069 26017449127485718685615651)
            ·
              refine ⟨39026173691228578028423477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26017449127485718685615651 39026173691228578028423477)
              ·
                refine ⟨3658703783552679190164701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39026173691228578028423477 3658703783552679190164701)
                ·
                  refine ⟨1372013918832254696311763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3658703783552679190164701 1372013918832254696311763)
                  ·
                    refine ⟨2058020878248382044467645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1372013918832254696311763 2058020878248382044467645)
                    ·
                      refine ⟨771757829343143266675367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2058020878248382044467645 771757829343143266675367)
                      ·
                        rfl

theorem cell23_1502993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_1502993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502993 prefixEnd_1502993 := by exact prefixLift 1502993
  have htrace : WordTrace (prefixWord ++ tailWord_1502993) baseStart_1502993 baseEnd_1502993 := by
    simpa [prefixWord, tailWord_1502993, baseEnd_1502993] using wordTrace_append hprefix tailTrace_1502993
  have hstable : (prefixWord ++ tailWord_1502993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502993).length < 2 ^ (prefixWord ++ tailWord_1502993).sum := by decide
  have hdescent : baseEnd_1502993 < baseStart_1502993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503010 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_1503010 : Nat := 118140960795 + 1503010 * 2 ^ 59
def prefixEnd_1503010 : Nat := 4983230072969 + 3 ^ 40 * 1503010 * 2
def baseEnd_1503010 : Nat := 771766558514269700162789

theorem tailTrace_1503010 : CollatzResearch.WordTrace tailWord_1503010 prefixEnd_1503010 771766558514269700162789 := by
  unfold tailWord_1503010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13704819571214734629170621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36546185523239292344454989 13704819571214734629170621)
  ·
    refine ⟨5139307339205525485938983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13704819571214734629170621 5139307339205525485938983)
    ·
      refine ⟨7708961008808288228908475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5139307339205525485938983 7708961008808288228908475)
      ·
        refine ⟨11563441513212432343362713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7708961008808288228908475 11563441513212432343362713)
        ·
          refine ⟨8672581134909324257522035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11563441513212432343362713 8672581134909324257522035)
          ·
            refine ⟨13008871702363986386283053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8672581134909324257522035 13008871702363986386283053)
            ·
              refine ⟨4878326888386494894856145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13008871702363986386283053 4878326888386494894856145)
              ·
                refine ⟨3658745166289871171142109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4878326888386494894856145 3658745166289871171142109)
                ·
                  refine ⟨1372029437358701689178291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3658745166289871171142109 1372029437358701689178291)
                  ·
                    refine ⟨2058044156038052533767437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1372029437358701689178291 2058044156038052533767437)
                    ·
                      refine ⟨771766558514269700162789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2058044156038052533767437 771766558514269700162789)
                      ·
                        rfl

theorem cell23_1503010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_1503010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503010 prefixEnd_1503010 := by exact prefixLift 1503010
  have htrace : WordTrace (prefixWord ++ tailWord_1503010) baseStart_1503010 baseEnd_1503010 := by
    simpa [prefixWord, tailWord_1503010, baseEnd_1503010] using wordTrace_append hprefix tailTrace_1503010
  have hstable : (prefixWord ++ tailWord_1503010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503010).length < 2 ^ (prefixWord ++ tailWord_1503010).sum := by decide
  have hdescent : baseEnd_1503010 < baseStart_1503010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503020 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 2, 3, 2]
def baseStart_1503020 : Nat := 118140960795 + 1503020 * 2 ^ 59
def prefixEnd_1503020 : Nat := 4983230072969 + 3 ^ 40 * 1503020 * 2
def baseEnd_1503020 : Nat := 771771693320814661037743

theorem tailTrace_1503020 : CollatzResearch.WordTrace tailWord_1503020 prefixEnd_1503020 771771693320814661037743 := by
  unfold tailWord_1503020
  simp only [CollatzResearch.WordTrace]
  refine ⟨27409821507411355112273257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36546428676548473483031009 27409821507411355112273257)
  ·
    refine ⟨20557366130558516334204943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27409821507411355112273257 20557366130558516334204943)
    ·
      refine ⟨30836049195837774501307415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20557366130558516334204943 30836049195837774501307415)
      ·
        refine ⟨46254073793756661751961123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30836049195837774501307415 46254073793756661751961123)
        ·
          refine ⟨69381110690634992627941685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46254073793756661751961123 69381110690634992627941685)
          ·
            refine ⟨6504479127247030558869533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69381110690634992627941685 6504479127247030558869533)
            ·
              refine ⟨2439179672717636459576075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6504479127247030558869533 2439179672717636459576075)
              ·
                refine ⟨3658769509076454689364113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439179672717636459576075 3658769509076454689364113)
                ·
                  refine ⟨2744077131807341017023085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3658769509076454689364113 2744077131807341017023085)
                  ·
                    refine ⟨1029028924427752881383657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744077131807341017023085 1029028924427752881383657)
                    ·
                      refine ⟨771771693320814661037743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029028924427752881383657 771771693320814661037743)
                      ·
                        rfl

theorem cell23_1503020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 3, 2].length) (baseStart_1503020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503020 prefixEnd_1503020 := by exact prefixLift 1503020
  have htrace : WordTrace (prefixWord ++ tailWord_1503020) baseStart_1503020 baseEnd_1503020 := by
    simpa [prefixWord, tailWord_1503020, baseEnd_1503020] using wordTrace_append hprefix tailTrace_1503020
  have hstable : (prefixWord ++ tailWord_1503020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503020).length < 2 ^ (prefixWord ++ tailWord_1503020).sum := by decide
  have hdescent : baseEnd_1503020 < baseStart_1503020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503043 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 4, 4]
def baseStart_1503043 : Nat := 118140960795 + 1503043 * 2 ^ 59
def prefixEnd_1503043 : Nat := 4983230072969 + 3 ^ 40 * 1503043 * 2
def baseEnd_1503043 : Nat := 257261167791956023683379

theorem tailTrace_1503043 : CollatzResearch.WordTrace tailWord_1503043 prefixEnd_1503043 257261167791956023683379 := by
  unfold tailWord_1503043
  simp only [CollatzResearch.WordTrace]
  refine ⟨54820481893739385152633783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36546987929159590101755855 54820481893739385152633783)
  ·
    refine ⟨82230722840609077728950675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54820481893739385152633783 82230722840609077728950675)
    ·
      refine ⟨123346084260913616593426013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82230722840609077728950675 123346084260913616593426013)
      ·
        refine ⟨46254781597842606222534755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123346084260913616593426013 46254781597842606222534755)
        ·
          refine ⟨69382172396763909333802133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46254781597842606222534755 69382172396763909333802133)
          ·
            refine ⟨3252289331098308250021975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69382172396763909333802133 3252289331098308250021975)
            ·
              refine ⟨4878433996647462375032963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252289331098308250021975 4878433996647462375032963)
              ·
                refine ⟨7317650994971193562549445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4878433996647462375032963 7317650994971193562549445)
                ·
                  refine ⟨1372059561557098792978021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7317650994971193562549445 1372059561557098792978021)
                  ·
                    refine ⟨257261167791956023683379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1372059561557098792978021 257261167791956023683379)
                    ·
                      rfl

theorem cell23_1503043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 4].length) (baseStart_1503043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503043 prefixEnd_1503043 := by exact prefixLift 1503043
  have htrace : WordTrace (prefixWord ++ tailWord_1503043) baseStart_1503043 baseEnd_1503043 := by
    simpa [prefixWord, tailWord_1503043, baseEnd_1503043] using wordTrace_append hprefix tailTrace_1503043
  have hstable : (prefixWord ++ tailWord_1503043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503043).length < 2 ^ (prefixWord ++ tailWord_1503043).sum := by decide
  have hdescent : baseEnd_1503043 < baseStart_1503043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503060 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_1503060 : Nat := 118140960795 + 1503060 * 2 ^ 59
def prefixEnd_1503060 : Nat := 4983230072969 + 3 ^ 40 * 1503060 * 2
def baseEnd_1503060 : Nat := 257264077515664834845853

theorem tailTrace_1503060 : CollatzResearch.WordTrace tailWord_1503060 prefixEnd_1503060 257264077515664834845853 := by
  unfold tailWord_1503060
  simp only [CollatzResearch.WordTrace]
  refine ⟨27410550967338898528001317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36547401289785198037335089 27410550967338898528001317)
  ·
    refine ⟨5139478306376043474000247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27410550967338898528001317 5139478306376043474000247)
    ·
      refine ⟨7709217459564065211000371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5139478306376043474000247 7709217459564065211000371)
      ·
        refine ⟨11563826189346097816500557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7709217459564065211000371 11563826189346097816500557)
        ·
          refine ⟨4336434821004786681187709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11563826189346097816500557 4336434821004786681187709)
          ·
            refine ⟨1626163057876795005445391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4336434821004786681187709 1626163057876795005445391)
            ·
              refine ⟨2439244586815192508168087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626163057876795005445391 2439244586815192508168087)
              ·
                refine ⟨3658866880222788762252131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439244586815192508168087 3658866880222788762252131)
                ·
                  refine ⟨5488300320334183143378197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658866880222788762252131 5488300320334183143378197)
                  ·
                    refine ⟨257264077515664834845853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5488300320334183143378197 257264077515664834845853)
                    ·
                      rfl

theorem cell23_1503060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_1503060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503060 prefixEnd_1503060 := by exact prefixLift 1503060
  have htrace : WordTrace (prefixWord ++ tailWord_1503060) baseStart_1503060 baseEnd_1503060 := by
    simpa [prefixWord, tailWord_1503060, baseEnd_1503060] using wordTrace_append hprefix tailTrace_1503060
  have hstable : (prefixWord ++ tailWord_1503060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503060).length < 2 ^ (prefixWord ++ tailWord_1503060).sum := by decide
  have hdescent : baseEnd_1503060 < baseStart_1503060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503063 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 6]
def baseStart_1503063 : Nat := 118140960795 + 1503063 * 2 ^ 59
def prefixEnd_1503063 : Nat := 4983230072969 + 3 ^ 40 * 1503063 * 2
def baseEnd_1503063 : Nat := 771793772988957992800045

theorem tailTrace_1503063 : CollatzResearch.WordTrace tailWord_1503063 prefixEnd_1503063 771793772988957992800045 := by
  unfold tailWord_1503063
  simp only [CollatzResearch.WordTrace]
  refine ⟨54821211353666928568361843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36547474235777952378907895 54821211353666928568361843)
  ·
    refine ⟨82231817030500392852542765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54821211353666928568361843 82231817030500392852542765)
    ·
      refine ⟨30836931386437647319703537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82231817030500392852542765 30836931386437647319703537)
      ·
        refine ⟨23127698539828235489777653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30836931386437647319703537 23127698539828235489777653)
        ·
          refine ⟨2168221738108897077166655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23127698539828235489777653 2168221738108897077166655)
          ·
            refine ⟨3252332607163345615749983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168221738108897077166655 3252332607163345615749983)
            ·
              refine ⟨4878498910745018423624975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252332607163345615749983 4878498910745018423624975)
              ·
                refine ⟨7317748366117527635437463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4878498910745018423624975 7317748366117527635437463)
                ·
                  refine ⟨10976622549176291453156195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7317748366117527635437463 10976622549176291453156195)
                  ·
                    refine ⟨16464933823764437179734293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10976622549176291453156195 16464933823764437179734293)
                    ·
                      refine ⟨771793772988957992800045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16464933823764437179734293 771793772988957992800045)
                      ·
                        rfl

theorem cell23_1503063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_1503063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503063 prefixEnd_1503063 := by exact prefixLift 1503063
  have htrace : WordTrace (prefixWord ++ tailWord_1503063) baseStart_1503063 baseEnd_1503063 := by
    simpa [prefixWord, tailWord_1503063, baseEnd_1503063] using wordTrace_append hprefix tailTrace_1503063
  have hstable : (prefixWord ++ tailWord_1503063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503063).length < 2 ^ (prefixWord ++ tailWord_1503063).sum := by decide
  have hdescent : baseEnd_1503063 < baseStart_1503063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503084 : List Nat := [2, 2, 1, 1, 4, 2, 3, 3, 1, 2, 2]
def baseStart_1503084 : Nat := 118140960795 + 1503084 * 2 ^ 59
def prefixEnd_1503084 : Nat := 4983230072969 + 3 ^ 40 * 1503084 * 2
def baseEnd_1503084 : Nat := 771804556082702410637449

theorem tailTrace_1503084 : CollatzResearch.WordTrace tailWord_1503084 prefixEnd_1503084 771804556082702410637449 := by
  unfold tailWord_1503084
  simp only [CollatzResearch.WordTrace]
  refine ⟨27410988643295424577438153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36547984857727232769917537 27410988643295424577438153)
  ·
    refine ⟨20558241482471568433078615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27410988643295424577438153 20558241482471568433078615)
    ·
      refine ⟨30837362223707352649617923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20558241482471568433078615 30837362223707352649617923)
      ·
        refine ⟨46256043335561028974426885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30837362223707352649617923 46256043335561028974426885)
        ·
          refine ⟨8673008125417692932705041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46256043335561028974426885 8673008125417692932705041)
          ·
            refine ⟨6504756094063269699528781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8673008125417692932705041 6504756094063269699528781)
            ·
              refine ⟨2439283535273726137323293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6504756094063269699528781 2439283535273726137323293)
              ·
                refine ⟨914731325727647301496235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2439283535273726137323293 914731325727647301496235)
                ·
                  refine ⟨1372096988591470952244353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914731325727647301496235 1372096988591470952244353)
                  ·
                    refine ⟨1029072741443603214183265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1372096988591470952244353 1029072741443603214183265)
                    ·
                      refine ⟨771804556082702410637449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029072741443603214183265 771804556082702410637449)
                      ·
                        rfl

theorem cell23_1503084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 1, 2, 2].length) (baseStart_1503084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503084 prefixEnd_1503084 := by exact prefixLift 1503084
  have htrace : WordTrace (prefixWord ++ tailWord_1503084) baseStart_1503084 baseEnd_1503084 := by
    simpa [prefixWord, tailWord_1503084, baseEnd_1503084] using wordTrace_append hprefix tailTrace_1503084
  have hstable : (prefixWord ++ tailWord_1503084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503084).length < 2 ^ (prefixWord ++ tailWord_1503084).sum := by decide
  have hdescent : baseEnd_1503084 < baseStart_1503084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503116 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_1503116 : Nat := 118140960795 + 1503116 * 2 ^ 59
def prefixEnd_1503116 : Nat := 4983230072969 + 3 ^ 40 * 1503116 * 2
def baseEnd_1503116 : Nat := 257273662487882095145767

theorem tailTrace_1503116 : CollatzResearch.WordTrace tailWord_1503116 prefixEnd_1503116 257273662487882095145767 := by
  unfold tailWord_1503116
  simp only [CollatzResearch.WordTrace]
  refine ⟨27411572211237459310020601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36548762948316612413360801 27411572211237459310020601)
  ·
    refine ⟨20558679158428094482515451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27411572211237459310020601 20558679158428094482515451)
    ·
      refine ⟨30838018737642141723773177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20558679158428094482515451 30838018737642141723773177)
      ·
        refine ⟨23128514053231606292829883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30838018737642141723773177 23128514053231606292829883)
        ·
          refine ⟨34692771079847409439244825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23128514053231606292829883 34692771079847409439244825)
          ·
            refine ⟨26019578309885557079433619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34692771079847409439244825 26019578309885557079433619)
            ·
              refine ⟨39029367464828335619150429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26019578309885557079433619 39029367464828335619150429)
              ·
                refine ⟨14636012799310625857181411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39029367464828335619150429 14636012799310625857181411)
                ·
                  refine ⟨21954019198965938785772117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14636012799310625857181411 21954019198965938785772117)
                  ·
                    refine ⟨257273662487882095145767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21954019198965938785772117 257273662487882095145767)
                    ·
                      rfl

theorem cell23_1503116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_1503116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503116 prefixEnd_1503116 := by exact prefixLift 1503116
  have htrace : WordTrace (prefixWord ++ tailWord_1503116) baseStart_1503116 baseEnd_1503116 := by
    simpa [prefixWord, tailWord_1503116, baseEnd_1503116] using wordTrace_append hprefix tailTrace_1503116
  have hstable : (prefixWord ++ tailWord_1503116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503116).length < 2 ^ (prefixWord ++ tailWord_1503116).sum := by decide
  have hdescent : baseEnd_1503116 < baseStart_1503116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503127 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 1, 3, 2]
def baseStart_1503127 : Nat := 118140960795 + 1503127 * 2 ^ 59
def prefixEnd_1503127 : Nat := 4983230072969 + 3 ^ 40 * 1503127 * 2
def baseEnd_1503127 : Nat := 771826635750845742399751

theorem tailTrace_1503127 : CollatzResearch.WordTrace tailWord_1503127 prefixEnd_1503127 771826635750845742399751 := by
  unfold tailWord_1503127
  simp only [CollatzResearch.WordTrace]
  refine ⟨54823545625435067498691635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36549030416956711665794423 54823545625435067498691635)
  ·
    refine ⟨82235318438152601248037453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54823545625435067498691635 82235318438152601248037453)
    ·
      refine ⟨30838244414307225468014045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82235318438152601248037453 30838244414307225468014045)
      ·
        refine ⟨11564341655365209550505267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30838244414307225468014045 11564341655365209550505267)
        ·
          refine ⟨17346512483047814325757901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11564341655365209550505267 17346512483047814325757901)
          ·
            refine ⟨6504942181142930372159213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17346512483047814325757901 6504942181142930372159213)
            ·
              refine ⟨2439353317928598889559705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6504942181142930372159213 2439353317928598889559705)
              ·
                refine ⟨1829514988446449167169779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2439353317928598889559705 1829514988446449167169779)
                ·
                  refine ⟨2744272482669673750754669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829514988446449167169779 2744272482669673750754669)
                  ·
                    refine ⟨1029102181001127656533001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744272482669673750754669 1029102181001127656533001)
                    ·
                      refine ⟨771826635750845742399751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029102181001127656533001 771826635750845742399751)
                      ·
                        rfl

theorem cell23_1503127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_1503127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503127 prefixEnd_1503127 := by exact prefixLift 1503127
  have htrace : WordTrace (prefixWord ++ tailWord_1503127) baseStart_1503127 baseEnd_1503127 := by
    simpa [prefixWord, tailWord_1503127, baseEnd_1503127] using wordTrace_append hprefix tailTrace_1503127
  have hstable : (prefixWord ++ tailWord_1503127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503127).length < 2 ^ (prefixWord ++ tailWord_1503127).sum := by decide
  have hdescent : baseEnd_1503127 < baseStart_1503127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503134 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1503134 : Nat := 118140960795 + 1503134 * 2 ^ 59
def prefixEnd_1503134 : Nat := 4983230072969 + 3 ^ 40 * 1503134 * 2
def baseEnd_1503134 : Nat := 771830230115427215012219

theorem tailTrace_1503134 : CollatzResearch.WordTrace tailWord_1503134 prefixEnd_1503134 771830230115427215012219 := by
  unfold tailWord_1503134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6852975117051213461774557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36549200624273138462797637 6852975117051213461774557)
  ·
    refine ⟨2569865668894205048165459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6852975117051213461774557 2569865668894205048165459)
    ·
      refine ⟨3854798503341307572248189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2569865668894205048165459 3854798503341307572248189)
      ·
        refine ⟨1445549438752990339593071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3854798503341307572248189 1445549438752990339593071)
        ·
          refine ⟨2168324158129485509389607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445549438752990339593071 2168324158129485509389607)
          ·
            refine ⟨3252486237194228264084411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168324158129485509389607 3252486237194228264084411)
            ·
              refine ⟨4878729355791342396126617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252486237194228264084411 4878729355791342396126617)
              ·
                refine ⟨3659047016843506797094963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4878729355791342396126617 3659047016843506797094963)
                ·
                  refine ⟨5488570525265260195642445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3659047016843506797094963 5488570525265260195642445)
                  ·
                    refine ⟨2058213946974472573365917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5488570525265260195642445 2058213946974472573365917)
                    ·
                      refine ⟨771830230115427215012219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2058213946974472573365917 771830230115427215012219)
                      ·
                        rfl

theorem cell23_1503134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1503134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503134 prefixEnd_1503134 := by exact prefixLift 1503134
  have htrace : WordTrace (prefixWord ++ tailWord_1503134) baseStart_1503134 baseEnd_1503134 := by
    simpa [prefixWord, tailWord_1503134, baseEnd_1503134] using wordTrace_append hprefix tailTrace_1503134
  have hstable : (prefixWord ++ tailWord_1503134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503134).length < 2 ^ (prefixWord ++ tailWord_1503134).sum := by decide
  have hdescent : baseEnd_1503134 < baseStart_1503134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503140 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 3, 4, 2]
def baseStart_1503140 : Nat := 118140960795 + 1503140 * 2 ^ 59
def prefixEnd_1503140 : Nat := 4983230072969 + 3 ^ 40 * 1503140 * 2
def baseEnd_1503140 : Nat := 771833310999354191537191

theorem tailTrace_1503140 : CollatzResearch.WordTrace tailWord_1503140 prefixEnd_1503140 771833310999354191537191 := by
  unfold tailWord_1503140
  simp only [CollatzResearch.WordTrace]
  refine ⟨27412009887193985359457437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36549346516258647145943249 27412009887193985359457437)
  ·
    refine ⟨10279503707697744509796539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27412009887193985359457437 10279503707697744509796539)
    ·
      refine ⟨15419255561546616764694809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10279503707697744509796539 15419255561546616764694809)
      ·
        refine ⟨11564441671159962573521107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15419255561546616764694809 11564441671159962573521107)
        ·
          refine ⟨17346662506739943860281661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11564441671159962573521107 17346662506739943860281661)
          ·
            refine ⟨6504998440027478947605623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17346662506739943860281661 6504998440027478947605623)
            ·
              refine ⟨9757497660041218421408435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6504998440027478947605623 9757497660041218421408435)
              ·
                refine ⟨14636246490061827632112653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9757497660041218421408435 14636246490061827632112653)
                ·
                  refine ⟨5488592433773185362042245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14636246490061827632112653 5488592433773185362042245)
                  ·
                    refine ⟨1029111081332472255382921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5488592433773185362042245 1029111081332472255382921)
                    ·
                      refine ⟨771833310999354191537191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029111081332472255382921 771833310999354191537191)
                      ·
                        rfl

theorem cell23_1503140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_1503140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503140 prefixEnd_1503140 := by exact prefixLift 1503140
  have htrace : WordTrace (prefixWord ++ tailWord_1503140) baseStart_1503140 baseEnd_1503140 := by
    simpa [prefixWord, tailWord_1503140, baseEnd_1503140] using wordTrace_append hprefix tailTrace_1503140
  have hstable : (prefixWord ++ tailWord_1503140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503140).length < 2 ^ (prefixWord ++ tailWord_1503140).sum := by decide
  have hdescent : baseEnd_1503140 < baseStart_1503140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503240 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 3, 4]
def baseStart_1503240 : Nat := 118140960795 + 1503240 * 2 ^ 59
def prefixEnd_1503240 : Nat := 4983230072969 + 3 ^ 40 * 1503240 * 2
def baseEnd_1503240 : Nat := 257294886354934600095577

theorem tailTrace_1503240 : CollatzResearch.WordTrace tailWord_1503240 prefixEnd_1503240 257294886354934600095577 := by
  unfold tailWord_1503240
  simp only [CollatzResearch.WordTrace]
  refine ⟨27413833537012843898777587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36551778049350458531703449 27413833537012843898777587)
  ·
    refine ⟨41120750305519265848166381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27413833537012843898777587 41120750305519265848166381)
    ·
      refine ⟨15420281364569724693062393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41120750305519265848166381 15420281364569724693062393)
      ·
        refine ⟨11565211023427293519796795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15420281364569724693062393 11565211023427293519796795)
        ·
          refine ⟨17347816535140940279695193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11565211023427293519796795 17347816535140940279695193)
          ·
            refine ⟨13010862401355705209771395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17347816535140940279695193 13010862401355705209771395)
            ·
              refine ⟨19516293602033557814657093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13010862401355705209771395 19516293602033557814657093)
              ·
                refine ⟨3659305050381292090248205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19516293602033557814657093 3659305050381292090248205)
                ·
                  refine ⟨1372239393892984533843077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3659305050381292090248205 1372239393892984533843077)
                  ·
                    refine ⟨257294886354934600095577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1372239393892984533843077 257294886354934600095577)
                    ·
                      rfl

theorem cell23_1503240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_1503240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503240 prefixEnd_1503240 := by exact prefixLift 1503240
  have htrace : WordTrace (prefixWord ++ tailWord_1503240) baseStart_1503240 baseEnd_1503240 := by
    simpa [prefixWord, tailWord_1503240, baseEnd_1503240] using wordTrace_append hprefix tailTrace_1503240
  have hstable : (prefixWord ++ tailWord_1503240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503240).length < 2 ^ (prefixWord ++ tailWord_1503240).sum := by decide
  have hdescent : baseEnd_1503240 < baseStart_1503240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503243 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 4]
def baseStart_1503243 : Nat := 118140960795 + 1503243 * 2 ^ 59
def prefixEnd_1503243 : Nat := 4983230072969 + 3 ^ 40 * 1503243 * 2
def baseEnd_1503243 : Nat := 771886199506767288549217

theorem tailTrace_1503243 : CollatzResearch.WordTrace tailWord_1503243 prefixEnd_1503243 771886199506767288549217 := by
  unfold tailWord_1503243
  simp only [CollatzResearch.WordTrace]
  refine ⟨54827776493014819309914383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36551850995343212873276255 54827776493014819309914383)
  ·
    refine ⟨82241664739522228964871575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54827776493014819309914383 82241664739522228964871575)
    ·
      refine ⟨123362497109283343447307363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82241664739522228964871575 123362497109283343447307363)
      ·
        refine ⟨185043745663925015170961045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123362497109283343447307363 185043745663925015170961045)
        ·
          refine ⟨8673925577996485086138799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185043745663925015170961045 8673925577996485086138799)
          ·
            refine ⟨13010888366994727629208199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8673925577996485086138799 13010888366994727629208199)
            ·
              refine ⟨19516332550492091443812299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13010888366994727629208199 19516332550492091443812299)
              ·
                refine ⟨29274498825738137165718449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19516332550492091443812299 29274498825738137165718449)
                ·
                  refine ⟨21955874119303602874288837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29274498825738137165718449 21955874119303602874288837)
                  ·
                    refine ⟨4116726397369425538929157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21955874119303602874288837 4116726397369425538929157)
                    ·
                      refine ⟨771886199506767288549217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4116726397369425538929157 771886199506767288549217)
                      ·
                        rfl

theorem cell23_1503243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 4].length) (baseStart_1503243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503243 prefixEnd_1503243 := by exact prefixLift 1503243
  have htrace : WordTrace (prefixWord ++ tailWord_1503243) baseStart_1503243 baseEnd_1503243 := by
    simpa [prefixWord, tailWord_1503243, baseEnd_1503243] using wordTrace_append hprefix tailTrace_1503243
  have hstable : (prefixWord ++ tailWord_1503243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503243).length < 2 ^ (prefixWord ++ tailWord_1503243).sum := by decide
  have hdescent : baseEnd_1503243 < baseStart_1503243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503274 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1503274 : Nat := 118140960795 + 1503274 * 2 ^ 59
def prefixEnd_1503274 : Nat := 4983230072969 + 3 ^ 40 * 1503274 * 2
def baseEnd_1503274 : Nat := 257300705802352222420525

theorem tailTrace_1503274 : CollatzResearch.WordTrace tailWord_1503274 prefixEnd_1503274 257300705802352222420525 := by
  unfold tailWord_1503274
  simp only [CollatzResearch.WordTrace]
  refine ⟨13707226788975627901073219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36552604770601674402861917 13707226788975627901073219)
  ·
    refine ⟨20560840183463441851609829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13707226788975627901073219 20560840183463441851609829)
    ·
      refine ⟨3855157534399395347176843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20560840183463441851609829 3855157534399395347176843)
      ·
        refine ⟨5782736301599093020765265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3855157534399395347176843 5782736301599093020765265)
        ·
          refine ⟨4337052226199319765573949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5782736301599093020765265 4337052226199319765573949)
          ·
            refine ⟨1626394584824744912090231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4337052226199319765573949 1626394584824744912090231)
            ·
              refine ⟨2439591877237117368135347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626394584824744912090231 2439591877237117368135347)
              ·
                refine ⟨3659387815855676052203021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439591877237117368135347 3659387815855676052203021)
                ·
                  refine ⟨1372270430945878519576133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3659387815855676052203021 1372270430945878519576133)
                  ·
                    refine ⟨257300705802352222420525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1372270430945878519576133 257300705802352222420525)
                    ·
                      rfl

theorem cell23_1503274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1503274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503274 prefixEnd_1503274 := by exact prefixLift 1503274
  have htrace : WordTrace (prefixWord ++ tailWord_1503274) baseStart_1503274 baseEnd_1503274 := by
    simpa [prefixWord, tailWord_1503274, baseEnd_1503274] using wordTrace_append hprefix tailTrace_1503274
  have hstable : (prefixWord ++ tailWord_1503274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503274).length < 2 ^ (prefixWord ++ tailWord_1503274).sum := by decide
  have hdescent : baseEnd_1503274 < baseStart_1503274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503324 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_1503324 : Nat := 118140960795 + 1503324 * 2 ^ 59
def prefixEnd_1503324 : Nat := 4983230072969 + 3 ^ 40 * 1503324 * 2
def baseEnd_1503324 : Nat := 771927791439781471636345

theorem tailTrace_1503324 : CollatzResearch.WordTrace tailWord_1503324 prefixEnd_1503324 771927791439781471636345 := by
  unfold tailWord_1503324
  simp only [CollatzResearch.WordTrace]
  refine ⟨27415365402860685071806513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36553820537147580095742017 27415365402860685071806513)
  ·
    refine ⟨20561524052145513803854885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27415365402860685071806513 20561524052145513803854885)
    ·
      refine ⟨3855285759777283838222791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20561524052145513803854885 3855285759777283838222791)
      ·
        refine ⟨5782928639665925757334187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3855285759777283838222791 5782928639665925757334187)
        ·
          refine ⟨8674392959498888636001281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5782928639665925757334187 8674392959498888636001281)
          ·
            refine ⟨6505794719624166477000961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8674392959498888636001281 6505794719624166477000961)
            ·
              refine ⟨4879346039718124857750721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6505794719624166477000961 4879346039718124857750721)
              ·
                refine ⟨3659509529788593643313041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4879346039718124857750721 3659509529788593643313041)
                ·
                  refine ⟨2744632147341445232484781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3659509529788593643313041 2744632147341445232484781)
                  ·
                    refine ⟨1029237055253041962181793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744632147341445232484781 1029237055253041962181793)
                    ·
                      refine ⟨771927791439781471636345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029237055253041962181793 771927791439781471636345)
                      ·
                        rfl

theorem cell23_1503324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_1503324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503324 prefixEnd_1503324 := by exact prefixLift 1503324
  have htrace : WordTrace (prefixWord ++ tailWord_1503324) baseStart_1503324 baseEnd_1503324 := by
    simpa [prefixWord, tailWord_1503324, baseEnd_1503324] using wordTrace_append hprefix tailTrace_1503324
  have hstable : (prefixWord ++ tailWord_1503324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503324).length < 2 ^ (prefixWord ++ tailWord_1503324).sum := by decide
  have hdescent : baseEnd_1503324 < baseStart_1503324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503331 : List Nat := [1, 1, 1, 5, 1, 1, 6, 2, 1, 1, 3]
def baseStart_1503331 : Nat := 118140960795 + 1503331 * 2 ^ 59
def prefixEnd_1503331 : Nat := 4983230072969 + 3 ^ 40 * 1503331 * 2
def baseEnd_1503331 : Nat := 771931385804362944248813

theorem tailTrace_1503331 : CollatzResearch.WordTrace tailWord_1503331 prefixEnd_1503331 771931385804362944248813 := by
  unfold tailWord_1503331
  simp only [CollatzResearch.WordTrace]
  refine ⟨54830986116696010339117847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36553990744464006892745231 54830986116696010339117847)
  ·
    refine ⟨82246479175044015508676771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54830986116696010339117847 82246479175044015508676771)
    ·
      refine ⟨123369718762566023263015157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82246479175044015508676771 123369718762566023263015157)
      ·
        refine ⟨11565911133990564680907671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123369718762566023263015157 11565911133990564680907671)
        ·
          refine ⟨17348866700985847021361507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11565911133990564680907671 17348866700985847021361507)
          ·
            refine ⟨26023300051478770532042261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17348866700985847021361507 26023300051478770532042261)
            ·
              refine ⟨1219842189913067368689481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26023300051478770532042261 1219842189913067368689481)
              ·
                refine ⟨914881642434800526517111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1219842189913067368689481 914881642434800526517111)
                ·
                  refine ⟨1372322463652200789775667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914881642434800526517111 1372322463652200789775667)
                  ·
                    refine ⟨2058483695478301184663501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1372322463652200789775667 2058483695478301184663501)
                    ·
                      refine ⟨771931385804362944248813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2058483695478301184663501 771931385804362944248813)
                      ·
                        rfl

theorem cell23_1503331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_1503331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503331 prefixEnd_1503331 := by exact prefixLift 1503331
  have htrace : WordTrace (prefixWord ++ tailWord_1503331) baseStart_1503331 baseEnd_1503331 := by
    simpa [prefixWord, tailWord_1503331, baseEnd_1503331] using wordTrace_append hprefix tailTrace_1503331
  have hstable : (prefixWord ++ tailWord_1503331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503331).length < 2 ^ (prefixWord ++ tailWord_1503331).sum := by decide
  have hdescent : baseEnd_1503331 < baseStart_1503331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503357 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_1503357 : Nat := 118140960795 + 1503357 * 2 ^ 59
def prefixEnd_1503357 : Nat := 4983230072969 + 3 ^ 40 * 1503357 * 2
def baseEnd_1503357 : Nat := 771944736301379842523693

theorem tailTrace_1503357 : CollatzResearch.WordTrace tailWord_1503357 prefixEnd_1503357 771944736301379842523693 := by
  unfold tailWord_1503357
  simp only [CollatzResearch.WordTrace]
  refine ⟨54831934414601816779564325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36554622943067877853042883 54831934414601816779564325)
  ·
    refine ⟨10280987702737840646168311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54831934414601816779564325 10280987702737840646168311)
    ·
      refine ⟨15421481554106760969252467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10280987702737840646168311 15421481554106760969252467)
      ·
        refine ⟨23132222331160141453878701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15421481554106760969252467 23132222331160141453878701)
        ·
          refine ⟨8674583374185053045204513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23132222331160141453878701 8674583374185053045204513)
          ·
            refine ⟨6505937530638789783903385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8674583374185053045204513 6505937530638789783903385)
            ·
              refine ⟨4879453147979092337927539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6505937530638789783903385 4879453147979092337927539)
              ·
                refine ⟨7319179721968638506891309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4879453147979092337927539 7319179721968638506891309)
                ·
                  refine ⟨2744692395738239440084241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7319179721968638506891309 2744692395738239440084241)
                  ·
                    refine ⟨2058519296803679580063181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2744692395738239440084241 2058519296803679580063181)
                    ·
                      refine ⟨771944736301379842523693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2058519296803679580063181 771944736301379842523693)
                      ·
                        rfl

theorem cell23_1503357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_1503357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503357 prefixEnd_1503357 := by exact prefixLift 1503357
  have htrace : WordTrace (prefixWord ++ tailWord_1503357) baseStart_1503357 baseEnd_1503357 := by
    simpa [prefixWord, tailWord_1503357, baseEnd_1503357] using wordTrace_append hprefix tailTrace_1503357
  have hstable : (prefixWord ++ tailWord_1503357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503357).length < 2 ^ (prefixWord ++ tailWord_1503357).sum := by decide
  have hdescent : baseEnd_1503357 < baseStart_1503357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503382 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1503382 : Nat := 118140960795 + 1503382 * 2 ^ 59
def prefixEnd_1503382 : Nat := 4983230072969 + 3 ^ 40 * 1503382 * 2
def baseEnd_1503382 : Nat := 771957573317742244711079

theorem tailTrace_1503382 : CollatzResearch.WordTrace tailWord_1503382 prefixEnd_1503382 771957573317742244711079 := by
  unfold tailWord_1503382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3427052889969452878076525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36555230826340830699482933 3427052889969452878076525)
  ·
    refine ⟨1285144833738544829278697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3427052889969452878076525 1285144833738544829278697)
    ·
      refine ⟨963858625303908621959023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1285144833738544829278697 963858625303908621959023)
      ·
        refine ⟨1445787937955862932938535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963858625303908621959023 1445787937955862932938535)
        ·
          refine ⟨2168681906933794399407803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445787937955862932938535 2168681906933794399407803)
          ·
            refine ⟨3253022860400691599111705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168681906933794399407803 3253022860400691599111705)
            ·
              refine ⟨2439767145300518699333779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3253022860400691599111705 2439767145300518699333779)
              ·
                refine ⟨3659650717950778049000669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439767145300518699333779 3659650717950778049000669)
                ·
                  refine ⟨1372369019231541768375251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3659650717950778049000669 1372369019231541768375251)
                  ·
                    refine ⟨2058553528847312652562877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1372369019231541768375251 2058553528847312652562877)
                    ·
                      refine ⟨771957573317742244711079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2058553528847312652562877 771957573317742244711079)
                      ·
                        rfl

theorem cell23_1503382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1503382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503382 prefixEnd_1503382 := by exact prefixLift 1503382
  have htrace : WordTrace (prefixWord ++ tailWord_1503382) baseStart_1503382 baseEnd_1503382 := by
    simpa [prefixWord, tailWord_1503382, baseEnd_1503382] using wordTrace_append hprefix tailTrace_1503382
  have hstable : (prefixWord ++ tailWord_1503382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503382).length < 2 ^ (prefixWord ++ tailWord_1503382).sum := by decide
  have hdescent : baseEnd_1503382 < baseStart_1503382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503422 : List Nat := [4, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_1503422 : Nat := 118140960795 + 1503422 * 2 ^ 59
def prefixEnd_1503422 : Nat := 4983230072969 + 3 ^ 40 * 1503422 * 2
def baseEnd_1503422 : Nat := 771978112543922088210895

theorem tailTrace_1503422 : CollatzResearch.WordTrace tailWord_1503422 prefixEnd_1503422 771978112543922088210895 := by
  unfold tailWord_1503422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6854288144920791610085065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36556203439577555253787013 6854288144920791610085065)
  ·
    refine ⟨5140716108690593707563799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6854288144920791610085065 5140716108690593707563799)
    ·
      refine ⟨7711074163035890561345699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5140716108690593707563799 7711074163035890561345699)
      ·
        refine ⟨11566611244553835842018549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7711074163035890561345699 11566611244553835842018549)
        ·
          refine ⟨1084369804176922110189239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11566611244553835842018549 1084369804176922110189239)
          ·
            refine ⟨1626554706265383165283859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084369804176922110189239 1626554706265383165283859)
            ·
              refine ⟨2439832059398074747925789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626554706265383165283859 2439832059398074747925789)
              ·
                refine ⟨914937022274278030472171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2439832059398074747925789 914937022274278030472171)
                ·
                  refine ⟨1372405533411417045708257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914937022274278030472171 1372405533411417045708257)
                  ·
                    refine ⟨1029304150058562784281193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1372405533411417045708257 1029304150058562784281193)
                    ·
                      refine ⟨771978112543922088210895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029304150058562784281193 771978112543922088210895)
                      ·
                        rfl

theorem cell23_1503422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_1503422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503422 prefixEnd_1503422 := by exact prefixLift 1503422
  have htrace : WordTrace (prefixWord ++ tailWord_1503422) baseStart_1503422 baseEnd_1503422 := by
    simpa [prefixWord, tailWord_1503422, baseEnd_1503422] using wordTrace_append hprefix tailTrace_1503422
  have hstable : (prefixWord ++ tailWord_1503422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503422).length < 2 ^ (prefixWord ++ tailWord_1503422).sum := by decide
  have hdescent : baseEnd_1503422 < baseStart_1503422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503480 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 1, 7]
def baseStart_1503480 : Nat := 118140960795 + 1503480 * 2 ^ 59
def prefixEnd_1503480 : Nat := 4983230072969 + 3 ^ 40 * 1503480 * 2
def baseEnd_1503480 : Nat := 257335964807294287095209

theorem tailTrace_1503480 : CollatzResearch.WordTrace tailWord_1503480 prefixEnd_1503480 257335964807294287095209 := by
  unfold tailWord_1503480
  simp only [CollatzResearch.WordTrace]
  refine ⟨27418210296578104393145947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36557613728770805857527929 27418210296578104393145947)
  ·
    refine ⟨41127315444867156589718921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27418210296578104393145947 41127315444867156589718921)
    ·
      refine ⟨30845486583650367442289191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41127315444867156589718921 30845486583650367442289191)
      ·
        refine ⟨46268229875475551163433787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30845486583650367442289191 46268229875475551163433787)
        ·
          refine ⟨69402344813213326745150681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46268229875475551163433787 69402344813213326745150681)
          ·
            refine ⟨52051758609909995058863011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69402344813213326745150681 52051758609909995058863011)
            ·
              refine ⟨78077637914864992588294517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52051758609909995058863011 78077637914864992588294517)
              ·
                refine ⟨7319778554518593055152611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78077637914864992588294517 7319778554518593055152611)
                ·
                  refine ⟨10979667831777889582728917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7319778554518593055152611 10979667831777889582728917)
                  ·
                    refine ⟨257335964807294287095209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10979667831777889582728917 257335964807294287095209)
                    ·
                      rfl

theorem cell23_1503480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_1503480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503480 prefixEnd_1503480 := by exact prefixLift 1503480
  have htrace : WordTrace (prefixWord ++ tailWord_1503480) baseStart_1503480 baseEnd_1503480 := by
    simpa [prefixWord, tailWord_1503480, baseEnd_1503480] using wordTrace_append hprefix tailTrace_1503480
  have hstable : (prefixWord ++ tailWord_1503480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503480).length < 2 ^ (prefixWord ++ tailWord_1503480).sum := by decide
  have hdescent : baseEnd_1503480 < baseStart_1503480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503495 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1503495 : Nat := 118140960795 + 1503495 * 2 ^ 59
def prefixEnd_1503495 : Nat := 4983230072969 + 3 ^ 40 * 1503495 * 2
def baseEnd_1503495 : Nat := 772015596631700302598059

theorem tailTrace_1503495 : CollatzResearch.WordTrace tailWord_1503495 prefixEnd_1503495 772015596631700302598059 := by
  unfold tailWord_1503495
  simp only [CollatzResearch.WordTrace]
  refine ⟨54836967688101866348087939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36557978458734577565391959 54836967688101866348087939)
  ·
    refine ⟨82255451532152799522131909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54836967688101866348087939 82255451532152799522131909)
    ·
      refine ⟨15422897162278649910399733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82255451532152799522131909 15422897162278649910399733)
      ·
        refine ⟨1445896608963623429099975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15422897162278649910399733 1445896608963623429099975)
        ·
          refine ⟨2168844913445435143649963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445896608963623429099975 2168844913445435143649963)
          ·
            refine ⟨3253267370168152715474945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168844913445435143649963 3253267370168152715474945)
            ·
              refine ⟨2439950527626114536606209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3253267370168152715474945 2439950527626114536606209)
              ·
                refine ⟨1829962895719585902454657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2439950527626114536606209 1829962895719585902454657)
                ·
                  refine ⟨1372472171789689426840993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1829962895719585902454657 1372472171789689426840993)
                  ·
                    refine ⟨1029354128842267070130745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1372472171789689426840993 1029354128842267070130745)
                    ·
                      refine ⟨772015596631700302598059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029354128842267070130745 772015596631700302598059)
                      ·
                        rfl

theorem cell23_1503495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1503495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503495 prefixEnd_1503495 := by exact prefixLift 1503495
  have htrace : WordTrace (prefixWord ++ tailWord_1503495) baseStart_1503495 baseEnd_1503495 := by
    simpa [prefixWord, tailWord_1503495, baseEnd_1503495] using wordTrace_append hprefix tailTrace_1503495
  have hstable : (prefixWord ++ tailWord_1503495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503495).length < 2 ^ (prefixWord ++ tailWord_1503495).sum := by decide
  have hdescent : baseEnd_1503495 < baseStart_1503495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503497 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 2, 5]
def baseStart_1503497 : Nat := 118140960795 + 1503497 * 2 ^ 59
def prefixEnd_1503497 : Nat := 4983230072969 + 3 ^ 40 * 1503497 * 2
def baseEnd_1503497 : Nat := 257338874531003098257683

theorem tailTrace_1503497 : CollatzResearch.WordTrace tailWord_1503497 prefixEnd_1503497 257338874531003098257683 := by
  unfold tailWord_1503497
  simp only [CollatzResearch.WordTrace]
  refine ⟨54837040634094620689660745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36558027089396413793107163 54837040634094620689660745)
  ·
    refine ⟨41127780475570965517245559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54837040634094620689660745 41127780475570965517245559)
    ·
      refine ⟨61691670713356448275868339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41127780475570965517245559 61691670713356448275868339)
      ·
        refine ⟨92537506070034672413802509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61691670713356448275868339 92537506070034672413802509)
        ·
          refine ⟨34701564776263002155175941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92537506070034672413802509 34701564776263002155175941)
          ·
            refine ⟨6506543395549312904095489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34701564776263002155175941 6506543395549312904095489)
            ·
              refine ⟨4879907546661984678071617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6506543395549312904095489 4879907546661984678071617)
              ·
                refine ⟨3659930659996488508553713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4879907546661984678071617 3659930659996488508553713)
                ·
                  refine ⟨2744947994997366381415285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3659930659996488508553713 2744947994997366381415285)
                  ·
                    refine ⟨257338874531003098257683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2744947994997366381415285 257338874531003098257683)
                    ·
                      rfl

theorem cell23_1503497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_1503497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503497 prefixEnd_1503497 := by exact prefixLift 1503497
  have htrace : WordTrace (prefixWord ++ tailWord_1503497) baseStart_1503497 baseEnd_1503497 := by
    simpa [prefixWord, tailWord_1503497, baseEnd_1503497] using wordTrace_append hprefix tailTrace_1503497
  have hstable : (prefixWord ++ tailWord_1503497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503497).length < 2 ^ (prefixWord ++ tailWord_1503497).sum := by decide
  have hdescent : baseEnd_1503497 < baseStart_1503497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503611 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 2, 3, 2]
def baseStart_1503611 : Nat := 118140960795 + 1503611 * 2 ^ 59
def prefixEnd_1503611 : Nat := 4983230072969 + 3 ^ 40 * 1503611 * 2
def baseEnd_1503611 : Nat := 772075160387621848747525

theorem tailTrace_1503611 : CollatzResearch.WordTrace tailWord_1503611 prefixEnd_1503611 772075160387621848747525 := by
  unfold tailWord_1503611
  simp only [CollatzResearch.WordTrace]
  refine ⟨54841198555681618159310687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36560799037121078772873791 54841198555681618159310687)
  ·
    refine ⟨82261797833522427238966031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54841198555681618159310687 82261797833522427238966031)
    ·
      refine ⟨123392696750283640858449047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82261797833522427238966031 123392696750283640858449047)
      ·
        refine ⟨185089045125425461287673571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123392696750283640858449047 185089045125425461287673571)
        ·
          refine ⟨277633567688138191931510357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185089045125425461287673571 277633567688138191931510357)
          ·
            refine ⟨3253518371345369436697387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 277633567688138191931510357 3253518371345369436697387)
            ·
              refine ⟨4880277557018054155046081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3253518371345369436697387 4880277557018054155046081)
              ·
                refine ⟨3660208167763540616284561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4880277557018054155046081 3660208167763540616284561)
                ·
                  refine ⟨2745156125822655462213421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3660208167763540616284561 2745156125822655462213421)
                  ·
                    refine ⟨1029433547183495798330033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745156125822655462213421 1029433547183495798330033)
                    ·
                      refine ⟨772075160387621848747525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029433547183495798330033 772075160387621848747525)
                      ·
                        rfl

theorem cell23_1503611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 3, 2].length) (baseStart_1503611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503611 prefixEnd_1503611 := by exact prefixLift 1503611
  have htrace : WordTrace (prefixWord ++ tailWord_1503611) baseStart_1503611 baseEnd_1503611 := by
    simpa [prefixWord, tailWord_1503611, baseEnd_1503611] using wordTrace_append hprefix tailTrace_1503611
  have hstable : (prefixWord ++ tailWord_1503611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503611).length < 2 ^ (prefixWord ++ tailWord_1503611).sum := by decide
  have hdescent : baseEnd_1503611 < baseStart_1503611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503624 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1503624 : Nat := 118140960795 + 1503624 * 2 ^ 59
def prefixEnd_1503624 : Nat := 4983230072969 + 3 ^ 40 * 1503624 * 2
def baseEnd_1503624 : Nat := 772081835636130297884965

theorem tailTrace_1503624 : CollatzResearch.WordTrace tailWord_1503624 prefixEnd_1503624 772081835636130297884965 := by
  unfold tailWord_1503624
  simp only [CollatzResearch.WordTrace]
  refine ⟨27420836352317260689766963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36561115136423014253022617 27420836352317260689766963)
  ·
    refine ⟨41131254528475891034650445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27420836352317260689766963 41131254528475891034650445)
    ·
      refine ⟨15424220448178459137993917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41131254528475891034650445 15424220448178459137993917)
      ·
        refine ⟨5784082668066922176747719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15424220448178459137993917 5784082668066922176747719)
        ·
          refine ⟨8676124002100383265121579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5784082668066922176747719 8676124002100383265121579)
          ·
            refine ⟨13014186003150574897682369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8676124002100383265121579 13014186003150574897682369)
            ·
              refine ⟨9760639502362931173261777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13014186003150574897682369 9760639502362931173261777)
              ·
                refine ⟨7320479626772198379946333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9760639502362931173261777 7320479626772198379946333)
                ·
                  refine ⟨2745179860039574392479875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7320479626772198379946333 2745179860039574392479875)
                  ·
                    refine ⟨4117769790059361588719813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2745179860039574392479875 4117769790059361588719813)
                    ·
                      refine ⟨772081835636130297884965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4117769790059361588719813 772081835636130297884965)
                      ·
                        rfl

theorem cell23_1503624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1503624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503624 prefixEnd_1503624 := by exact prefixLift 1503624
  have htrace : WordTrace (prefixWord ++ tailWord_1503624) baseStart_1503624 baseEnd_1503624 := by
    simpa [prefixWord, tailWord_1503624, baseEnd_1503624] using wordTrace_append hprefix tailTrace_1503624
  have hstable : (prefixWord ++ tailWord_1503624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503624).length < 2 ^ (prefixWord ++ tailWord_1503624).sum := by decide
  have hdescent : baseEnd_1503624 < baseStart_1503624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503641 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 5, 2, 2]
def baseStart_1503641 : Nat := 118140960795 + 1503641 * 2 ^ 59
def prefixEnd_1503641 : Nat := 4983230072969 + 3 ^ 40 * 1503641 * 2
def baseEnd_1503641 : Nat := 772090564807256731372387

theorem tailTrace_1503641 : CollatzResearch.WordTrace tailWord_1503641 prefixEnd_1503641 772090564807256731372387 := by
  unfold tailWord_1503641
  simp only [CollatzResearch.WordTrace]
  refine ⟨54842292745572933282902777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36561528497048622188601851 54842292745572933282902777)
  ·
    refine ⟨41131719559179699962177083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54842292745572933282902777 41131719559179699962177083)
    ·
      refine ⟨61697579338769549943265625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41131719559179699962177083 61697579338769549943265625)
      ·
        refine ⟨46273184504077162457449219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61697579338769549943265625 46273184504077162457449219)
        ·
          refine ⟨69409776756115743686173829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46273184504077162457449219 69409776756115743686173829)
          ·
            refine ⟨13014333141771701941157593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69409776756115743686173829 13014333141771701941157593)
            ·
              refine ⟨9760749856328776455868195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13014333141771701941157593 9760749856328776455868195)
              ·
                refine ⟨14641124784493164683802293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9760749856328776455868195 14641124784493164683802293)
                ·
                  refine ⟨1372605448546234189106465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14641124784493164683802293 1372605448546234189106465)
                  ·
                    refine ⟨1029454086409675641829849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1372605448546234189106465 1029454086409675641829849)
                    ·
                      refine ⟨772090564807256731372387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029454086409675641829849 772090564807256731372387)
                      ·
                        rfl

theorem cell23_1503641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 2, 2].length) (baseStart_1503641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503641 prefixEnd_1503641 := by exact prefixLift 1503641
  have htrace : WordTrace (prefixWord ++ tailWord_1503641) baseStart_1503641 baseEnd_1503641 := by
    simpa [prefixWord, tailWord_1503641, baseEnd_1503641] using wordTrace_append hprefix tailTrace_1503641
  have hstable : (prefixWord ++ tailWord_1503641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503641).length < 2 ^ (prefixWord ++ tailWord_1503641).sum := by decide
  have hdescent : baseEnd_1503641 < baseStart_1503641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503647 : List Nat := [1, 1, 2, 5, 1, 1, 1, 11]
def baseStart_1503647 : Nat := 118140960795 + 1503647 * 2 ^ 59
def prefixEnd_1503647 : Nat := 4983230072969 + 3 ^ 40 * 1503647 * 2
def baseEnd_1503647 : Nat := 28596060951525322514717

theorem tailTrace_1503647 : CollatzResearch.WordTrace tailWord_1503647 prefixEnd_1503647 28596060951525322514717 := by
  unfold tailWord_1503647
  simp only [CollatzResearch.WordTrace]
  refine ⟨54842511583551196307621195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36561674389034130871747463 54842511583551196307621195)
  ·
    refine ⟨82263767375326794461431793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54842511583551196307621195 82263767375326794461431793)
    ·
      refine ⟨61697825531495095846073845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82263767375326794461431793 61697825531495095846073845)
      ·
        refine ⟨5784171143577665235569423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61697825531495095846073845 5784171143577665235569423)
        ·
          refine ⟨8676256715366497853354135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5784171143577665235569423 8676256715366497853354135)
          ·
            refine ⟨13014385073049746780031203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8676256715366497853354135 13014385073049746780031203)
            ·
              refine ⟨19521577609574620170046805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13014385073049746780031203 19521577609574620170046805)
              ·
                refine ⟨28596060951525322514717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 19521577609574620170046805 28596060951525322514717)
                ·
                  rfl

theorem cell23_1503647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 11].length) (baseStart_1503647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503647 prefixEnd_1503647 := by exact prefixLift 1503647
  have htrace : WordTrace (prefixWord ++ tailWord_1503647) baseStart_1503647 baseEnd_1503647 := by
    simpa [prefixWord, tailWord_1503647, baseEnd_1503647] using wordTrace_append hprefix tailTrace_1503647
  have hstable : (prefixWord ++ tailWord_1503647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503647).length < 2 ^ (prefixWord ++ tailWord_1503647).sum := by decide
  have hdescent : baseEnd_1503647 < baseStart_1503647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503669 : List Nat := [1, 3, 3, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_1503669 : Nat := 118140960795 + 1503669 * 2 ^ 59
def prefixEnd_1503669 : Nat := 4983230072969 + 3 ^ 40 * 1503669 * 2
def baseEnd_1503669 : Nat := 772104942265582621822259

theorem tailTrace_1503669 : CollatzResearch.WordTrace tailWord_1503669 prefixEnd_1503669 772104942265582621822259 := by
  unfold tailWord_1503669
  simp only [CollatzResearch.WordTrace]
  refine ⟨54843313989471494064922061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36562209326314329376614707 54843313989471494064922061)
  ·
    refine ⟨20566242746051810274345773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54843313989471494064922061 20566242746051810274345773)
    ·
      refine ⟨7712341029769428852879665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20566242746051810274345773 7712341029769428852879665)
      ·
        refine ⟨5784255772327071639659749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7712341029769428852879665 5784255772327071639659749)
        ·
          refine ⟨1084547957311325932436203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5784255772327071639659749 1084547957311325932436203)
          ·
            refine ⟨1626821935966988898654305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084547957311325932436203 1626821935966988898654305)
            ·
              refine ⟨1220116451975241673990729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1626821935966988898654305 1220116451975241673990729)
              ·
                refine ⟨915087338981431255493047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1220116451975241673990729 915087338981431255493047)
                ·
                  refine ⟨1372631008472146883239571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915087338981431255493047 1372631008472146883239571)
                  ·
                    refine ⟨2058946512708220324859357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1372631008472146883239571 2058946512708220324859357)
                    ·
                      refine ⟨772104942265582621822259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2058946512708220324859357 772104942265582621822259)
                      ·
                        rfl

theorem cell23_1503669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_1503669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503669 prefixEnd_1503669 := by exact prefixLift 1503669
  have htrace : WordTrace (prefixWord ++ tailWord_1503669) baseStart_1503669 baseEnd_1503669 := by
    simpa [prefixWord, tailWord_1503669, baseEnd_1503669] using wordTrace_append hprefix tailTrace_1503669
  have hstable : (prefixWord ++ tailWord_1503669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503669).length < 2 ^ (prefixWord ++ tailWord_1503669).sum := by decide
  have hdescent : baseEnd_1503669 < baseStart_1503669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503698 : List Nat := [3, 2, 2, 4, 1, 1, 3, 7]
def baseStart_1503698 : Nat := 118140960795 + 1503698 * 2 ^ 59
def prefixEnd_1503698 : Nat := 4983230072969 + 3 ^ 40 * 1503698 * 2
def baseEnd_1503698 : Nat := 28597030859428259568875

theorem tailTrace_1503698 : CollatzResearch.WordTrace tailWord_1503698 prefixEnd_1503698 28597030859428259568875 := by
  unfold tailWord_1503698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13711092926591608004431937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36562914470910954678485165 13711092926591608004431937)
  ·
    refine ⟨10283319694943706003323953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13711092926591608004431937 10283319694943706003323953)
    ·
      refine ⟨7712489771207779502492965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10283319694943706003323953 7712489771207779502492965)
      ·
        refine ⟨1446091832101458656717431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7712489771207779502492965 1446091832101458656717431)
        ·
          refine ⟨2169137748152187985076147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446091832101458656717431 2169137748152187985076147)
          ·
            refine ⟨3253706622228281977614221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169137748152187985076147 3253706622228281977614221)
            ·
              refine ⟨1220139983335605741605333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3253706622228281977614221 1220139983335605741605333)
              ·
                refine ⟨28597030859428259568875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1220139983335605741605333 28597030859428259568875)
                ·
                  rfl

theorem cell23_1503698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 7].length) (baseStart_1503698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503698 prefixEnd_1503698 := by exact prefixLift 1503698
  have htrace : WordTrace (prefixWord ++ tailWord_1503698) baseStart_1503698 baseEnd_1503698 := by
    simpa [prefixWord, tailWord_1503698, baseEnd_1503698] using wordTrace_append hprefix tailTrace_1503698
  have hstable : (prefixWord ++ tailWord_1503698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503698).length < 2 ^ (prefixWord ++ tailWord_1503698).sum := by decide
  have hdescent : baseEnd_1503698 < baseStart_1503698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503725 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1503725 : Nat := 118140960795 + 1503725 * 2 ^ 59
def prefixEnd_1503725 : Nat := 4983230072969 + 3 ^ 40 * 1503725 * 2
def baseEnd_1503725 : Nat := 772133697182234402722001

theorem tailTrace_1503725 : CollatzResearch.WordTrace tailWord_1503725 prefixEnd_1503725 772133697182234402722001 := by
  unfold tailWord_1503725
  simp only [CollatzResearch.WordTrace]
  refine ⟨54845356477268615628960629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36563570984845743752640419 54845356477268615628960629)
  ·
    refine ⟨5141752169743932715215059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54845356477268615628960629 5141752169743932715215059)
    ·
      refine ⟨7712628254615899072822589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5141752169743932715215059 7712628254615899072822589)
      ·
        refine ⟨2892235595480962152308471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7712628254615899072822589 2892235595480962152308471)
        ·
          refine ⟨4338353393221443228462707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892235595480962152308471 4338353393221443228462707)
          ·
            refine ⟨6507530089832164842694061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338353393221443228462707 6507530089832164842694061)
            ·
              refine ⟨2440323783687061816010273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6507530089832164842694061 2440323783687061816010273)
              ·
                refine ⟨1830242837765296362007705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2440323783687061816010273 1830242837765296362007705)
                ·
                  refine ⟨1372682128323972271505779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1830242837765296362007705 1372682128323972271505779)
                  ·
                    refine ⟨2059023192485958407258669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1372682128323972271505779 2059023192485958407258669)
                    ·
                      refine ⟨772133697182234402722001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2059023192485958407258669 772133697182234402722001)
                      ·
                        rfl

theorem cell23_1503725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1503725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503725 prefixEnd_1503725 := by exact prefixLift 1503725
  have htrace : WordTrace (prefixWord ++ tailWord_1503725) baseStart_1503725 baseEnd_1503725 := by
    simpa [prefixWord, tailWord_1503725, baseEnd_1503725] using wordTrace_append hprefix tailTrace_1503725
  have hstable : (prefixWord ++ tailWord_1503725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503725).length < 2 ^ (prefixWord ++ tailWord_1503725).sum := by decide
  have hdescent : baseEnd_1503725 < baseStart_1503725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503754 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 7]
def baseStart_1503754 : Nat := 118140960795 + 1503754 * 2 ^ 59
def prefixEnd_1503754 : Nat := 4983230072969 + 3 ^ 40 * 1503754 * 2
def baseEnd_1503754 : Nat := 85794287569023865473263

theorem tailTrace_1503754 : CollatzResearch.WordTrace tailWord_1503754 prefixEnd_1503754 85794287569023865473263 := by
  unfold tailWord_1503754
  simp only [CollatzResearch.WordTrace]
  refine ⟨13711603548540888395441579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36564276129442369054510877 13711603548540888395441579)
  ·
    refine ⟨20567405322811332593162369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13711603548540888395441579 20567405322811332593162369)
    ·
      refine ⟨15425553992108499444871777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20567405322811332593162369 15425553992108499444871777)
      ·
        refine ⟨11569165494081374583653833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15425553992108499444871777 11569165494081374583653833)
        ·
          refine ⟨8676874120561030937740375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11569165494081374583653833 8676874120561030937740375)
          ·
            refine ⟨13015311180841546406610563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8676874120561030937740375 13015311180841546406610563)
            ·
              refine ⟨19522966771262319609915845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13015311180841546406610563 19522966771262319609915845)
              ·
                refine ⟨3660556269611684926859221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19522966771262319609915845 3660556269611684926859221)
                ·
                  refine ⟨85794287569023865473263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3660556269611684926859221 85794287569023865473263)
                  ·
                    rfl

theorem cell23_1503754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_1503754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503754 prefixEnd_1503754 := by exact prefixLift 1503754
  have htrace : WordTrace (prefixWord ++ tailWord_1503754) baseStart_1503754 baseEnd_1503754 := by
    simpa [prefixWord, tailWord_1503754, baseEnd_1503754] using wordTrace_append hprefix tailTrace_1503754
  have hstable : (prefixWord ++ tailWord_1503754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503754).length < 2 ^ (prefixWord ++ tailWord_1503754).sum := by decide
  have hdescent : baseEnd_1503754 < baseStart_1503754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503794 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1503794 : Nat := 118140960795 + 1503794 * 2 ^ 59
def prefixEnd_1503794 : Nat := 4983230072969 + 3 ^ 40 * 1503794 * 2
def baseEnd_1503794 : Nat := 772169127347394632759183

theorem tailTrace_1503794 : CollatzResearch.WordTrace tailWord_1503794 prefixEnd_1503794 772169127347394632759183 := by
  unfold tailWord_1503794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13711968278504660103305609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36565248742679093608814957 13711968278504660103305609)
  ·
    refine ⟨10283976208878495077479207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13711968278504660103305609 10283976208878495077479207)
    ·
      refine ⟨15425964313317742616218811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10283976208878495077479207 15425964313317742616218811)
      ·
        refine ⟨23138946469976613924328217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15425964313317742616218811 23138946469976613924328217)
        ·
          refine ⟨17354209852482460443246163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23138946469976613924328217 17354209852482460443246163)
          ·
            refine ⟨26031314778723690664869245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17354209852482460443246163 26031314778723690664869245)
            ·
              refine ⟨9761743042021383999325967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26031314778723690664869245 9761743042021383999325967)
              ·
                refine ⟨14642614563032075998988951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9761743042021383999325967 14642614563032075998988951)
                ·
                  refine ⟨21963921844548113998483427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14642614563032075998988951 21963921844548113998483427)
                  ·
                    refine ⟨32945882766822170997725141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21963921844548113998483427 32945882766822170997725141)
                    ·
                      refine ⟨772169127347394632759183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32945882766822170997725141 772169127347394632759183)
                      ·
                        rfl

theorem cell23_1503794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1503794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503794 prefixEnd_1503794 := by exact prefixLift 1503794
  have htrace : WordTrace (prefixWord ++ tailWord_1503794) baseStart_1503794 baseEnd_1503794 := by
    simpa [prefixWord, tailWord_1503794, baseEnd_1503794] using wordTrace_append hprefix tailTrace_1503794
  have hstable : (prefixWord ++ tailWord_1503794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503794).length < 2 ^ (prefixWord ++ tailWord_1503794).sum := by decide
  have hdescent : baseEnd_1503794 < baseStart_1503794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503864 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_1503864 : Nat := 118140960795 + 1503864 * 2 ^ 59
def prefixEnd_1503864 : Nat := 4983230072969 + 3 ^ 40 * 1503864 * 2
def baseEnd_1503864 : Nat := 772205070993209358883861

theorem tailTrace_1503864 : CollatzResearch.WordTrace tailWord_1503864 prefixEnd_1503864 772205070993209358883861 := by
  unfold tailWord_1503864
  simp only [CollatzResearch.WordTrace]
  refine ⟨27425213111882521184135323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36566950815843361578847097 27425213111882521184135323)
  ·
    refine ⟨41137819667823781776202985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27425213111882521184135323 41137819667823781776202985)
    ·
      refine ⟨30853364750867836332152239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41137819667823781776202985 30853364750867836332152239)
      ·
        refine ⟨46280047126301754498228359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30853364750867836332152239 46280047126301754498228359)
        ·
          refine ⟨69420070689452631747342539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46280047126301754498228359 69420070689452631747342539)
          ·
            refine ⟨104130106034178947621013809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69420070689452631747342539 104130106034178947621013809)
            ·
              refine ⟨78097579525634210715760357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104130106034178947621013809 78097579525634210715760357)
              ·
                refine ⟨14643296161056414509205067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78097579525634210715760357 14643296161056414509205067)
                ·
                  refine ⟨21964944241584621763807601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14643296161056414509205067 21964944241584621763807601)
                  ·
                    refine ⟨16473708181188466322855701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21964944241584621763807601 16473708181188466322855701)
                    ·
                      refine ⟨772205070993209358883861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16473708181188466322855701 772205070993209358883861)
                      ·
                        rfl

theorem cell23_1503864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_1503864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503864 prefixEnd_1503864 := by exact prefixLift 1503864
  have htrace : WordTrace (prefixWord ++ tailWord_1503864) baseStart_1503864 baseEnd_1503864 := by
    simpa [prefixWord, tailWord_1503864, baseEnd_1503864] using wordTrace_append hprefix tailTrace_1503864
  have hstable : (prefixWord ++ tailWord_1503864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503864).length < 2 ^ (prefixWord ++ tailWord_1503864).sum := by decide
  have hdescent : baseEnd_1503864 < baseStart_1503864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503882 : List Nat := [3, 1, 2, 3, 3, 1, 2, 3, 1, 4]
def baseStart_1503882 : Nat := 118140960795 + 1503882 * 2 ^ 59
def prefixEnd_1503882 : Nat := 4983230072969 + 3 ^ 40 * 1503882 * 2
def baseEnd_1503882 : Nat := 257404771214996762819593

theorem tailTrace_1503882 : CollatzResearch.WordTrace tailWord_1503882 prefixEnd_1503882 257404771214996762819593 := by
  unfold tailWord_1503882
  simp only [CollatzResearch.WordTrace]
  refine ⟨13712770684424957860606475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36567388491799887628283933 13712770684424957860606475)
  ·
    refine ⟨20569156026637436790909713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13712770684424957860606475 20569156026637436790909713)
    ·
      refine ⟨15426867019978077593182285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20569156026637436790909713 15426867019978077593182285)
      ·
        refine ⟨5785075132491779097443357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15426867019978077593182285 5785075132491779097443357)
        ·
          refine ⟨2169403174684417161541259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5785075132491779097443357 2169403174684417161541259)
          ·
            refine ⟨3254104762026625742311889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169403174684417161541259 3254104762026625742311889)
            ·
              refine ⟨2440578571519969306733917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3254104762026625742311889 2440578571519969306733917)
              ·
                refine ⟨915216964319988490025219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2440578571519969306733917 915216964319988490025219)
                ·
                  refine ⟨1372825446479982735037829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915216964319988490025219 1372825446479982735037829)
                  ·
                    refine ⟨257404771214996762819593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1372825446479982735037829 257404771214996762819593)
                    ·
                      rfl

theorem cell23_1503882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_1503882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503882 prefixEnd_1503882 := by exact prefixLift 1503882
  have htrace : WordTrace (prefixWord ++ tailWord_1503882) baseStart_1503882 baseEnd_1503882 := by
    simpa [prefixWord, tailWord_1503882, baseEnd_1503882] using wordTrace_append hprefix tailTrace_1503882
  have hstable : (prefixWord ++ tailWord_1503882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503882).length < 2 ^ (prefixWord ++ tailWord_1503882).sum := by decide
  have hdescent : baseEnd_1503882 < baseStart_1503882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503891 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 1, 5]
def baseStart_1503891 : Nat := 118140960795 + 1503891 * 2 ^ 59
def prefixEnd_1503891 : Nat := 4983230072969 + 3 ^ 40 * 1503891 * 2
def baseEnd_1503891 : Nat := 257406311656960251082079

theorem tailTrace_1503891 : CollatzResearch.WordTrace tailWord_1503891 prefixEnd_1503891 257406311656960251082079 := by
  unfold tailWord_1503891
  simp only [CollatzResearch.WordTrace]
  refine ⟨54851410994667225979503527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36567607329778150653002351 54851410994667225979503527)
  ·
    refine ⟨82277116492000838969255291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54851410994667225979503527 82277116492000838969255291)
    ·
      refine ⟨123415674738001258453882937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82277116492000838969255291 123415674738001258453882937)
      ·
        refine ⟨92561756053500943840412203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123415674738001258453882937 92561756053500943840412203)
        ·
          refine ⟨138842634080251415760618305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92561756053500943840412203 138842634080251415760618305)
          ·
            refine ⟨104131975560188561820463729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138842634080251415760618305 104131975560188561820463729)
            ·
              refine ⟨78098981670141421365347797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104131975560188561820463729 78098981670141421365347797)
              ·
                refine ⟨1830444882893939563250339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 78098981670141421365347797 1830444882893939563250339)
                ·
                  refine ⟨2745667324340909344875509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830444882893939563250339 2745667324340909344875509)
                  ·
                    refine ⟨257406311656960251082079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2745667324340909344875509 257406311656960251082079)
                    ·
                      rfl

theorem cell23_1503891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 5].length) (baseStart_1503891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503891 prefixEnd_1503891 := by exact prefixLift 1503891
  have htrace : WordTrace (prefixWord ++ tailWord_1503891) baseStart_1503891 baseEnd_1503891 := by
    simpa [prefixWord, tailWord_1503891, baseEnd_1503891] using wordTrace_append hprefix tailTrace_1503891
  have hstable : (prefixWord ++ tailWord_1503891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503891).length < 2 ^ (prefixWord ++ tailWord_1503891).sum := by decide
  have hdescent : baseEnd_1503891 < baseStart_1503891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503925 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1503925 : Nat := 118140960795 + 1503925 * 2 ^ 59
def prefixEnd_1503925 : Nat := 4983230072969 + 3 ^ 40 * 1503925 * 2
def baseEnd_1503925 : Nat := 257412131104377873407027

theorem tailTrace_1503925 : CollatzResearch.WordTrace tailWord_1503925 prefixEnd_1503925 257412131104377873407027 := by
  unfold tailWord_1503925
  simp only [CollatzResearch.WordTrace]
  refine ⟨54852651076544049786241229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36568434051029366524160819 54852651076544049786241229)
  ·
    refine ⟨20569744153704018669840461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54852651076544049786241229 20569744153704018669840461)
    ·
      refine ⟨7713654057639007001190173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20569744153704018669840461 7713654057639007001190173)
      ·
        refine ⟨2892620271614627625446315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7713654057639007001190173 2892620271614627625446315)
        ·
          refine ⟨4338930407421941438169473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892620271614627625446315 4338930407421941438169473)
          ·
            refine ⟨3254197805566456078627105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4338930407421941438169473 3254197805566456078627105)
            ·
              refine ⟨2440648354174842058970329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3254197805566456078627105 2440648354174842058970329)
              ·
                refine ⟨1830486265631131544227747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2440648354174842058970329 1830486265631131544227747)
                ·
                  refine ⟨2745729398446697316341621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830486265631131544227747 2745729398446697316341621)
                  ·
                    refine ⟨257412131104377873407027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2745729398446697316341621 257412131104377873407027)
                    ·
                      rfl

theorem cell23_1503925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1503925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503925 prefixEnd_1503925 := by exact prefixLift 1503925
  have htrace : WordTrace (prefixWord ++ tailWord_1503925) baseStart_1503925 baseEnd_1503925 := by
    simpa [prefixWord, tailWord_1503925, baseEnd_1503925] using wordTrace_append hprefix tailTrace_1503925
  have hstable : (prefixWord ++ tailWord_1503925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503925).length < 2 ^ (prefixWord ++ tailWord_1503925).sum := by decide
  have hdescent : baseEnd_1503925 < baseStart_1503925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503948 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1503948 : Nat := 118140960795 + 1503948 * 2 ^ 59
def prefixEnd_1503948 : Nat := 4983230072969 + 3 ^ 40 * 1503948 * 2
def baseEnd_1503948 : Nat := 772248203368187030233475

theorem tailTrace_1503948 : CollatzResearch.WordTrace tailWord_1503948 prefixEnd_1503948 772248203368187030233475 := by
  unfold tailWord_1503948
  simp only [CollatzResearch.WordTrace]
  refine ⟨27426744977730362357164249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36568993303640483142885665 27426744977730362357164249)
  ·
    refine ⟨20570058733297771767873187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27426744977730362357164249 20570058733297771767873187)
    ·
      refine ⟨30855088099946657651809781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20570058733297771767873187 30855088099946657651809781)
      ·
        refine ⟨2892664509369999154857167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30855088099946657651809781 2892664509369999154857167)
        ·
          refine ⟨4338996764054998732285751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892664509369999154857167 4338996764054998732285751)
          ·
            refine ⟨6508495146082498098428627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338996764054998732285751 6508495146082498098428627)
            ·
              refine ⟨9762742719123747147642941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6508495146082498098428627 9762742719123747147642941)
              ·
                refine ⟨3661028519671405180366103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9762742719123747147642941 3661028519671405180366103)
                ·
                  refine ⟨5491542779507107770549155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661028519671405180366103 5491542779507107770549155)
                  ·
                    refine ⟨8237314169260661655823733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5491542779507107770549155 8237314169260661655823733)
                    ·
                      refine ⟨772248203368187030233475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8237314169260661655823733 772248203368187030233475)
                      ·
                        rfl

theorem cell23_1503948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1503948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503948 prefixEnd_1503948 := by exact prefixLift 1503948
  have htrace : WordTrace (prefixWord ++ tailWord_1503948) baseStart_1503948 baseEnd_1503948 := by
    simpa [prefixWord, tailWord_1503948, baseEnd_1503948] using wordTrace_append hprefix tailTrace_1503948
  have hstable : (prefixWord ++ tailWord_1503948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503948).length < 2 ^ (prefixWord ++ tailWord_1503948).sum := by decide
  have hdescent : baseEnd_1503948 < baseStart_1503948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503949 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_1503949 : Nat := 118140960795 + 1503949 * 2 ^ 59
def prefixEnd_1503949 : Nat := 4983230072969 + 3 ^ 40 * 1503949 * 2
def baseEnd_1503949 : Nat := 772248716848841526320971

theorem tailTrace_1503949 : CollatzResearch.WordTrace tailWord_1503949 prefixEnd_1503949 772248716848841526320971 := by
  unfold tailWord_1503949
  simp only [CollatzResearch.WordTrace]
  refine ⟨54853526428457101885114901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36569017618971401256743267 54853526428457101885114901)
  ·
    refine ⟨2571259051333926650864761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54853526428457101885114901 2571259051333926650864761)
    ·
      refine ⟨1928444288500444988148571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2571259051333926650864761 1928444288500444988148571)
      ·
        refine ⟨2892666432750667482222857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928444288500444988148571 2892666432750667482222857)
        ·
          refine ⟨2169499824563000611667143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2892666432750667482222857 2169499824563000611667143)
          ·
            refine ⟨3254249736844500917500715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169499824563000611667143 3254249736844500917500715)
            ·
              refine ⟨4881374605266751376251073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254249736844500917500715 4881374605266751376251073)
              ·
                refine ⟨3661030953950063532188305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4881374605266751376251073 3661030953950063532188305)
                ·
                  refine ⟨2745773215462547649141229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3661030953950063532188305 2745773215462547649141229)
                  ·
                    refine ⟨1029664955798455368427961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745773215462547649141229 1029664955798455368427961)
                    ·
                      refine ⟨772248716848841526320971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029664955798455368427961 772248716848841526320971)
                      ·
                        rfl

theorem cell23_1503949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_1503949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503949 prefixEnd_1503949 := by exact prefixLift 1503949
  have htrace : WordTrace (prefixWord ++ tailWord_1503949) baseStart_1503949 baseEnd_1503949 := by
    simpa [prefixWord, tailWord_1503949, baseEnd_1503949] using wordTrace_append hprefix tailTrace_1503949
  have hstable : (prefixWord ++ tailWord_1503949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503949).length < 2 ^ (prefixWord ++ tailWord_1503949).sum := by decide
  have hdescent : baseEnd_1503949 < baseStart_1503949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503956 : List Nat := [2, 4, 1, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1503956 : Nat := 118140960795 + 1503956 * 2 ^ 59
def prefixEnd_1503956 : Nat := 4983230072969 + 3 ^ 40 * 1503956 * 2
def baseEnd_1503956 : Nat := 772252311213422998933439

theorem tailTrace_1503956 : CollatzResearch.WordTrace tailWord_1503956 prefixEnd_1503956 772252311213422998933439 := by
  unfold tailWord_1503956
  simp only [CollatzResearch.WordTrace]
  refine ⟨27426890869715871040309861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36569187826287828053746481 27426890869715871040309861)
  ·
    refine ⟨5142542038071725820058099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27426890869715871040309861 5142542038071725820058099)
    ·
      refine ⟨7713813057107588730087149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5142542038071725820058099 7713813057107588730087149)
      ·
        refine ⟨2892679896415345773782681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7713813057107588730087149 2892679896415345773782681)
        ·
          refine ⟨2169509922311509330337011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2892679896415345773782681 2169509922311509330337011)
          ·
            refine ⟨3254264883467263995505517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169509922311509330337011 3254264883467263995505517)
            ·
              refine ⟨1220349331300223998314569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3254264883467263995505517 1220349331300223998314569)
              ·
                refine ⟨915261998475167998735927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1220349331300223998314569 915261998475167998735927)
                ·
                  refine ⟨1372892997712751998103891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915261998475167998735927 1372892997712751998103891)
                  ·
                    refine ⟨2059339496569127997155837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1372892997712751998103891 2059339496569127997155837)
                    ·
                      refine ⟨772252311213422998933439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2059339496569127997155837 772252311213422998933439)
                      ·
                        rfl

theorem cell23_1503956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1503956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503956 prefixEnd_1503956 := by exact prefixLift 1503956
  have htrace : WordTrace (prefixWord ++ tailWord_1503956) baseStart_1503956 baseEnd_1503956 := by
    simpa [prefixWord, tailWord_1503956, baseEnd_1503956] using wordTrace_append hprefix tailTrace_1503956
  have hstable : (prefixWord ++ tailWord_1503956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503956).length < 2 ^ (prefixWord ++ tailWord_1503956).sum := by decide
  have hdescent : baseEnd_1503956 < baseStart_1503956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503972 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_1503972 : Nat := 118140960795 + 1503972 * 2 ^ 59
def prefixEnd_1503972 : Nat := 4983230072969 + 3 ^ 40 * 1503972 * 2
def baseEnd_1503972 : Nat := 257420175634631645444455

theorem tailTrace_1503972 : CollatzResearch.WordTrace tailWord_1503972 prefixEnd_1503972 257420175634631645444455 := by
  unfold tailWord_1503972
  simp only [CollatzResearch.WordTrace]
  refine ⟨27427182653686888406601085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36569576871582517875468113 27427182653686888406601085)
  ·
    refine ⟨10285193495132583152475407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27427182653686888406601085 10285193495132583152475407)
    ·
      refine ⟨15427790242698874728713111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10285193495132583152475407 15427790242698874728713111)
      ·
        refine ⟨23141685364048312093069667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15427790242698874728713111 23141685364048312093069667)
        ·
          refine ⟨34712528046072468139604501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23141685364048312093069667 34712528046072468139604501)
          ·
            refine ⟨1627149752159646944043961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34712528046072468139604501 1627149752159646944043961)
            ·
              refine ⟨1220362314119735208032971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1627149752159646944043961 1220362314119735208032971)
              ·
                refine ⟨1830543471179602812049457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220362314119735208032971 1830543471179602812049457)
                ·
                  refine ⟨1372907603384702109037093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1830543471179602812049457 1372907603384702109037093)
                  ·
                    refine ⟨257420175634631645444455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1372907603384702109037093 257420175634631645444455)
                    ·
                      rfl

theorem cell23_1503972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_1503972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503972 prefixEnd_1503972 := by exact prefixLift 1503972
  have htrace : WordTrace (prefixWord ++ tailWord_1503972) baseStart_1503972 baseEnd_1503972 := by
    simpa [prefixWord, tailWord_1503972, baseEnd_1503972] using wordTrace_append hprefix tailTrace_1503972
  have hstable : (prefixWord ++ tailWord_1503972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503972).length < 2 ^ (prefixWord ++ tailWord_1503972).sum := by decide
  have hdescent : baseEnd_1503972 < baseStart_1503972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503978 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_1503978 : Nat := 118140960795 + 1503978 * 2 ^ 59
def prefixEnd_1503978 : Nat := 4983230072969 + 3 ^ 40 * 1503978 * 2
def baseEnd_1503978 : Nat := 772263607787821912858337

theorem tailTrace_1503978 : CollatzResearch.WordTrace tailWord_1503978 prefixEnd_1503978 772263607787821912858337 := by
  unfold tailWord_1503978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13713646036338009959480147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36569722763568026558613725 13713646036338009959480147)
  ·
    refine ⟨20570469054507014939220221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13713646036338009959480147 20570469054507014939220221)
    ·
      refine ⟨7713925895440130602207583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20570469054507014939220221 7713925895440130602207583)
      ·
        refine ⟨11570888843160195903311375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7713925895440130602207583 11570888843160195903311375)
        ·
          refine ⟨17356333264740293854967063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11570888843160195903311375 17356333264740293854967063)
          ·
            refine ⟨26034499897110440782450595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17356333264740293854967063 26034499897110440782450595)
            ·
              refine ⟨39051749845665661173675893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26034499897110440782450595 39051749845665661173675893)
              ·
                refine ⟨3661101548031155735032115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39051749845665661173675893 3661101548031155735032115)
                ·
                  refine ⟨5491652322046733602548173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661101548031155735032115 5491652322046733602548173)
                  ·
                    refine ⟨2059369620767525100955565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5491652322046733602548173 2059369620767525100955565)
                    ·
                      refine ⟨772263607787821912858337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2059369620767525100955565 772263607787821912858337)
                      ·
                        rfl

theorem cell23_1503978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_1503978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503978 prefixEnd_1503978 := by exact prefixLift 1503978
  have htrace : WordTrace (prefixWord ++ tailWord_1503978) baseStart_1503978 baseEnd_1503978 := by
    simpa [prefixWord, tailWord_1503978, baseEnd_1503978] using wordTrace_append hprefix tailTrace_1503978
  have hstable : (prefixWord ++ tailWord_1503978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503978).length < 2 ^ (prefixWord ++ tailWord_1503978).sum := by decide
  have hdescent : baseEnd_1503978 < baseStart_1503978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503982 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_1503982 : Nat := 118140960795 + 1503982 * 2 ^ 59
def prefixEnd_1503982 : Nat := 4983230072969 + 3 ^ 40 * 1503982 * 2
def baseEnd_1503982 : Nat := 772265661710439897208319

theorem tailTrace_1503982 : CollatzResearch.WordTrace tailWord_1503982 prefixEnd_1503982 772265661710439897208319 := by
  unfold tailWord_1503982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6856841254667193565133275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36569820024891699014044133 6856841254667193565133275)
  ·
    refine ⟨10285261882000790347699913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6856841254667193565133275 10285261882000790347699913)
    ·
      refine ⟨7713946411500592760774935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10285261882000790347699913 7713946411500592760774935)
      ·
        refine ⟨11570919617250889141162403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7713946411500592760774935 11570919617250889141162403)
        ·
          refine ⟨17356379425876333711743605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11570919617250889141162403 17356379425876333711743605)
          ·
            refine ⟨1627160571175906285475963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17356379425876333711743605 1627160571175906285475963)
            ·
              refine ⟨2440740856763859428213945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1627160571175906285475963 2440740856763859428213945)
              ·
                refine ⟨1830555642572894571160459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2440740856763859428213945 1830555642572894571160459)
                ·
                  refine ⟨2745833463859341856740689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830555642572894571160459 2745833463859341856740689)
                  ·
                    refine ⟨2059375097894506392555517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2745833463859341856740689 2059375097894506392555517)
                    ·
                      refine ⟨772265661710439897208319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2059375097894506392555517 772265661710439897208319)
                      ·
                        rfl

theorem cell23_1503982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_1503982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1503982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1503982 prefixEnd_1503982 := by exact prefixLift 1503982
  have htrace : WordTrace (prefixWord ++ tailWord_1503982) baseStart_1503982 baseEnd_1503982 := by
    simpa [prefixWord, tailWord_1503982, baseEnd_1503982] using wordTrace_append hprefix tailTrace_1503982
  have hstable : (prefixWord ++ tailWord_1503982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503982).length < 2 ^ (prefixWord ++ tailWord_1503982).sum := by decide
  have hdescent : baseEnd_1503982 < baseStart_1503982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504005 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 1, 3, 2]
def baseStart_1504005 : Nat := 118140960795 + 1504005 * 2 ^ 59
def prefixEnd_1504005 : Nat := 4983230072969 + 3 ^ 40 * 1504005 * 2
def baseEnd_1504005 : Nat := 772277471765493307220713

theorem tailTrace_1504005 : CollatzResearch.WordTrace tailWord_1504005 prefixEnd_1504005 772277471765493307220713 := by
  unfold tailWord_1504005
  simp only [CollatzResearch.WordTrace]
  refine ⟨54855568916254223449153469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36570379277502815632768979 54855568916254223449153469)
  ·
    refine ⟨20570838343595333793432551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54855568916254223449153469 20570838343595333793432551)
    ·
      refine ⟨30856257515393000690148827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20570838343595333793432551 30856257515393000690148827)
      ·
        refine ⟨46284386273089501035223241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30856257515393000690148827 46284386273089501035223241)
        ·
          refine ⟨34713289704817125776417431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46284386273089501035223241 34713289704817125776417431)
          ·
            refine ⟨52069934557225688664626147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34713289704817125776417431 52069934557225688664626147)
            ·
              refine ⟨78104901835838532996939221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52069934557225688664626147 78104901835838532996939221)
              ·
                refine ⟨1830583636777465617115763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 78104901835838532996939221 1830583636777465617115763)
                ·
                  refine ⟨2745875455166198425673645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830583636777465617115763 2745875455166198425673645)
                  ·
                    refine ⟨1029703295687324409627617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2745875455166198425673645 1029703295687324409627617)
                    ·
                      refine ⟨772277471765493307220713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029703295687324409627617 772277471765493307220713)
                      ·
                        rfl

theorem cell23_1504005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 3, 2].length) (baseStart_1504005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504005 prefixEnd_1504005 := by exact prefixLift 1504005
  have htrace : WordTrace (prefixWord ++ tailWord_1504005) baseStart_1504005 baseEnd_1504005 := by
    simpa [prefixWord, tailWord_1504005, baseEnd_1504005] using wordTrace_append hprefix tailTrace_1504005
  have hstable : (prefixWord ++ tailWord_1504005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504005).length < 2 ^ (prefixWord ++ tailWord_1504005).sum := by decide
  have hdescent : baseEnd_1504005 < baseStart_1504005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504011 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 2, 6]
def baseStart_1504011 : Nat := 118140960795 + 1504011 * 2 ^ 59
def prefixEnd_1504011 : Nat := 4983230072969 + 3 ^ 40 * 1504011 * 2
def baseEnd_1504011 : Nat := 257426850883140094581895

theorem tailTrace_1504011 : CollatzResearch.WordTrace tailWord_1504011 prefixEnd_1504011 257426850883140094581895 := by
  unfold tailWord_1504011
  simp only [CollatzResearch.WordTrace]
  refine ⟨54855787754232486473871887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36570525169488324315914591 54855787754232486473871887)
  ·
    refine ⟨82283681631348729710807831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54855787754232486473871887 82283681631348729710807831)
    ·
      refine ⟨123425522447023094566211747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82283681631348729710807831 123425522447023094566211747)
      ·
        refine ⟨185138283670534641849317621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123425522447023094566211747 185138283670534641849317621)
        ·
          refine ⟨17356714094112622673373527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185138283670534641849317621 17356714094112622673373527)
          ·
            refine ⟨26035071141168934010060291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17356714094112622673373527 26035071141168934010060291)
            ·
              refine ⟨39052606711753401015090437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26035071141168934010060291 39052606711753401015090437)
              ·
                refine ⟨7322363758453762690329457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39052606711753401015090437 7322363758453762690329457)
                ·
                  refine ⟨5491772818840322017747093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7322363758453762690329457 5491772818840322017747093)
                  ·
                    refine ⟨257426850883140094581895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5491772818840322017747093 257426850883140094581895)
                    ·
                      rfl

theorem cell23_1504011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 6].length) (baseStart_1504011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504011 prefixEnd_1504011 := by exact prefixLift 1504011
  have htrace : WordTrace (prefixWord ++ tailWord_1504011) baseStart_1504011 baseEnd_1504011 := by
    simpa [prefixWord, tailWord_1504011, baseEnd_1504011] using wordTrace_append hprefix tailTrace_1504011
  have hstable : (prefixWord ++ tailWord_1504011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504011).length < 2 ^ (prefixWord ++ tailWord_1504011).sum := by decide
  have hdescent : baseEnd_1504011 < baseStart_1504011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504028 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1504028 : Nat := 118140960795 + 1504028 * 2 ^ 59
def prefixEnd_1504028 : Nat := 4983230072969 + 3 ^ 40 * 1504028 * 2
def baseEnd_1504028 : Nat := 257429760606848905744369

theorem tailTrace_1504028 : CollatzResearch.WordTrace tailWord_1504028 prefixEnd_1504028 257429760606848905744369 := by
  unfold tailWord_1504028
  simp only [CollatzResearch.WordTrace]
  refine ⟨27428203897585449188620369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36570938530113932251493825 27428203897585449188620369)
  ·
    refine ⟨20571152923189086891465277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27428203897585449188620369 20571152923189086891465277)
    ·
      refine ⟨7714182346195907584299479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20571152923189086891465277 7714182346195907584299479)
      ·
        refine ⟨11571273519293861376449219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7714182346195907584299479 11571273519293861376449219)
        ·
          refine ⟨17356910278940792064673829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11571273519293861376449219 17356910278940792064673829)
          ·
            refine ⟨3254420677301398512126343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17356910278940792064673829 3254420677301398512126343)
            ·
              refine ⟨4881631015952097768189515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254420677301398512126343 4881631015952097768189515)
              ·
                refine ⟨7322446523928146652284273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4881631015952097768189515 7322446523928146652284273)
                ·
                  refine ⟨5491834892946109989213205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7322446523928146652284273 5491834892946109989213205)
                  ·
                    refine ⟨257429760606848905744369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5491834892946109989213205 257429760606848905744369)
                    ·
                      rfl

theorem cell23_1504028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1504028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504028 prefixEnd_1504028 := by exact prefixLift 1504028
  have htrace : WordTrace (prefixWord ++ tailWord_1504028) baseStart_1504028 baseEnd_1504028 := by
    simpa [prefixWord, tailWord_1504028, baseEnd_1504028] using wordTrace_append hprefix tailTrace_1504028
  have hstable : (prefixWord ++ tailWord_1504028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504028).length < 2 ^ (prefixWord ++ tailWord_1504028).sum := by decide
  have hdescent : baseEnd_1504028 < baseStart_1504028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504035 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 6, 2, 2]
def baseStart_1504035 : Nat := 118140960795 + 1504035 * 2 ^ 59
def prefixEnd_1504035 : Nat := 4983230072969 + 3 ^ 40 * 1504035 * 2
def baseEnd_1504035 : Nat := 772292876185128189845575

theorem tailTrace_1504035 : CollatzResearch.WordTrace tailWord_1504035 prefixEnd_1504035 772292876185128189845575 := by
  unfold tailWord_1504035
  simp only [CollatzResearch.WordTrace]
  refine ⟨54856663106145538572745559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36571108737430359048497039 54856663106145538572745559)
  ·
    refine ⟨82284994659218307859118339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54856663106145538572745559 82284994659218307859118339)
    ·
      refine ⟨123427491988827461788677509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82284994659218307859118339 123427491988827461788677509)
      ·
        refine ⟨23142654747905149085377033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123427491988827461788677509 23142654747905149085377033)
        ·
          refine ⟨17356991060928861814032775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23142654747905149085377033 17356991060928861814032775)
          ·
            refine ⟨26035486591393292721049163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17356991060928861814032775 26035486591393292721049163)
            ·
              refine ⟨39053229887089939081573745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26035486591393292721049163 39053229887089939081573745)
              ·
                refine ⟨29289922415317454311180309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39053229887089939081573745 29289922415317454311180309)
                ·
                  refine ⟨1372965113218005670836577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29289922415317454311180309 1372965113218005670836577)
                  ·
                    refine ⟨1029723834913504253127433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1372965113218005670836577 1029723834913504253127433)
                    ·
                      refine ⟨772292876185128189845575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029723834913504253127433 772292876185128189845575)
                      ·
                        rfl

theorem cell23_1504035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_1504035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504035 prefixEnd_1504035 := by exact prefixLift 1504035
  have htrace : WordTrace (prefixWord ++ tailWord_1504035) baseStart_1504035 baseEnd_1504035 := by
    simpa [prefixWord, tailWord_1504035, baseEnd_1504035] using wordTrace_append hprefix tailTrace_1504035
  have hstable : (prefixWord ++ tailWord_1504035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504035).length < 2 ^ (prefixWord ++ tailWord_1504035).sum := by decide
  have hdescent : baseEnd_1504035 < baseStart_1504035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504041 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 7]
def baseStart_1504041 : Nat := 118140960795 + 1504041 * 2 ^ 59
def prefixEnd_1504041 : Nat := 4983230072969 + 3 ^ 40 * 1504041 * 2
def baseEnd_1504041 : Nat := 85810661896561685152283

theorem tailTrace_1504041 : CollatzResearch.WordTrace tailWord_1504041 prefixEnd_1504041 85810661896561685152283 := by
  unfold tailWord_1504041
  simp only [CollatzResearch.WordTrace]
  refine ⟨54856881944123801597463977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36571254629415867731642651 54856881944123801597463977)
  ·
    refine ⟨41142661458092851198097983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54856881944123801597463977 41142661458092851198097983)
    ·
      refine ⟨61713992187139276797146975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41142661458092851198097983 61713992187139276797146975)
      ·
        refine ⟨92570988280708915195720463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61713992187139276797146975 92570988280708915195720463)
        ·
          refine ⟨138856482421063372793580695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92570988280708915195720463 138856482421063372793580695)
          ·
            refine ⟨208284723631595059190371043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138856482421063372793580695 208284723631595059190371043)
            ·
              refine ⟨312427085447392588785556565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208284723631595059190371043 312427085447392588785556565)
              ·
                refine ⟨3661254907586631899830741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 312427085447392588785556565 3661254907586631899830741)
                ·
                  refine ⟨85810661896561685152283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3661254907586631899830741 85810661896561685152283)
                  ·
                    rfl

theorem cell23_1504041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 7].length) (baseStart_1504041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504041 prefixEnd_1504041 := by exact prefixLift 1504041
  have htrace : WordTrace (prefixWord ++ tailWord_1504041) baseStart_1504041 baseEnd_1504041 := by
    simpa [prefixWord, tailWord_1504041, baseEnd_1504041] using wordTrace_append hprefix tailTrace_1504041
  have hstable : (prefixWord ++ tailWord_1504041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504041).length < 2 ^ (prefixWord ++ tailWord_1504041).sum := by decide
  have hdescent : baseEnd_1504041 < baseStart_1504041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504108 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_1504108 : Nat := 118140960795 + 1504108 * 2 ^ 59
def prefixEnd_1504108 : Nat := 4983230072969 + 3 ^ 40 * 1504108 * 2
def baseEnd_1504108 : Nat := 772330360272906404232739

theorem tailTrace_1504108 : CollatzResearch.WordTrace tailWord_1504108 prefixEnd_1504108 772330360272906404232739 := by
  unfold tailWord_1504108
  simp only [CollatzResearch.WordTrace]
  refine ⟨27429662817440536020076489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36572883756587381360101985 27429662817440536020076489)
  ·
    refine ⟨20572247113080402015057367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27429662817440536020076489 20572247113080402015057367)
    ·
      refine ⟨30858370669620603022586051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20572247113080402015057367 30858370669620603022586051)
      ·
        refine ⟨46287556004430904533879077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30858370669620603022586051 46287556004430904533879077)
        ·
          refine ⟨8678916750830794600102327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46287556004430904533879077 8678916750830794600102327)
          ·
            refine ⟨13018375126246191900153491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8678916750830794600102327 13018375126246191900153491)
            ·
              refine ⟨19527562689369287850230237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13018375126246191900153491 19527562689369287850230237)
              ·
                refine ⟨7322836008513482943836339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19527562689369287850230237 7322836008513482943836339)
                ·
                  refine ⟨10984254012770224415754509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7322836008513482943836339 10984254012770224415754509)
                  ·
                    refine ⟨4119095254788834155907941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10984254012770224415754509 4119095254788834155907941)
                    ·
                      refine ⟨772330360272906404232739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4119095254788834155907941 772330360272906404232739)
                      ·
                        rfl

theorem cell23_1504108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_1504108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504108 prefixEnd_1504108 := by exact prefixLift 1504108
  have htrace : WordTrace (prefixWord ++ tailWord_1504108) baseStart_1504108 baseEnd_1504108 := by
    simpa [prefixWord, tailWord_1504108, baseEnd_1504108] using wordTrace_append hprefix tailTrace_1504108
  have hstable : (prefixWord ++ tailWord_1504108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504108).length < 2 ^ (prefixWord ++ tailWord_1504108).sum := by decide
  have hdescent : baseEnd_1504108 < baseStart_1504108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504125 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 4, 4, 2]
def baseStart_1504125 : Nat := 118140960795 + 1504125 * 2 ^ 59
def prefixEnd_1504125 : Nat := 4983230072969 + 3 ^ 40 * 1504125 * 2
def baseEnd_1504125 : Nat := 772339089444032837720161

theorem tailTrace_1504125 : CollatzResearch.WordTrace tailWord_1504125 prefixEnd_1504125 772339089444032837720161 := by
  unfold tailWord_1504125
  simp only [CollatzResearch.WordTrace]
  refine ⟨54859945675819483943521829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36573297117212989295681219 54859945675819483943521829)
  ·
    refine ⟨10286239814216153239410343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54859945675819483943521829 10286239814216153239410343)
    ·
      refine ⟨15429359721324229859115515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10286239814216153239410343 15429359721324229859115515)
      ·
        refine ⟨23144039581986344788673273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15429359721324229859115515 23144039581986344788673273)
        ·
          refine ⟨17358029686489758591504955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23144039581986344788673273 17358029686489758591504955)
          ·
            refine ⟨26037044529734637887257433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17358029686489758591504955 26037044529734637887257433)
            ·
              refine ⟨19527783397300978415443075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26037044529734637887257433 19527783397300978415443075)
              ·
                refine ⟨29291675095951467623164613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19527783397300978415443075 29291675095951467623164613)
                ·
                  refine ⟨5492189080490900179343365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29291675095951467623164613 5492189080490900179343365)
                  ·
                    refine ⟨1029785452592043783626881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5492189080490900179343365 1029785452592043783626881)
                    ·
                      refine ⟨772339089444032837720161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029785452592043783626881 772339089444032837720161)
                      ·
                        rfl

theorem cell23_1504125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_1504125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504125 prefixEnd_1504125 := by exact prefixLift 1504125
  have htrace : WordTrace (prefixWord ++ tailWord_1504125) baseStart_1504125 baseEnd_1504125 := by
    simpa [prefixWord, tailWord_1504125, baseEnd_1504125] using wordTrace_append hprefix tailTrace_1504125
  have hstable : (prefixWord ++ tailWord_1504125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504125).length < 2 ^ (prefixWord ++ tailWord_1504125).sum := by decide
  have hdescent : baseEnd_1504125 < baseStart_1504125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504126 : List Nat := [4, 2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_1504126 : Nat := 118140960795 + 1504126 * 2 ^ 59
def prefixEnd_1504126 : Nat := 4983230072969 + 3 ^ 40 * 1504126 * 2
def baseEnd_1504126 : Nat := 85815511436076370423073

theorem tailTrace_1504126 : CollatzResearch.WordTrace tailWord_1504126 prefixEnd_1504126 85815511436076370423073 := by
  unfold tailWord_1504126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6857497768601982639288529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36573321432543907409538821 6857497768601982639288529)
  ·
    refine ⟨5143123326451486979466397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6857497768601982639288529 5143123326451486979466397)
    ·
      refine ⟨1928671247419307617299899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5143123326451486979466397 1928671247419307617299899)
      ·
        refine ⟨2893006871128961425949849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928671247419307617299899 2893006871128961425949849)
        ·
          refine ⟨2169755153346721069462387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2893006871128961425949849 2169755153346721069462387)
          ·
            refine ⟨3254632730020081604193581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169755153346721069462387 3254632730020081604193581)
            ·
              refine ⟨1220487273757530601572593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3254632730020081604193581 1220487273757530601572593)
              ·
                refine ⟨915365455318147951179445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1220487273757530601572593 915365455318147951179445)
                ·
                  refine ⟨85815511436076370423073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 915365455318147951179445 85815511436076370423073)
                  ·
                    rfl

theorem cell23_1504126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_1504126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504126 prefixEnd_1504126 := by exact prefixLift 1504126
  have htrace : WordTrace (prefixWord ++ tailWord_1504126) baseStart_1504126 baseEnd_1504126 := by
    simpa [prefixWord, tailWord_1504126, baseEnd_1504126] using wordTrace_append hprefix tailTrace_1504126
  have hstable : (prefixWord ++ tailWord_1504126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504126).length < 2 ^ (prefixWord ++ tailWord_1504126).sum := by decide
  have hdescent : baseEnd_1504126 < baseStart_1504126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504128 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 3]
def baseStart_1504128 : Nat := 118140960795 + 1504128 * 2 ^ 59
def prefixEnd_1504128 : Nat := 4983230072969 + 3 ^ 40 * 1504128 * 2
def baseEnd_1504128 : Nat := 772340629885996325982647

theorem tailTrace_1504128 : CollatzResearch.WordTrace tailWord_1504128 prefixEnd_1504128 772340629885996325982647 := by
  unfold tailWord_1504128
  simp only [CollatzResearch.WordTrace]
  refine ⟨27430027547404307727940519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36573370063205743637254025 27430027547404307727940519)
  ·
    refine ⟨41145041321106461591910779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27430027547404307727940519 41145041321106461591910779)
    ·
      refine ⟨61717561981659692387866169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41145041321106461591910779 61717561981659692387866169)
      ·
        refine ⟨46288171486244769290899627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61717561981659692387866169 46288171486244769290899627)
        ·
          refine ⟨69432257229367153936349441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46288171486244769290899627 69432257229367153936349441)
          ·
            refine ⟨52074192922025365452262081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69432257229367153936349441 52074192922025365452262081)
            ·
              refine ⟨39055644691519024089196561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52074192922025365452262081 39055644691519024089196561)
              ·
                refine ⟨29291733518639268066897421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39055644691519024089196561 29291733518639268066897421)
                ·
                  refine ⟨10984400069489725525086533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29291733518639268066897421 10984400069489725525086533)
                  ·
                    refine ⟨2059575013029323535953725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10984400069489725525086533 2059575013029323535953725)
                    ·
                      refine ⟨772340629885996325982647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2059575013029323535953725 772340629885996325982647)
                      ·
                        rfl

theorem cell23_1504128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_1504128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504128 prefixEnd_1504128 := by exact prefixLift 1504128
  have htrace : WordTrace (prefixWord ++ tailWord_1504128) baseStart_1504128 baseEnd_1504128 := by
    simpa [prefixWord, tailWord_1504128, baseEnd_1504128] using wordTrace_append hprefix tailTrace_1504128
  have hstable : (prefixWord ++ tailWord_1504128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504128).length < 2 ^ (prefixWord ++ tailWord_1504128).sum := by decide
  have hdescent : baseEnd_1504128 < baseStart_1504128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504162 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1504162 : Nat := 118140960795 + 1504162 * 2 ^ 59
def prefixEnd_1504162 : Nat := 4983230072969 + 3 ^ 40 * 1504162 * 2
def baseEnd_1504162 : Nat := 772358088228249192957491

theorem tailTrace_1504162 : CollatzResearch.WordTrace tailWord_1504162 prefixEnd_1504162 772358088228249192957491 := by
  unfold tailWord_1504162
  simp only [CollatzResearch.WordTrace]
  refine ⟨13715323794171359815654685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36574196784456959508412493 13715323794171359815654685)
  ·
    refine ⟨5143246422814259930870507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13715323794171359815654685 5143246422814259930870507)
    ·
      refine ⟨7714869634221389896305761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5143246422814259930870507 7714869634221389896305761)
      ·
        refine ⟨5786152225666042422229321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7714869634221389896305761 5786152225666042422229321)
        ·
          refine ⟨4339614169249531816671991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5786152225666042422229321 4339614169249531816671991)
          ·
            refine ⟨6509421253874297725007987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339614169249531816671991 6509421253874297725007987)
            ·
              refine ⟨9764131880811446587511981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6509421253874297725007987 9764131880811446587511981)
              ·
                refine ⟨3661549455304292470316993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9764131880811446587511981 3661549455304292470316993)
                ·
                  refine ⟨2746162091478219352737745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3661549455304292470316993 2746162091478219352737745)
                  ·
                    refine ⟨2059621568608664514553309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2746162091478219352737745 2059621568608664514553309)
                    ·
                      refine ⟨772358088228249192957491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2059621568608664514553309 772358088228249192957491)
                      ·
                        rfl

theorem cell23_1504162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1504162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504162 prefixEnd_1504162 := by exact prefixLift 1504162
  have htrace : WordTrace (prefixWord ++ tailWord_1504162) baseStart_1504162 baseEnd_1504162 := by
    simpa [prefixWord, tailWord_1504162, baseEnd_1504162] using wordTrace_append hprefix tailTrace_1504162
  have hstable : (prefixWord ++ tailWord_1504162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504162).length < 2 ^ (prefixWord ++ tailWord_1504162).sum := by decide
  have hdescent : baseEnd_1504162 < baseStart_1504162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504175 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 7, 1, 3]
def baseStart_1504175 : Nat := 118140960795 + 1504175 * 2 ^ 59
def prefixEnd_1504175 : Nat := 4983230072969 + 3 ^ 40 * 1504175 * 2
def baseEnd_1504175 : Nat := 772364763476757642094931

theorem tailTrace_1504175 : CollatzResearch.WordTrace tailWord_1504175 prefixEnd_1504175 772364763476757642094931 := by
  unfold tailWord_1504175
  simp only [CollatzResearch.WordTrace]
  refine ⟨54861769325638342482841979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36574512883758894988561319 54861769325638342482841979)
  ·
    refine ⟨82292653988457513724262969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54861769325638342482841979 82292653988457513724262969)
    ·
      refine ⟨61719490491343135293197227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82292653988457513724262969 61719490491343135293197227)
      ·
        refine ⟨92579235737014702939795841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61719490491343135293197227 92579235737014702939795841)
        ·
          refine ⟨69434426802761027204846881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92579235737014702939795841 69434426802761027204846881)
          ·
            refine ⟨52075820102070770403635161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69434426802761027204846881 52075820102070770403635161)
            ·
              refine ⟨39056865076553077802726371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52075820102070770403635161 39056865076553077802726371)
              ·
                refine ⟨58585297614829616704089557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39056865076553077802726371 58585297614829616704089557)
                ·
                  refine ⟨1373092912847569141502099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 58585297614829616704089557 1373092912847569141502099)
                  ·
                    refine ⟨2059639369271353712253149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1373092912847569141502099 2059639369271353712253149)
                    ·
                      refine ⟨772364763476757642094931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2059639369271353712253149 772364763476757642094931)
                      ·
                        rfl

theorem cell23_1504175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 1, 3].length) (baseStart_1504175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504175 prefixEnd_1504175 := by exact prefixLift 1504175
  have htrace : WordTrace (prefixWord ++ tailWord_1504175) baseStart_1504175 baseEnd_1504175 := by
    simpa [prefixWord, tailWord_1504175, baseEnd_1504175] using wordTrace_append hprefix tailTrace_1504175
  have hstable : (prefixWord ++ tailWord_1504175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504175).length < 2 ^ (prefixWord ++ tailWord_1504175).sum := by decide
  have hdescent : baseEnd_1504175 < baseStart_1504175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504215 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 1, 8, 2]
def baseStart_1504215 : Nat := 118140960795 + 1504215 * 2 ^ 59
def prefixEnd_1504215 : Nat := 4983230072969 + 3 ^ 40 * 1504215 * 2
def baseEnd_1504215 : Nat := 772385302702937485594747

theorem tailTrace_1504215 : CollatzResearch.WordTrace tailWord_1504215 prefixEnd_1504215 772385302702937485594747 := by
  unfold tailWord_1504215
  simp only [CollatzResearch.WordTrace]
  refine ⟨54863228245493429314298099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36575485496995619542865399 54863228245493429314298099)
  ·
    refine ⟨82294842368240143971447149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54863228245493429314298099 82294842368240143971447149)
    ·
      refine ⟨30860565888090053989292681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82294842368240143971447149 30860565888090053989292681)
      ·
        refine ⟨23145424416067540491969511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30860565888090053989292681 23145424416067540491969511)
        ·
          refine ⟨34718136624101310737954267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23145424416067540491969511 34718136624101310737954267)
          ·
            refine ⟨52077204936151966106931401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34718136624101310737954267 52077204936151966106931401)
            ·
              refine ⟨39057903702113974580198551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52077204936151966106931401 39057903702113974580198551)
              ·
                refine ⟨58586855553170961870297827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39057903702113974580198551 58586855553170961870297827)
                ·
                  refine ⟨87880283329756442805446741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58586855553170961870297827 87880283329756442805446741)
                  ·
                    refine ⟨1029847070270583314126329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87880283329756442805446741 1029847070270583314126329)
                    ·
                      refine ⟨772385302702937485594747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029847070270583314126329 772385302702937485594747)
                      ·
                        rfl

theorem cell23_1504215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_1504215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504215 prefixEnd_1504215 := by exact prefixLift 1504215
  have htrace : WordTrace (prefixWord ++ tailWord_1504215) baseStart_1504215 baseEnd_1504215 := by
    simpa [prefixWord, tailWord_1504215, baseEnd_1504215] using wordTrace_append hprefix tailTrace_1504215
  have hstable : (prefixWord ++ tailWord_1504215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504215).length < 2 ^ (prefixWord ++ tailWord_1504215).sum := by decide
  have hdescent : baseEnd_1504215 < baseStart_1504215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504225 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 4, 4]
def baseStart_1504225 : Nat := 118140960795 + 1504225 * 2 ^ 59
def prefixEnd_1504225 : Nat := 4983230072969 + 3 ^ 40 * 1504225 * 2
def baseEnd_1504225 : Nat := 257463479169827482156567

theorem tailTrace_1504225 : CollatzResearch.WordTrace tailWord_1504225 prefixEnd_1504225 257463479169827482156567 := by
  unfold tailWord_1504225
  simp only [CollatzResearch.WordTrace]
  refine ⟨54863592975457201022162129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36575728650304800681441419 54863592975457201022162129)
  ·
    refine ⟨41147694731592900766621597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54863592975457201022162129 41147694731592900766621597)
    ·
      refine ⟨15430385524347337787483099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41147694731592900766621597 15430385524347337787483099)
      ·
        refine ⟨23145578286521006681224649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15430385524347337787483099 23145578286521006681224649)
        ·
          refine ⟨17359183714890755010918487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23145578286521006681224649 17359183714890755010918487)
          ·
            refine ⟨26038775572336132516377731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17359183714890755010918487 26038775572336132516377731)
            ·
              refine ⟨39058163358504198774566597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26038775572336132516377731 39058163358504198774566597)
              ·
                refine ⟨7323405629719537270231237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39058163358504198774566597 7323405629719537270231237)
                ·
                  refine ⟨1373138555572413238168357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7323405629719537270231237 1373138555572413238168357)
                  ·
                    refine ⟨257463479169827482156567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1373138555572413238168357 257463479169827482156567)
                    ·
                      rfl

theorem cell23_1504225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_1504225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504225 prefixEnd_1504225 := by exact prefixLift 1504225
  have htrace : WordTrace (prefixWord ++ tailWord_1504225) baseStart_1504225 baseEnd_1504225 := by
    simpa [prefixWord, tailWord_1504225, baseEnd_1504225] using wordTrace_append hprefix tailTrace_1504225
  have hstable : (prefixWord ++ tailWord_1504225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504225).length < 2 ^ (prefixWord ++ tailWord_1504225).sum := by decide
  have hdescent : baseEnd_1504225 < baseStart_1504225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504229 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 1, 5]
def baseStart_1504229 : Nat := 118140960795 + 1504229 * 2 ^ 59
def prefixEnd_1504229 : Nat := 4983230072969 + 3 ^ 40 * 1504229 * 2
def baseEnd_1504229 : Nat := 257464163810700143606561

theorem tailTrace_1504229 : CollatzResearch.WordTrace tailWord_1504229 prefixEnd_1504229 257464163810700143606561 := by
  unfold tailWord_1504229
  simp only [CollatzResearch.WordTrace]
  refine ⟨54863738867442709705307741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36575825911628473136871827 54863738867442709705307741)
  ·
    refine ⟨20573902075291016139490403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54863738867442709705307741 20573902075291016139490403)
    ·
      refine ⟨30860853112936524209235605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20573902075291016139490403 30860853112936524209235605)
      ·
        refine ⟨1446602489668899572307919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30860853112936524209235605 1446602489668899572307919)
        ·
          refine ⟨2169903734503349358461879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446602489668899572307919 2169903734503349358461879)
          ·
            refine ⟨3254855601755024037692819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169903734503349358461879 3254855601755024037692819)
            ·
              refine ⟨4882283402632536056539229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3254855601755024037692819 4882283402632536056539229)
              ·
                refine ⟨1830856275987201021202211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4882283402632536056539229 1830856275987201021202211)
                ·
                  refine ⟨2746284413980801531803317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830856275987201021202211 2746284413980801531803317)
                  ·
                    refine ⟨257464163810700143606561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2746284413980801531803317 257464163810700143606561)
                    ·
                      rfl

theorem cell23_1504229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_1504229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504229 prefixEnd_1504229 := by exact prefixLift 1504229
  have htrace : WordTrace (prefixWord ++ tailWord_1504229) baseStart_1504229 baseEnd_1504229 := by
    simpa [prefixWord, tailWord_1504229, baseEnd_1504229] using wordTrace_append hprefix tailTrace_1504229
  have hstable : (prefixWord ++ tailWord_1504229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504229).length < 2 ^ (prefixWord ++ tailWord_1504229).sum := by decide
  have hdescent : baseEnd_1504229 < baseStart_1504229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504248 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_1504248 : Nat := 118140960795 + 1504248 * 2 ^ 59
def prefixEnd_1504248 : Nat := 4983230072969 + 3 ^ 40 * 1504248 * 2
def baseEnd_1504248 : Nat := 772402247564535856482095

theorem tailTrace_1504248 : CollatzResearch.WordTrace tailWord_1504248 prefixEnd_1504248 772402247564535856482095 := by
  unfold tailWord_1504248
  simp only [CollatzResearch.WordTrace]
  refine ⟨27432215927186937975124699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36576287902915917300166265 27432215927186937975124699)
  ·
    refine ⟨41148323890780406962687049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27432215927186937975124699 41148323890780406962687049)
    ·
      refine ⟨30861242918085305222015287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41148323890780406962687049 30861242918085305222015287)
      ·
        refine ⟨46291864377127957833022931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30861242918085305222015287 46291864377127957833022931)
        ·
          refine ⟨69437796565691936749534397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46291864377127957833022931 69437796565691936749534397)
          ·
            refine ⟨26039173712134476281075399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69437796565691936749534397 26039173712134476281075399)
            ·
              refine ⟨39058760568201714421613099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26039173712134476281075399 39058760568201714421613099)
              ·
                refine ⟨58588140852302571632419649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39058760568201714421613099 58588140852302571632419649)
                ·
                  refine ⟨43941105639226928724314737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58588140852302571632419649 43941105639226928724314737)
                  ·
                    refine ⟨32955829229420196543236053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43941105639226928724314737 32955829229420196543236053)
                    ·
                      refine ⟨772402247564535856482095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32955829229420196543236053 772402247564535856482095)
                      ·
                        rfl

theorem cell23_1504248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_1504248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504248 prefixEnd_1504248 := by exact prefixLift 1504248
  have htrace : WordTrace (prefixWord ++ tailWord_1504248) baseStart_1504248 baseEnd_1504248 := by
    simpa [prefixWord, tailWord_1504248, baseEnd_1504248] using wordTrace_append hprefix tailTrace_1504248
  have hstable : (prefixWord ++ tailWord_1504248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504248).length < 2 ^ (prefixWord ++ tailWord_1504248).sum := by decide
  have hdescent : baseEnd_1504248 < baseStart_1504248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504249 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 3, 2, 2]
def baseStart_1504249 : Nat := 118140960795 + 1504249 * 2 ^ 59
def prefixEnd_1504249 : Nat := 4983230072969 + 3 ^ 40 * 1504249 * 2
def baseEnd_1504249 : Nat := 772402761045190352569591

theorem tailTrace_1504249 : CollatzResearch.WordTrace tailWord_1504249 prefixEnd_1504249 772402761045190352569591 := by
  unfold tailWord_1504249
  simp only [CollatzResearch.WordTrace]
  refine ⟨54864468327370253121035801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36576312218246835414023867 54864468327370253121035801)
  ·
    refine ⟨41148351245527689840776851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54864468327370253121035801 41148351245527689840776851)
    ·
      refine ⟨61722526868291534761165277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41148351245527689840776851 61722526868291534761165277)
      ·
        refine ⟨23145947575609325535436979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61722526868291534761165277 23145947575609325535436979)
        ·
          refine ⟨34718921363413988303155469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23145947575609325535436979 34718921363413988303155469)
          ·
            refine ⟨13019595511280245613683301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34718921363413988303155469 13019595511280245613683301)
            ·
              refine ⟨2441174158365046052565619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13019595511280245613683301 2441174158365046052565619)
              ·
                refine ⟨3661761237547569078848429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441174158365046052565619 3661761237547569078848429)
                ·
                  refine ⟨1373160464080338404568161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3661761237547569078848429 1373160464080338404568161)
                  ·
                    refine ⟨1029870348060253803426121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1373160464080338404568161 1029870348060253803426121)
                    ·
                      refine ⟨772402761045190352569591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029870348060253803426121 772402761045190352569591)
                      ·
                        rfl

theorem cell23_1504249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_1504249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504249 prefixEnd_1504249 := by exact prefixLift 1504249
  have htrace : WordTrace (prefixWord ++ tailWord_1504249) baseStart_1504249 baseEnd_1504249 := by
    simpa [prefixWord, tailWord_1504249, baseEnd_1504249] using wordTrace_append hprefix tailTrace_1504249
  have hstable : (prefixWord ++ tailWord_1504249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504249).length < 2 ^ (prefixWord ++ tailWord_1504249).sum := by decide
  have hdescent : baseEnd_1504249 < baseStart_1504249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504282 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3]
def baseStart_1504282 : Nat := 118140960795 + 1504282 * 2 ^ 59
def prefixEnd_1504282 : Nat := 4983230072969 + 3 ^ 40 * 1504282 * 2
def baseEnd_1504282 : Nat := 772419705906788723456939

theorem tailTrace_1504282 : CollatzResearch.WordTrace tailWord_1504282 prefixEnd_1504282 772419705906788723456939 := by
  unfold tailWord_1504282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716417984062674939246775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36577114624167133171324733 13716417984062674939246775)
  ·
    refine ⟨20574626976094012408870163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13716417984062674939246775 20574626976094012408870163)
    ·
      refine ⟨30861940464141018613305245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20574626976094012408870163 30861940464141018613305245)
      ·
        refine ⟨11573227674052881979989467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30861940464141018613305245 11573227674052881979989467)
        ·
          refine ⟨17359841511079322969984201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11573227674052881979989467 17359841511079322969984201)
          ·
            refine ⟨13019881133309492227488151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17359841511079322969984201 13019881133309492227488151)
            ·
              refine ⟨19529821699964238341232227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13019881133309492227488151 19529821699964238341232227)
              ·
                refine ⟨29294732549946357511848341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19529821699964238341232227 29294732549946357511848341)
                ·
                  refine ⟨1373190588278735508367891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29294732549946357511848341 1373190588278735508367891)
                  ·
                    refine ⟨2059785882418103262551837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1373190588278735508367891 2059785882418103262551837)
                    ·
                      refine ⟨772419705906788723456939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2059785882418103262551837 772419705906788723456939)
                      ·
                        rfl

theorem cell23_1504282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_1504282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504282 prefixEnd_1504282 := by exact prefixLift 1504282
  have htrace : WordTrace (prefixWord ++ tailWord_1504282) baseStart_1504282 baseEnd_1504282 := by
    simpa [prefixWord, tailWord_1504282, baseEnd_1504282] using wordTrace_append hprefix tailTrace_1504282
  have hstable : (prefixWord ++ tailWord_1504282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504282).length < 2 ^ (prefixWord ++ tailWord_1504282).sum := by decide
  have hdescent : baseEnd_1504282 < baseStart_1504282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504305 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1504305 : Nat := 118140960795 + 1504305 * 2 ^ 59
def prefixEnd_1504305 : Nat := 4983230072969 + 3 ^ 40 * 1504305 * 2
def baseEnd_1504305 : Nat := 772431515961842133469333

theorem tailTrace_1504305 : CollatzResearch.WordTrace tailWord_1504305 prefixEnd_1504305 772431515961842133469333 := by
  unfold tailWord_1504305
  simp only [CollatzResearch.WordTrace]
  refine ⟨54866510815167374685074369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36577673876778249790049579 54866510815167374685074369)
  ·
    refine ⟨41149883111375531013805777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54866510815167374685074369 41149883111375531013805777)
    ·
      refine ⟨30862412333531648260354333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41149883111375531013805777 30862412333531648260354333)
      ·
        refine ⟨11573404625074368097632875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30862412333531648260354333 11573404625074368097632875)
        ·
          refine ⟨17360106937611552146449313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11573404625074368097632875 17360106937611552146449313)
          ·
            refine ⟨13020080203208664109836985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17360106937611552146449313 13020080203208664109836985)
            ·
              refine ⟨9765060152406498082377739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13020080203208664109836985 9765060152406498082377739)
              ·
                refine ⟨14647590228609747123566609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9765060152406498082377739 14647590228609747123566609)
                ·
                  refine ⟨10985692671457310342674957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14647590228609747123566609 10985692671457310342674957)
                  ·
                    refine ⟨4119634751796491378503109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10985692671457310342674957 4119634751796491378503109)
                    ·
                      refine ⟨772431515961842133469333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4119634751796491378503109 772431515961842133469333)
                      ·
                        rfl

theorem cell23_1504305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1504305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504305 prefixEnd_1504305 := by exact prefixLift 1504305
  have htrace : WordTrace (prefixWord ++ tailWord_1504305) baseStart_1504305 baseEnd_1504305 := by
    simpa [prefixWord, tailWord_1504305, baseEnd_1504305] using wordTrace_append hprefix tailTrace_1504305
  have hstable : (prefixWord ++ tailWord_1504305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504305).length < 2 ^ (prefixWord ++ tailWord_1504305).sum := by decide
  have hdescent : baseEnd_1504305 < baseStart_1504305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504316 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 2, 1, 3]
def baseStart_1504316 : Nat := 118140960795 + 1504316 * 2 ^ 59
def prefixEnd_1504316 : Nat := 4983230072969 + 3 ^ 40 * 1504316 * 2
def baseEnd_1504316 : Nat := 772437164249041590431783

theorem tailTrace_1504316 : CollatzResearch.WordTrace tailWord_1504316 prefixEnd_1504316 772437164249041590431783 := by
  unfold tailWord_1504316
  simp only [CollatzResearch.WordTrace]
  refine ⟨27433456009063761781862401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36577941345418349042483201 27433456009063761781862401)
  ·
    refine ⟨20575092006797821336396801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27433456009063761781862401 20575092006797821336396801)
    ·
      refine ⟨15431319005098366002297601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20575092006797821336396801 15431319005098366002297601)
      ·
        refine ⟨11573489253823774501723201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15431319005098366002297601 11573489253823774501723201)
        ·
          refine ⟨8680116940367830876292401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11573489253823774501723201 8680116940367830876292401)
          ·
            refine ⟨6510087705275873157219301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8680116940367830876292401 6510087705275873157219301)
            ·
              refine ⟨1220641444739226216978619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6510087705275873157219301 1220641444739226216978619)
              ·
                refine ⟨1830962167108839325467929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220641444739226216978619 1830962167108839325467929)
                ·
                  refine ⟨1373221625331629494100947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1830962167108839325467929 1373221625331629494100947)
                  ·
                    refine ⟨2059832437997444241151421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1373221625331629494100947 2059832437997444241151421)
                    ·
                      refine ⟨772437164249041590431783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2059832437997444241151421 772437164249041590431783)
                      ·
                        rfl

theorem cell23_1504316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_1504316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504316 prefixEnd_1504316 := by exact prefixLift 1504316
  have htrace : WordTrace (prefixWord ++ tailWord_1504316) baseStart_1504316 baseEnd_1504316 := by
    simpa [prefixWord, tailWord_1504316, baseEnd_1504316] using wordTrace_append hprefix tailTrace_1504316
  have hstable : (prefixWord ++ tailWord_1504316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504316).length < 2 ^ (prefixWord ++ tailWord_1504316).sum := by decide
  have hdescent : baseEnd_1504316 < baseStart_1504316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504325 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_1504325 : Nat := 118140960795 + 1504325 * 2 ^ 59
def prefixEnd_1504325 : Nat := 4983230072969 + 3 ^ 40 * 1504325 * 2
def baseEnd_1504325 : Nat := 772441785574932055219241

theorem tailTrace_1504325 : CollatzResearch.WordTrace tailWord_1504325 prefixEnd_1504325 772441785574932055219241 := by
  unfold tailWord_1504325
  simp only [CollatzResearch.WordTrace]
  refine ⟨54867240275094918100802429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36578160183396612067201619 54867240275094918100802429)
  ·
    refine ⟨20575215103160594287800911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54867240275094918100802429 20575215103160594287800911)
    ·
      refine ⟨30862822654740891431701367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20575215103160594287800911 30862822654740891431701367)
      ·
        refine ⟨46294233982111337147552051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30862822654740891431701367 46294233982111337147552051)
        ·
          refine ⟨69441350973167005721328077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46294233982111337147552051 69441350973167005721328077)
          ·
            refine ⟨26040506614937627145498029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69441350973167005721328077 26040506614937627145498029)
            ·
              refine ⟨9765189980601610179561761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26040506614937627145498029 9765189980601610179561761)
              ·
                refine ⟨7323892485451207634671321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9765189980601610179561761 7323892485451207634671321)
                ·
                  refine ⟨5492919364088405726003491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7323892485451207634671321 5492919364088405726003491)
                  ·
                    refine ⟨8239379046132608589005237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5492919364088405726003491 8239379046132608589005237)
                    ·
                      refine ⟨772441785574932055219241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8239379046132608589005237 772441785574932055219241)
                      ·
                        rfl

theorem cell23_1504325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_1504325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504325 prefixEnd_1504325 := by exact prefixLift 1504325
  have htrace : WordTrace (prefixWord ++ tailWord_1504325) baseStart_1504325 baseEnd_1504325 := by
    simpa [prefixWord, tailWord_1504325, baseEnd_1504325] using wordTrace_append hprefix tailTrace_1504325
  have hstable : (prefixWord ++ tailWord_1504325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504325).length < 2 ^ (prefixWord ++ tailWord_1504325).sum := by decide
  have hdescent : baseEnd_1504325 < baseStart_1504325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504350 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1504350 : Nat := 118140960795 + 1504350 * 2 ^ 59
def prefixEnd_1504350 : Nat := 4983230072969 + 3 ^ 40 * 1504350 * 2
def baseEnd_1504350 : Nat := 772454622591294457406627

theorem tailTrace_1504350 : CollatzResearch.WordTrace tailWord_1504350 prefixEnd_1504350 772454622591294457406627 := by
  unfold tailWord_1504350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6858519012500543421307813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36578768066669564913641669 6858519012500543421307813)
  ·
    refine ⟨1285972314843851891495215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6858519012500543421307813 1285972314843851891495215)
    ·
      refine ⟨1928958472265777837242823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1285972314843851891495215 1928958472265777837242823)
      ·
        refine ⟨2893437708398666755864235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928958472265777837242823 2893437708398666755864235)
        ·
          refine ⟨4340156562598000133796353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2893437708398666755864235 4340156562598000133796353)
          ·
            refine ⟨3255117421948500100347265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4340156562598000133796353 3255117421948500100347265)
            ·
              refine ⟨2441338066461375075260449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3255117421948500100347265 2441338066461375075260449)
              ·
                refine ⟨1831003549846031306445337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441338066461375075260449 1831003549846031306445337)
                ·
                  refine ⟨1373252662384523479834003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1831003549846031306445337 1373252662384523479834003)
                  ·
                    refine ⟨2059878993576785219751005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1373252662384523479834003 2059878993576785219751005)
                    ·
                      refine ⟨772454622591294457406627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2059878993576785219751005 772454622591294457406627)
                      ·
                        rfl

theorem cell23_1504350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1504350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504350 prefixEnd_1504350 := by exact prefixLift 1504350
  have htrace : WordTrace (prefixWord ++ tailWord_1504350) baseStart_1504350 baseEnd_1504350 := by
    simpa [prefixWord, tailWord_1504350, baseEnd_1504350] using wordTrace_append hprefix tailTrace_1504350
  have hstable : (prefixWord ++ tailWord_1504350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504350).length < 2 ^ (prefixWord ++ tailWord_1504350).sum := by decide
  have hdescent : baseEnd_1504350 < baseStart_1504350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504373 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1504373 : Nat := 118140960795 + 1504373 * 2 ^ 59
def prefixEnd_1504373 : Nat := 4983230072969 + 3 ^ 40 * 1504373 * 2
def baseEnd_1504373 : Nat := 772466432646347867419021

theorem tailTrace_1504373 : CollatzResearch.WordTrace tailWord_1504373 prefixEnd_1504373 772466432646347867419021 := by
  unfold tailWord_1504373
  simp only [CollatzResearch.WordTrace]
  refine ⟨54868990978921022298549773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36579327319280681532366515 54868990978921022298549773)
  ·
    refine ⟨20575871617095383361956165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54868990978921022298549773 20575871617095383361956165)
    ·
      refine ⟨3857975928205384380366781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20575871617095383361956165 3857975928205384380366781)
      ·
        refine ⟨1446740973077019142637543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3857975928205384380366781 1446740973077019142637543)
        ·
          refine ⟨2170111459615528713956315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446740973077019142637543 2170111459615528713956315)
          ·
            refine ⟨3255167189423293070934473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170111459615528713956315 3255167189423293070934473)
            ·
              refine ⟨2441375392067469803200855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3255167189423293070934473 2441375392067469803200855)
              ·
                refine ⟨3662063088101204704801283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441375392067469803200855 3662063088101204704801283)
                ·
                  refine ⟨5493094632151807057201925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662063088101204704801283 5493094632151807057201925)
                  ·
                    refine ⟨1029955243528463823225361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5493094632151807057201925 1029955243528463823225361)
                    ·
                      refine ⟨772466432646347867419021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1029955243528463823225361 772466432646347867419021)
                      ·
                        rfl

theorem cell23_1504373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1504373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504373 prefixEnd_1504373 := by exact prefixLift 1504373
  have htrace : WordTrace (prefixWord ++ tailWord_1504373) baseStart_1504373 baseEnd_1504373 := by
    simpa [prefixWord, tailWord_1504373, baseEnd_1504373] using wordTrace_append hprefix tailTrace_1504373
  have hstable : (prefixWord ++ tailWord_1504373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504373).length < 2 ^ (prefixWord ++ tailWord_1504373).sum := by decide
  have hdescent : baseEnd_1504373 < baseStart_1504373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504375 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 1, 7]
def baseStart_1504375 : Nat := 118140960795 + 1504375 * 2 ^ 59
def prefixEnd_1504375 : Nat := 4983230072969 + 3 ^ 40 * 1504375 * 2
def baseEnd_1504375 : Nat := 257489153202552286531337

theorem tailTrace_1504375 : CollatzResearch.WordTrace tailWord_1504375 prefixEnd_1504375 257489153202552286531337 := by
  unfold tailWord_1504375
  simp only [CollatzResearch.WordTrace]
  refine ⟨54869063924913776640122579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36579375949942517760081719 54869063924913776640122579)
  ·
    refine ⟨82303595887370664960183869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54869063924913776640122579 82303595887370664960183869)
    ·
      refine ⟨30863848457763999360068951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82303595887370664960183869 30863848457763999360068951)
      ·
        refine ⟨46295772686645999040103427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30863848457763999360068951 46295772686645999040103427)
        ·
          refine ⟨69443659029968998560155141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46295772686645999040103427 69443659029968998560155141)
          ·
            refine ⟨13020686068119187230029089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69443659029968998560155141 13020686068119187230029089)
            ·
              refine ⟨9765514551089390422521817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13020686068119187230029089 9765514551089390422521817)
              ·
                refine ⟨7324135913317042816891363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9765514551089390422521817 7324135913317042816891363)
                ·
                  refine ⟨10986203869975564225337045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7324135913317042816891363 10986203869975564225337045)
                  ·
                    refine ⟨257489153202552286531337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10986203869975564225337045 257489153202552286531337)
                    ·
                      rfl

theorem cell23_1504375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_1504375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504375 prefixEnd_1504375 := by exact prefixLift 1504375
  have htrace : WordTrace (prefixWord ++ tailWord_1504375) baseStart_1504375 baseEnd_1504375 := by
    simpa [prefixWord, tailWord_1504375, baseEnd_1504375] using wordTrace_append hprefix tailTrace_1504375
  have hstable : (prefixWord ++ tailWord_1504375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504375).length < 2 ^ (prefixWord ++ tailWord_1504375).sum := by decide
  have hdescent : baseEnd_1504375 < baseStart_1504375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504432 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 3]
def baseStart_1504432 : Nat := 118140960795 + 1504432 * 2 ^ 59
def prefixEnd_1504432 : Nat := 4983230072969 + 3 ^ 40 * 1504432 * 2
def baseEnd_1504432 : Nat := 772496728004963136581249

theorem tailTrace_1504432 : CollatzResearch.WordTrace tailWord_1504432 prefixEnd_1504432 772496728004963136581249 := by
  unfold tailWord_1504432
  simp only [CollatzResearch.WordTrace]
  refine ⟨27435571442853637687473775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36580761923804850249965033 27435571442853637687473775)
  ·
    refine ⟨41153357164280456531210663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27435571442853637687473775 41153357164280456531210663)
    ·
      refine ⟨61730035746420684796815995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41153357164280456531210663 61730035746420684796815995)
      ·
        refine ⟨92595053619631027195223993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61730035746420684796815995 92595053619631027195223993)
        ·
          refine ⟨69446290214723270396417995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92595053619631027195223993 69446290214723270396417995)
          ·
            refine ⟨104169435322084905594626993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69446290214723270396417995 104169435322084905594626993)
            ·
              refine ⟨78127076491563679195970245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104169435322084905594626993 78127076491563679195970245)
              ·
                refine ⟨14648826842168189849244421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78127076491563679195970245 14648826842168189849244421)
                ·
                  refine ⟨2746655032906535596733329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14648826842168189849244421 2746655032906535596733329)
                  ·
                    refine ⟨2059991274679901697549997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2746655032906535596733329 2059991274679901697549997)
                    ·
                      refine ⟨772496728004963136581249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2059991274679901697549997 772496728004963136581249)
                      ·
                        rfl

theorem cell23_1504432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 3].length) (baseStart_1504432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504432 prefixEnd_1504432 := by exact prefixLift 1504432
  have htrace : WordTrace (prefixWord ++ tailWord_1504432) baseStart_1504432 baseEnd_1504432 := by
    simpa [prefixWord, tailWord_1504432, baseEnd_1504432] using wordTrace_append hprefix tailTrace_1504432
  have hstable : (prefixWord ++ tailWord_1504432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504432).length < 2 ^ (prefixWord ++ tailWord_1504432).sum := by decide
  have hdescent : baseEnd_1504432 < baseStart_1504432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504456 : List Nat := [2, 1, 3, 1, 2, 1, 5, 3, 1, 4]
def baseStart_1504456 : Nat := 118140960795 + 1504456 * 2 ^ 59
def prefixEnd_1504456 : Nat := 4983230072969 + 3 ^ 40 * 1504456 * 2
def baseEnd_1504456 : Nat := 257503017180223680893713

theorem tailTrace_1504456 : CollatzResearch.WordTrace tailWord_1504456 prefixEnd_1504456 257503017180223680893713 := by
  unfold tailWord_1504456
  simp only [CollatzResearch.WordTrace]
  refine ⟨27436009118810163736910611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36581345491746884982547481 27436009118810163736910611)
  ·
    refine ⟨41154013678215245605365917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27436009118810163736910611 41154013678215245605365917)
    ·
      refine ⟨15432755129330717102012219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41154013678215245605365917 15432755129330717102012219)
      ·
        refine ⟨23149132693996075653018329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15432755129330717102012219 23149132693996075653018329)
        ·
          refine ⟨17361849520497056739763747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23149132693996075653018329 17361849520497056739763747)
          ·
            refine ⟨26042774280745585109645621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17361849520497056739763747 26042774280745585109645621)
            ·
              refine ⟨2441510088819898604029277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26042774280745585109645621 2441510088819898604029277)
              ·
                refine ⟨915566283307461976510979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2441510088819898604029277 915566283307461976510979)
                ·
                  refine ⟨1373349424961192964766469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915566283307461976510979 1373349424961192964766469)
                  ·
                    refine ⟨257503017180223680893713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1373349424961192964766469 257503017180223680893713)
                    ·
                      rfl

theorem cell23_1504456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_1504456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504456 prefixEnd_1504456 := by exact prefixLift 1504456
  have htrace : WordTrace (prefixWord ++ tailWord_1504456) baseStart_1504456 baseEnd_1504456 := by
    simpa [prefixWord, tailWord_1504456, baseEnd_1504456] using wordTrace_append hprefix tailTrace_1504456
  have hstable : (prefixWord ++ tailWord_1504456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504456).length < 2 ^ (prefixWord ++ tailWord_1504456).sum := by decide
  have hdescent : baseEnd_1504456 < baseStart_1504456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504499 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 1, 5]
def baseStart_1504499 : Nat := 118140960795 + 1504499 * 2 ^ 59
def prefixEnd_1504499 : Nat := 4983230072969 + 3 ^ 40 * 1504499 * 2
def baseEnd_1504499 : Nat := 257510377069604791481147

theorem tailTrace_1504499 : CollatzResearch.WordTrace tailWord_1504499 prefixEnd_1504499 257510377069604791481147 := by
  unfold tailWord_1504499
  simp only [CollatzResearch.WordTrace]
  refine ⟨54873586576464545817636551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36582391050976363878424367 54873586576464545817636551)
  ·
    refine ⟨82310379864696818726454827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54873586576464545817636551 82310379864696818726454827)
    ·
      refine ⟨123465569797045228089682241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82310379864696818726454827 123465569797045228089682241)
      ·
        refine ⟨92599177347783921067261681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123465569797045228089682241 92599177347783921067261681)
        ·
          refine ⟨69449383010837940800446261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92599177347783921067261681 69449383010837940800446261)
          ·
            refine ⟨6510879657266056950041837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69449383010837940800446261 6510879657266056950041837)
            ·
              refine ⟨2441579871474771356265689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6510879657266056950041837 2441579871474771356265689)
              ·
                refine ⟨1831184903606078517199267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441579871474771356265689 1831184903606078517199267)
                ·
                  refine ⟨2746777355409117775798901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831184903606078517199267 2746777355409117775798901)
                  ·
                    refine ⟨257510377069604791481147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2746777355409117775798901 257510377069604791481147)
                    ·
                      rfl

theorem cell23_1504499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 5].length) (baseStart_1504499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504499 prefixEnd_1504499 := by exact prefixLift 1504499
  have htrace : WordTrace (prefixWord ++ tailWord_1504499) baseStart_1504499 baseEnd_1504499 := by
    simpa [prefixWord, tailWord_1504499, baseEnd_1504499] using wordTrace_append hprefix tailTrace_1504499
  have hstable : (prefixWord ++ tailWord_1504499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504499).length < 2 ^ (prefixWord ++ tailWord_1504499).sum := by decide
  have hdescent : baseEnd_1504499 < baseStart_1504499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504506 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2]
def baseStart_1504506 : Nat := 118140960795 + 1504506 * 2 ^ 59
def prefixEnd_1504506 : Nat := 4983230072969 + 3 ^ 40 * 1504506 * 2
def baseEnd_1504506 : Nat := 772534725573395847055909

theorem tailTrace_1504506 : CollatzResearch.WordTrace tailWord_1504506 prefixEnd_1504506 772534725573395847055909 := by
  unfold tailWord_1504506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13718460471859796503285343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36582561258292790675427581 13718460471859796503285343)
  ·
    refine ⟨20577690707789694754928015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13718460471859796503285343 20577690707789694754928015)
    ·
      refine ⟨30866536061684542132392023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20577690707789694754928015 30866536061684542132392023)
      ·
        refine ⟨46299804092526813198588035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30866536061684542132392023 46299804092526813198588035)
        ·
          refine ⟨69449706138790219797882053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46299804092526813198588035 69449706138790219797882053)
          ·
            refine ⟨13021819901023166212102885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69449706138790219797882053 13021819901023166212102885)
            ·
              refine ⟨2441591231441843664769291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13021819901023166212102885 2441591231441843664769291)
              ·
                refine ⟨3662386847162765497153937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441591231441843664769291 3662386847162765497153937)
                ·
                  refine ⟨2746790135372074122865453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3662386847162765497153937 2746790135372074122865453)
                  ·
                    refine ⟨1030046300764527796074545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2746790135372074122865453 1030046300764527796074545)
                    ·
                      refine ⟨772534725573395847055909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030046300764527796074545 772534725573395847055909)
                      ·
                        rfl

theorem cell23_1504506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2].length) (baseStart_1504506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504506 prefixEnd_1504506 := by exact prefixLift 1504506
  have htrace : WordTrace (prefixWord ++ tailWord_1504506) baseStart_1504506 baseEnd_1504506 := by
    simpa [prefixWord, tailWord_1504506, baseEnd_1504506] using wordTrace_append hprefix tailTrace_1504506
  have hstable : (prefixWord ++ tailWord_1504506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504506).length < 2 ^ (prefixWord ++ tailWord_1504506).sum := by decide
  have hdescent : baseEnd_1504506 < baseStart_1504506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504546 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_1504546 : Nat := 118140960795 + 1504546 * 2 ^ 59
def prefixEnd_1504546 : Nat := 4983230072969 + 3 ^ 40 * 1504546 * 2
def baseEnd_1504546 : Nat := 257518421599858563518575

theorem tailTrace_1504546 : CollatzResearch.WordTrace tailWord_1504546 prefixEnd_1504546 257518421599858563518575 := by
  unfold tailWord_1504546
  simp only [CollatzResearch.WordTrace]
  refine ⟨13718825201823568211149373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36583533871529515229731661 13718825201823568211149373)
  ·
    refine ⟨5144559450683838079181015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13718825201823568211149373 5144559450683838079181015)
    ·
      refine ⟨7716839176025757118771523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5144559450683838079181015 7716839176025757118771523)
      ·
        refine ⟨11575258764038635678157285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7716839176025757118771523 11575258764038635678157285)
        ·
          refine ⟨2170361018257244189654491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11575258764038635678157285 2170361018257244189654491)
          ·
            refine ⟨3255541527385866284481737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170361018257244189654491 3255541527385866284481737)
            ·
              refine ⟨2441656145539399713361303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3255541527385866284481737 2441656145539399713361303)
              ·
                refine ⟨3662484218309099570041955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441656145539399713361303 3662484218309099570041955)
                ·
                  refine ⟨5493726327463649355062933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662484218309099570041955 5493726327463649355062933)
                  ·
                    refine ⟨257518421599858563518575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5493726327463649355062933 257518421599858563518575)
                    ·
                      rfl

theorem cell23_1504546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_1504546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504546 prefixEnd_1504546 := by exact prefixLift 1504546
  have htrace : WordTrace (prefixWord ++ tailWord_1504546) baseStart_1504546 baseEnd_1504546 := by
    simpa [prefixWord, tailWord_1504546, baseEnd_1504546] using wordTrace_append hprefix tailTrace_1504546
  have hstable : (prefixWord ++ tailWord_1504546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504546).length < 2 ^ (prefixWord ++ tailWord_1504546).sum := by decide
  have hdescent : baseEnd_1504546 < baseStart_1504546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504549 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_1504549 : Nat := 118140960795 + 1504549 * 2 ^ 59
def prefixEnd_1504549 : Nat := 4983230072969 + 3 ^ 40 * 1504549 * 2
def baseEnd_1504549 : Nat := 772556805241539178818211

theorem tailTrace_1504549 : CollatzResearch.WordTrace tailWord_1504549 prefixEnd_1504549 772556805241539178818211 := by
  unfold tailWord_1504549
  simp only [CollatzResearch.WordTrace]
  refine ⟨54875410226283404356956701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36583606817522269571304467 54875410226283404356956701)
  ·
    refine ⟨20578278834856276633858763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54875410226283404356956701 20578278834856276633858763)
    ·
      refine ⟨30867418252284414950788145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20578278834856276633858763 30867418252284414950788145)
      ·
        refine ⟨23150563689213311213091109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30867418252284414950788145 23150563689213311213091109)
        ·
          refine ⟨4340730691727495852454583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23150563689213311213091109 4340730691727495852454583)
          ·
            refine ⟨6511096037591243778681875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340730691727495852454583 6511096037591243778681875)
            ·
              refine ⟨9766644056386865668022813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511096037591243778681875 9766644056386865668022813)
              ·
                refine ⟨3662491521145074625508555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9766644056386865668022813 3662491521145074625508555)
                ·
                  refine ⟨5493737281717611938262833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662491521145074625508555 5493737281717611938262833)
                  ·
                    refine ⟨4120302961288208953697125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5493737281717611938262833 4120302961288208953697125)
                    ·
                      refine ⟨772556805241539178818211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4120302961288208953697125 772556805241539178818211)
                      ·
                        rfl

theorem cell23_1504549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_1504549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504549 prefixEnd_1504549 := by exact prefixLift 1504549
  have htrace : WordTrace (prefixWord ++ tailWord_1504549) baseStart_1504549 baseEnd_1504549 := by
    simpa [prefixWord, tailWord_1504549, baseEnd_1504549] using wordTrace_append hprefix tailTrace_1504549
  have hstable : (prefixWord ++ tailWord_1504549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504549).length < 2 ^ (prefixWord ++ tailWord_1504549).sum := by decide
  have hdescent : baseEnd_1504549 < baseStart_1504549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504570 : List Nat := [3, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2]
def baseStart_1504570 : Nat := 118140960795 + 1504570 * 2 ^ 59
def prefixEnd_1504570 : Nat := 4983230072969 + 3 ^ 40 * 1504570 * 2
def baseEnd_1504570 : Nat := 772567588335283596655615

theorem tailTrace_1504570 : CollatzResearch.WordTrace tailWord_1504570 prefixEnd_1504570 772567588335283596655615 := by
  unfold tailWord_1504570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13719044039801831235867791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36584117439471549962314109 13719044039801831235867791)
  ·
    refine ⟨20578566059702746853801687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13719044039801831235867791 20578566059702746853801687)
    ·
      refine ⟨30867849089554120280702531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20578566059702746853801687 30867849089554120280702531)
      ·
        refine ⟨46301773634331180421053797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30867849089554120280702531 46301773634331180421053797)
        ·
          refine ⟨8681582556437096328947587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46301773634331180421053797 8681582556437096328947587)
          ·
            refine ⟨13022373834655644493421381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8681582556437096328947587 13022373834655644493421381)
            ·
              refine ⟨2441695093997933342516509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13022373834655644493421381 2441695093997933342516509)
              ·
                refine ⟨915635660249225003443691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2441695093997933342516509 915635660249225003443691)
                ·
                  refine ⟨1373453490373837505165537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915635660249225003443691 1373453490373837505165537)
                  ·
                    refine ⟨1030090117780378128874153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1373453490373837505165537 1030090117780378128874153)
                    ·
                      refine ⟨772567588335283596655615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030090117780378128874153 772567588335283596655615)
                      ·
                        rfl

theorem cell23_1504570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2].length) (baseStart_1504570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504570 prefixEnd_1504570 := by exact prefixLift 1504570
  have htrace : WordTrace (prefixWord ++ tailWord_1504570) baseStart_1504570 baseEnd_1504570 := by
    simpa [prefixWord, tailWord_1504570, baseEnd_1504570] using wordTrace_append hprefix tailTrace_1504570
  have hstable : (prefixWord ++ tailWord_1504570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504570).length < 2 ^ (prefixWord ++ tailWord_1504570).sum := by decide
  have hdescent : baseEnd_1504570 < baseStart_1504570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504580 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1504580 : Nat := 118140960795 + 1504580 * 2 ^ 59
def prefixEnd_1504580 : Nat := 4983230072969 + 3 ^ 40 * 1504580 * 2
def baseEnd_1504580 : Nat := 257524241047276185843523

theorem tailTrace_1504580 : CollatzResearch.WordTrace tailWord_1504580 prefixEnd_1504580 257524241047276185843523 := by
  unfold tailWord_1504580
  simp only [CollatzResearch.WordTrace]
  refine ⟨27438270444585548325667597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36584360592780731100890129 27438270444585548325667597)
  ·
    refine ⟨10289351416719580622125349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27438270444585548325667597 10289351416719580622125349)
    ·
      refine ⟨1929253390634921366648503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10289351416719580622125349 1929253390634921366648503)
      ·
        refine ⟨2893880085952382049972755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929253390634921366648503 2893880085952382049972755)
        ·
          refine ⟨4340820128928573074959133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2893880085952382049972755 4340820128928573074959133)
          ·
            refine ⟨1627807548348214903109675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4340820128928573074959133 1627807548348214903109675)
            ·
              refine ⟨2441711322522322354664513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1627807548348214903109675 2441711322522322354664513)
              ·
                refine ⟨1831283491891741765998385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441711322522322354664513 1831283491891741765998385)
                ·
                  refine ⟨1373462618918806324498789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1831283491891741765998385 1373462618918806324498789)
                  ·
                    refine ⟨257524241047276185843523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1373462618918806324498789 257524241047276185843523)
                    ·
                      rfl

theorem cell23_1504580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1504580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504580 prefixEnd_1504580 := by exact prefixLift 1504580
  have htrace : WordTrace (prefixWord ++ tailWord_1504580) baseStart_1504580 baseEnd_1504580 := by
    simpa [prefixWord, tailWord_1504580, baseEnd_1504580] using wordTrace_append hprefix tailTrace_1504580
  have hstable : (prefixWord ++ tailWord_1504580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504580).length < 2 ^ (prefixWord ++ tailWord_1504580).sum := by decide
  have hdescent : baseEnd_1504580 < baseStart_1504580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504613 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 1, 3, 2]
def baseStart_1504613 : Nat := 118140960795 + 1504613 * 2 ^ 59
def prefixEnd_1504613 : Nat := 4983230072969 + 3 ^ 40 * 1504613 * 2
def baseEnd_1504613 : Nat := 772589668003426928417917

theorem tailTrace_1504613 : CollatzResearch.WordTrace tailWord_1504613 prefixEnd_1504613 772589668003426928417917 := by
  unfold tailWord_1504613
  simp only [CollatzResearch.WordTrace]
  refine ⟨54877744498051543287286493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36585162998701028858190995 54877744498051543287286493)
  ·
    refine ⟨20579154186769328732732435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54877744498051543287286493 20579154186769328732732435)
    ·
      refine ⟨30868731280153993099098653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20579154186769328732732435 30868731280153993099098653)
      ·
        refine ⟨11575774230057747412161995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30868731280153993099098653 11575774230057747412161995)
        ·
          refine ⟨17363661345086621118242993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11575774230057747412161995 17363661345086621118242993)
          ·
            refine ⟨13022746008814965838682245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17363661345086621118242993 13022746008814965838682245)
            ·
              refine ⟨2441764876652806094752921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13022746008814965838682245 2441764876652806094752921)
              ·
                refine ⟨1831323657489604571064691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441764876652806094752921 1831323657489604571064691)
                ·
                  refine ⟨2746985486234406856597037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831323657489604571064691 2746985486234406856597037)
                  ·
                    refine ⟨1030119557337902571223889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2746985486234406856597037 1030119557337902571223889)
                    ·
                      refine ⟨772589668003426928417917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030119557337902571223889 772589668003426928417917)
                      ·
                        rfl

theorem cell23_1504613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_1504613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504613 prefixEnd_1504613 := by exact prefixLift 1504613
  have htrace : WordTrace (prefixWord ++ tailWord_1504613) baseStart_1504613 baseEnd_1504613 := by
    simpa [prefixWord, tailWord_1504613, baseEnd_1504613] using wordTrace_append hprefix tailTrace_1504613
  have hstable : (prefixWord ++ tailWord_1504613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504613).length < 2 ^ (prefixWord ++ tailWord_1504613).sum := by decide
  have hdescent : baseEnd_1504613 < baseStart_1504613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504626 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 3, 4, 2]
def baseStart_1504626 : Nat := 118140960795 + 1504626 * 2 ^ 59
def prefixEnd_1504626 : Nat := 4983230072969 + 3 ^ 40 * 1504626 * 2
def baseEnd_1504626 : Nat := 772596343251935377555357

theorem tailTrace_1504626 : CollatzResearch.WordTrace tailWord_1504626 prefixEnd_1504626 772596343251935377555357 := by
  unfold tailWord_1504626
  simp only [CollatzResearch.WordTrace]
  refine ⟨13719554661751111626877433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36585479098002964338339821 13719554661751111626877433)
  ·
    refine ⟨10289665996313333720158075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13719554661751111626877433 10289665996313333720158075)
    ·
      refine ⟨15434498994470000580237113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10289665996313333720158075 15434498994470000580237113)
      ·
        refine ⟨11575874245852500435177835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15434498994470000580237113 11575874245852500435177835)
        ·
          refine ⟨17363811368778750652766753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11575874245852500435177835 17363811368778750652766753)
          ·
            refine ⟨13022858526584062989575065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17363811368778750652766753 13022858526584062989575065)
            ·
              refine ⟨9767143894938047242181299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13022858526584062989575065 9767143894938047242181299)
              ·
                refine ⟨14650715842407070863271949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9767143894938047242181299 14650715842407070863271949)
                ·
                  refine ⟨5494018440902651573726981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14650715842407070863271949 5494018440902651573726981)
                  ·
                    refine ⟨1030128457669247170073809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494018440902651573726981 1030128457669247170073809)
                    ·
                      refine ⟨772596343251935377555357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030128457669247170073809 772596343251935377555357)
                      ·
                        rfl

theorem cell23_1504626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_1504626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504626 prefixEnd_1504626 := by exact prefixLift 1504626
  have htrace : WordTrace (prefixWord ++ tailWord_1504626) baseStart_1504626 baseEnd_1504626 := by
    simpa [prefixWord, tailWord_1504626, baseEnd_1504626] using wordTrace_append hprefix tailTrace_1504626
  have hstable : (prefixWord ++ tailWord_1504626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504626).length < 2 ^ (prefixWord ++ tailWord_1504626).sum := by decide
  have hdescent : baseEnd_1504626 < baseStart_1504626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504643 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 4, 2, 2]
def baseStart_1504643 : Nat := 118140960795 + 1504643 * 2 ^ 59
def prefixEnd_1504643 : Nat := 4983230072969 + 3 ^ 40 * 1504643 * 2
def baseEnd_1504643 : Nat := 772605072423061811042779

theorem tailTrace_1504643 : CollatzResearch.WordTrace tailWord_1504643 prefixEnd_1504643 772605072423061811042779 := by
  unfold tailWord_1504643
  simp only [CollatzResearch.WordTrace]
  refine ⟨54878838687942858410878583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36585892458628572273919055 54878838687942858410878583)
  ·
    refine ⟨82318258031914287616317875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54878838687942858410878583 82318258031914287616317875)
    ·
      refine ⟨123477387047871431424476813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82318258031914287616317875 123477387047871431424476813)
      ·
        refine ⟨46304020142951786784178805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123477387047871431424476813 46304020142951786784178805)
        ·
          refine ⟨4341001888401730011016763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46304020142951786784178805 4341001888401730011016763)
          ·
            refine ⟨6511502832602595016525145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341001888401730011016763 6511502832602595016525145)
            ·
              refine ⟨4883627124451946262393859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6511502832602595016525145 4883627124451946262393859)
              ·
                refine ⟨7325440686677919393590789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4883627124451946262393859 7325440686677919393590789)
                ·
                  refine ⟨1373520128752109886298273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7325440686677919393590789 1373520128752109886298273)
                  ·
                    refine ⟨1030140096564082414723705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1373520128752109886298273 1030140096564082414723705)
                    ·
                      refine ⟨772605072423061811042779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030140096564082414723705 772605072423061811042779)
                      ·
                        rfl

theorem cell23_1504643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 2, 2].length) (baseStart_1504643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504643 prefixEnd_1504643 := by exact prefixLift 1504643
  have htrace : WordTrace (prefixWord ++ tailWord_1504643) baseStart_1504643 baseEnd_1504643 := by
    simpa [prefixWord, tailWord_1504643, baseEnd_1504643] using wordTrace_append hprefix tailTrace_1504643
  have hstable : (prefixWord ++ tailWord_1504643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504643).length < 2 ^ (prefixWord ++ tailWord_1504643).sum := by decide
  have hdescent : baseEnd_1504643 < baseStart_1504643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504654 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3]
def baseStart_1504654 : Nat := 118140960795 + 1504654 * 2 ^ 59
def prefixEnd_1504654 : Nat := 4983230072969 + 3 ^ 40 * 1504654 * 2
def baseEnd_1504654 : Nat := 772610720710261268005229

theorem tailTrace_1504654 : CollatzResearch.WordTrace tailWord_1504654 prefixEnd_1504654 772610720710261268005229 := by
  unfold tailWord_1504654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6859904986362875911191127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36586159927268671526352677 6859904986362875911191127)
  ·
    refine ⟨10289857479544313866786691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6859904986362875911191127 10289857479544313866786691)
    ·
      refine ⟨15434786219316470800180037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10289857479544313866786691 15434786219316470800180037)
      ·
        refine ⟨2894022416121838275033757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15434786219316470800180037 2894022416121838275033757)
        ·
          refine ⟨1085258406045689353137659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2894022416121838275033757 1085258406045689353137659)
          ·
            refine ⟨1627887609068534029706489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085258406045689353137659 1627887609068534029706489)
            ·
              refine ⟨1220915706801400522279867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1627887609068534029706489 1220915706801400522279867)
              ·
                refine ⟨1831373560202100783419801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220915706801400522279867 1831373560202100783419801)
                ·
                  refine ⟨1373530170151575587564851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1831373560202100783419801 1373530170151575587564851)
                  ·
                    refine ⟨2060295255227363381347277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1373530170151575587564851 2060295255227363381347277)
                    ·
                      refine ⟨772610720710261268005229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2060295255227363381347277 772610720710261268005229)
                      ·
                        rfl

theorem cell23_1504654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_1504654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504654 prefixEnd_1504654 := by exact prefixLift 1504654
  have htrace : WordTrace (prefixWord ++ tailWord_1504654) baseStart_1504654 baseEnd_1504654 := by
    simpa [prefixWord, tailWord_1504654, baseEnd_1504654] using wordTrace_append hprefix tailTrace_1504654
  have hstable : (prefixWord ++ tailWord_1504654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504654).length < 2 ^ (prefixWord ++ tailWord_1504654).sum := by decide
  have hdescent : baseEnd_1504654 < baseStart_1504654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504689 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1504689 : Nat := 118140960795 + 1504689 * 2 ^ 59
def prefixEnd_1504689 : Nat := 4983230072969 + 3 ^ 40 * 1504689 * 2
def baseEnd_1504689 : Nat := 772628692533168631067567

theorem tailTrace_1504689 : CollatzResearch.WordTrace tailWord_1504689 prefixEnd_1504689 772628692533168631067567 := by
  unfold tailWord_1504689
  simp only [CollatzResearch.WordTrace]
  refine ⟨54880516445776208267053121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36587010963850805511368747 54880516445776208267053121)
  ·
    refine ⟨41160387334332156200289841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54880516445776208267053121 41160387334332156200289841)
    ·
      refine ⟨30870290500749117150217381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41160387334332156200289841 30870290500749117150217381)
      ·
        refine ⟨5788179468890459465665759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30870290500749117150217381 5788179468890459465665759)
        ·
          refine ⟨8682269203335689198498639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788179468890459465665759 8682269203335689198498639)
          ·
            refine ⟨13023403805003533797747959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8682269203335689198498639 13023403805003533797747959)
            ·
              refine ⟨19535105707505300696621939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13023403805003533797747959 19535105707505300696621939)
              ·
                refine ⟨29302658561257951044932909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19535105707505300696621939 29302658561257951044932909)
                ·
                  refine ⟨10988496960471731641849841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29302658561257951044932909 10988496960471731641849841)
                  ·
                    refine ⟨8241372720353798731387381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10988496960471731641849841 8241372720353798731387381)
                    ·
                      refine ⟨772628692533168631067567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8241372720353798731387381 772628692533168631067567)
                      ·
                        rfl

theorem cell23_1504689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1504689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504689 prefixEnd_1504689 := by exact prefixLift 1504689
  have htrace : WordTrace (prefixWord ++ tailWord_1504689) baseStart_1504689 baseEnd_1504689 := by
    simpa [prefixWord, tailWord_1504689, baseEnd_1504689] using wordTrace_append hprefix tailTrace_1504689
  have hstable : (prefixWord ++ tailWord_1504689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504689).length < 2 ^ (prefixWord ++ tailWord_1504689).sum := by decide
  have hdescent : baseEnd_1504689 < baseStart_1504689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504733 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1504733 : Nat := 118140960795 + 1504733 * 2 ^ 59
def prefixEnd_1504733 : Nat := 4983230072969 + 3 ^ 40 * 1504733 * 2
def baseEnd_1504733 : Nat := 772651285681966458917365

theorem tailTrace_1504733 : CollatzResearch.WordTrace tailWord_1504733 prefixEnd_1504733 772651285681966458917365 := by
  unfold tailWord_1504733
  simp only [CollatzResearch.WordTrace]
  refine ⟨54882121257616803781654853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36588080838411202521103235 54882121257616803781654853)
  ·
    refine ⟨10290397735803150709060285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54882121257616803781654853 10290397735803150709060285)
    ·
      refine ⟨3858899150926181515897607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10290397735803150709060285 3858899150926181515897607)
      ·
        refine ⟨5788348726389272273846411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3858899150926181515897607 5788348726389272273846411)
        ·
          refine ⟨8682523089583908410769617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788348726389272273846411 8682523089583908410769617)
          ·
            refine ⟨6511892317187931308077213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8682523089583908410769617 6511892317187931308077213)
            ·
              refine ⟨2441959618945474240528955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6511892317187931308077213 2441959618945474240528955)
              ·
                refine ⟨3662939428418211360793433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441959618945474240528955 3662939428418211360793433)
                ·
                  refine ⟨2747204571313658520595075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3662939428418211360793433 2747204571313658520595075)
                  ·
                    refine ⟨4120806856970487780892613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2747204571313658520595075 4120806856970487780892613)
                    ·
                      refine ⟨772651285681966458917365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4120806856970487780892613 772651285681966458917365)
                      ·
                        rfl

theorem cell23_1504733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1504733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504733 prefixEnd_1504733 := by exact prefixLift 1504733
  have htrace : WordTrace (prefixWord ++ tailWord_1504733) baseStart_1504733 baseEnd_1504733 := by
    simpa [prefixWord, tailWord_1504733, baseEnd_1504733] using wordTrace_append hprefix tailTrace_1504733
  have hstable : (prefixWord ++ tailWord_1504733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504733).length < 2 ^ (prefixWord ++ tailWord_1504733).sum := by decide
  have hdescent : baseEnd_1504733 < baseStart_1504733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504736 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 3]
def baseStart_1504736 : Nat := 118140960795 + 1504736 * 2 ^ 59
def prefixEnd_1504736 : Nat := 4983230072969 + 3 ^ 40 * 1504736 * 2
def baseEnd_1504736 : Nat := 772652826123929947179851

theorem tailTrace_1504736 : CollatzResearch.WordTrace tailWord_1504736 prefixEnd_1504736 772652826123929947179851 := by
  unfold tailWord_1504736
  simp only [CollatzResearch.WordTrace]
  refine ⟨27441115338302967647007031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36588153784403956862676041 27441115338302967647007031)
  ·
    refine ⟨41161673007454451470510547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27441115338302967647007031 41161673007454451470510547)
    ·
      refine ⟨61742509511181677205765821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41161673007454451470510547 61742509511181677205765821)
      ·
        refine ⟨23153441066693128952162183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61742509511181677205765821 23153441066693128952162183)
        ·
          refine ⟨34730161600039693428243275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23153441066693128952162183 34730161600039693428243275)
          ·
            refine ⟨52095242400059540142364913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34730161600039693428243275 52095242400059540142364913)
            ·
              refine ⟨39071431800044655106773685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52095242400059540142364913 39071431800044655106773685)
              ·
                refine ⟨3662946731254186416260033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39071431800044655106773685 3662946731254186416260033)
                ·
                  refine ⟨2747210048440639812195025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3662946731254186416260033 2747210048440639812195025)
                  ·
                    refine ⟨2060407536330479859146269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2747210048440639812195025 2060407536330479859146269)
                    ·
                      refine ⟨772652826123929947179851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2060407536330479859146269 772652826123929947179851)
                      ·
                        rfl

theorem cell23_1504736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_1504736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504736 prefixEnd_1504736 := by exact prefixLift 1504736
  have htrace : WordTrace (prefixWord ++ tailWord_1504736) baseStart_1504736 baseEnd_1504736 := by
    simpa [prefixWord, tailWord_1504736, baseEnd_1504736] using wordTrace_append hprefix tailTrace_1504736
  have hstable : (prefixWord ++ tailWord_1504736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504736).length < 2 ^ (prefixWord ++ tailWord_1504736).sum := by decide
  have hdescent : baseEnd_1504736 < baseStart_1504736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504810 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_1504810 : Nat := 118140960795 + 1504810 * 2 ^ 59
def prefixEnd_1504810 : Nat := 4983230072969 + 3 ^ 40 * 1504810 * 2
def baseEnd_1504810 : Nat := 772690823692362657654511

theorem tailTrace_1504810 : CollatzResearch.WordTrace tailWord_1504810 prefixEnd_1504810 772690823692362657654511 := by
  unfold tailWord_1504810
  simp only [CollatzResearch.WordTrace]
  refine ⟨13721232419584461483051971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36589953118891897288138589 13721232419584461483051971)
  ·
    refine ⟨20581848629376692224577957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13721232419584461483051971 20581848629376692224577957)
    ·
      refine ⟨3859096618008129792108367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20581848629376692224577957 3859096618008129792108367)
      ·
        refine ⟨5788644927012194688162551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859096618008129792108367 5788644927012194688162551)
        ·
          refine ⟨8682967390518292032243827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788644927012194688162551 8682967390518292032243827)
          ·
            refine ⟨13024451085777438048365741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8682967390518292032243827 13024451085777438048365741)
            ·
              refine ⟨4884169157166539268137153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13024451085777438048365741 4884169157166539268137153)
              ·
                refine ⟨3663126867874904451102865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884169157166539268137153 3663126867874904451102865)
                ·
                  refine ⟨2747345150906178338327149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3663126867874904451102865 2747345150906178338327149)
                  ·
                    refine ⟨1030254431589816876872681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747345150906178338327149 1030254431589816876872681)
                    ·
                      refine ⟨772690823692362657654511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030254431589816876872681 772690823692362657654511)
                      ·
                        rfl

theorem cell23_1504810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_1504810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504810 prefixEnd_1504810 := by exact prefixLift 1504810
  have htrace : WordTrace (prefixWord ++ tailWord_1504810) baseStart_1504810 baseEnd_1504810 := by
    simpa [prefixWord, tailWord_1504810, baseEnd_1504810] using wordTrace_append hprefix tailTrace_1504810
  have hstable : (prefixWord ++ tailWord_1504810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504810).length < 2 ^ (prefixWord ++ tailWord_1504810).sum := by decide
  have hdescent : baseEnd_1504810 < baseStart_1504810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504826 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_1504826 : Nat := 118140960795 + 1504826 * 2 ^ 59
def prefixEnd_1504826 : Nat := 4983230072969 + 3 ^ 40 * 1504826 * 2
def baseEnd_1504826 : Nat := 772699039382834595054437

theorem tailTrace_1504826 : CollatzResearch.WordTrace tailWord_1504826 prefixEnd_1504826 772699039382834595054437 := by
  unfold tailWord_1504826
  simp only [CollatzResearch.WordTrace]
  refine ⟨13721378311569970166197583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36590342164186587109860221 13721378311569970166197583)
  ·
    refine ⟨20582067467354955249296375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13721378311569970166197583 20582067467354955249296375)
    ·
      refine ⟨30873101201032432873944563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20582067467354955249296375 30873101201032432873944563)
      ·
        refine ⟨46309651801548649310916845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30873101201032432873944563 46309651801548649310916845)
        ·
          refine ⟨17366119425580743491593817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46309651801548649310916845 17366119425580743491593817)
          ·
            refine ⟨13024589569185557618695363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17366119425580743491593817 13024589569185557618695363)
            ·
              refine ⟨19536884353778336428043045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13024589569185557618695363 19536884353778336428043045)
              ·
                refine ⟨3663165816333438080258071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19536884353778336428043045 3663165816333438080258071)
                ·
                  refine ⟨5494748724500157120387107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663165816333438080258071 5494748724500157120387107)
                  ·
                    refine ⟨8242123086750235680580661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5494748724500157120387107 8242123086750235680580661)
                    ·
                      refine ⟨772699039382834595054437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8242123086750235680580661 772699039382834595054437)
                      ·
                        rfl

theorem cell23_1504826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_1504826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504826 prefixEnd_1504826 := by exact prefixLift 1504826
  have htrace : WordTrace (prefixWord ++ tailWord_1504826) baseStart_1504826 baseEnd_1504826 := by
    simpa [prefixWord, tailWord_1504826, baseEnd_1504826] using wordTrace_append hprefix tailTrace_1504826
  have hstable : (prefixWord ++ tailWord_1504826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504826).length < 2 ^ (prefixWord ++ tailWord_1504826).sum := by decide
  have hdescent : baseEnd_1504826 < baseStart_1504826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504860 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1504860 : Nat := 118140960795 + 1504860 * 2 ^ 59
def prefixEnd_1504860 : Nat := 4983230072969 + 3 ^ 40 * 1504860 * 2
def baseEnd_1504860 : Nat := 772716497725087462029281

theorem tailTrace_1504860 : CollatzResearch.WordTrace tailWord_1504860 prefixEnd_1504860 772716497725087462029281 := by
  unfold tailWord_1504860
  simp only [CollatzResearch.WordTrace]
  refine ⟨27443376664078352235764017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36591168885437802981018689 27443376664078352235764017)
  ·
    refine ⟨20582532498058764176823013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27443376664078352235764017 20582532498058764176823013)
    ·
      refine ⟨3859224843386018283154315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20582532498058764176823013 3859224843386018283154315)
      ·
        refine ⟨5788837265079027424731473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859224843386018283154315 5788837265079027424731473)
        ·
          refine ⟨4341627948809270568548605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5788837265079027424731473 4341627948809270568548605)
          ·
            refine ⟨1628110480803476463205727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4341627948809270568548605 1628110480803476463205727)
            ·
              refine ⟨2442165721205214694808591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628110480803476463205727 2442165721205214694808591)
              ·
                refine ⟨3663248581807822042212887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442165721205214694808591 3663248581807822042212887)
                ·
                  refine ⟨5494872872711733063319331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663248581807822042212887 5494872872711733063319331)
                  ·
                    refine ⟨8242309309067599594978997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5494872872711733063319331 8242309309067599594978997)
                    ·
                      refine ⟨772716497725087462029281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8242309309067599594978997 772716497725087462029281)
                      ·
                        rfl

theorem cell23_1504860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1504860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504860 prefixEnd_1504860 := by exact prefixLift 1504860
  have htrace : WordTrace (prefixWord ++ tailWord_1504860) baseStart_1504860 baseEnd_1504860 := by
    simpa [prefixWord, tailWord_1504860, baseEnd_1504860] using wordTrace_append hprefix tailTrace_1504860
  have hstable : (prefixWord ++ tailWord_1504860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504860).length < 2 ^ (prefixWord ++ tailWord_1504860).sum := by decide
  have hdescent : baseEnd_1504860 < baseStart_1504860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504873 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 4, 1, 3]
def baseStart_1504873 : Nat := 118140960795 + 1504873 * 2 ^ 59
def prefixEnd_1504873 : Nat := 4983230072969 + 3 ^ 40 * 1504873 * 2
def baseEnd_1504873 : Nat := 772723172973595911166721

theorem tailTrace_1504873 : CollatzResearch.WordTrace tailWord_1504873 prefixEnd_1504873 772723172973595911166721 := by
  unfold tailWord_1504873
  simp only [CollatzResearch.WordTrace]
  refine ⟨54887227477109607691751273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36591484984739738461167515 54887227477109607691751273)
  ·
    refine ⟨41165420607832205768813455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54887227477109607691751273 41165420607832205768813455)
    ·
      refine ⟨61748130911748308653220183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41165420607832205768813455 61748130911748308653220183)
      ·
        refine ⟨92622196367622462979830275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61748130911748308653220183 92622196367622462979830275)
        ·
          refine ⟨138933294551433694469745413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92622196367622462979830275 138933294551433694469745413)
          ·
            refine ⟨26049992728393817713077265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138933294551433694469745413 26049992728393817713077265)
            ·
              refine ⟨19537494546295363284807949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26049992728393817713077265 19537494546295363284807949)
              ·
                refine ⟨7326560454860761231802981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19537494546295363284807949 7326560454860761231802981)
                ·
                  refine ⟨1373730085286392730963059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7326560454860761231802981 1373730085286392730963059)
                  ·
                    refine ⟨2060595127929589096444589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1373730085286392730963059 2060595127929589096444589)
                    ·
                      refine ⟨772723172973595911166721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2060595127929589096444589 772723172973595911166721)
                      ·
                        rfl

theorem cell23_1504873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 1, 3].length) (baseStart_1504873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504873 prefixEnd_1504873 := by exact prefixLift 1504873
  have htrace : WordTrace (prefixWord ++ tailWord_1504873) baseStart_1504873 baseEnd_1504873 := by
    simpa [prefixWord, tailWord_1504873, baseEnd_1504873] using wordTrace_append hprefix tailTrace_1504873
  have hstable : (prefixWord ++ tailWord_1504873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504873).length < 2 ^ (prefixWord ++ tailWord_1504873).sum := by decide
  have hdescent : baseEnd_1504873 < baseStart_1504873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504874 : List Nat := [3, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_1504874 : Nat := 118140960795 + 1504874 * 2 ^ 59
def prefixEnd_1504874 : Nat := 4983230072969 + 3 ^ 40 * 1504874 * 2
def baseEnd_1504874 : Nat := 772723686454250407254217

theorem tailTrace_1504874 : CollatzResearch.WordTrace tailWord_1504874 prefixEnd_1504874 772723686454250407254217 := by
  unfold tailWord_1504874
  simp only [CollatzResearch.WordTrace]
  refine ⟨13721815987526496215634419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36591509300070656575025117 13721815987526496215634419)
  ·
    refine ⟨20582723981289744323451629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13721815987526496215634419 20582723981289744323451629)
    ·
      refine ⟨7718521492983654121294361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20582723981289744323451629 7718521492983654121294361)
      ·
        refine ⟨5788891119737740590970771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7718521492983654121294361 5788891119737740590970771)
        ·
          refine ⟨8683336679606610886456157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788891119737740590970771 8683336679606610886456157)
          ·
            refine ⟨3256251254852479082421059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8683336679606610886456157 3256251254852479082421059)
            ·
              refine ⟨4884376882278718623631589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3256251254852479082421059 4884376882278718623631589)
              ·
                refine ⟨915820665427259741930923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4884376882278718623631589 915820665427259741930923)
                ·
                  refine ⟨1373730998140889612896385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915820665427259741930923 1373730998140889612896385)
                  ·
                    refine ⟨1030298248605667209672289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1373730998140889612896385 1030298248605667209672289)
                    ·
                      refine ⟨772723686454250407254217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030298248605667209672289 772723686454250407254217)
                      ·
                        rfl

theorem cell23_1504874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_1504874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504874 prefixEnd_1504874 := by exact prefixLift 1504874
  have htrace : WordTrace (prefixWord ++ tailWord_1504874) baseStart_1504874 baseEnd_1504874 := by
    simpa [prefixWord, tailWord_1504874, baseEnd_1504874] using wordTrace_append hprefix tailTrace_1504874
  have hstable : (prefixWord ++ tailWord_1504874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504874).length < 2 ^ (prefixWord ++ tailWord_1504874).sum := by decide
  have hdescent : baseEnd_1504874 < baseStart_1504874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504896 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 4]
def baseStart_1504896 : Nat := 118140960795 + 1504896 * 2 ^ 59
def prefixEnd_1504896 : Nat := 4983230072969 + 3 ^ 40 * 1504896 * 2
def baseEnd_1504896 : Nat := 772734983028649321179115

theorem tailTrace_1504896 : CollatzResearch.WordTrace tailWord_1504896 prefixEnd_1504896 772734983028649321179115 := by
  unfold tailWord_1504896
  simp only [CollatzResearch.WordTrace]
  refine ⟨27444033178013141309919271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36592044237350855079892361 27444033178013141309919271)
  ·
    refine ⟨41166049767019711964878907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27444033178013141309919271 41166049767019711964878907)
    ·
      refine ⟨61749074650529567947318361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41166049767019711964878907 61749074650529567947318361)
      ·
        refine ⟨46311805987897175960488771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61749074650529567947318361 46311805987897175960488771)
        ·
          refine ⟨69467708981845763940733157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46311805987897175960488771 69467708981845763940733157)
          ·
            refine ⟨13025195434096080738887467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69467708981845763940733157 13025195434096080738887467)
            ·
              refine ⟨19537793151144121108331201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13025195434096080738887467 19537793151144121108331201)
              ·
                refine ⟨14653344863358090831248401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19537793151144121108331201 14653344863358090831248401)
                ·
                  refine ⟨10990008647518568123436301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14653344863358090831248401 10990008647518568123436301)
                  ·
                    refine ⟨4121253242819463046288613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10990008647518568123436301 4121253242819463046288613)
                    ·
                      refine ⟨772734983028649321179115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4121253242819463046288613 772734983028649321179115)
                      ·
                        rfl

theorem cell23_1504896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_1504896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504896 prefixEnd_1504896 := by exact prefixLift 1504896
  have htrace : WordTrace (prefixWord ++ tailWord_1504896) baseStart_1504896 baseEnd_1504896 := by
    simpa [prefixWord, tailWord_1504896, baseEnd_1504896] using wordTrace_append hprefix tailTrace_1504896
  have hstable : (prefixWord ++ tailWord_1504896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504896).length < 2 ^ (prefixWord ++ tailWord_1504896).sum := by decide
  have hdescent : baseEnd_1504896 < baseStart_1504896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504913 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 3, 4, 2]
def baseStart_1504913 : Nat := 118140960795 + 1504913 * 2 ^ 59
def prefixEnd_1504913 : Nat := 4983230072969 + 3 ^ 40 * 1504913 * 2
def baseEnd_1504913 : Nat := 772743712199775754666537

theorem tailTrace_1504913 : CollatzResearch.WordTrace tailWord_1504913 prefixEnd_1504913 772743712199775754666537 := by
  unfold tailWord_1504913
  simp only [CollatzResearch.WordTrace]
  refine ⟨54888686396964694523207393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36592457597976463015471595 54888686396964694523207393)
  ·
    refine ⟨41166514797723520892405545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54888686396964694523207393 41166514797723520892405545)
    ·
      refine ⟨30874886098292640669304159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41166514797723520892405545 30874886098292640669304159)
      ·
        refine ⟨46312329147438961003956239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30874886098292640669304159 46312329147438961003956239)
        ·
          refine ⟨69468493721158441505934359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46312329147438961003956239 69468493721158441505934359)
          ·
            refine ⟨104202740581737662258901539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69468493721158441505934359 104202740581737662258901539)
            ·
              refine ⟨156304110872606493388352309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104202740581737662258901539 156304110872606493388352309)
              ·
                refine ⟨14653510394306858755158029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156304110872606493388352309 14653510394306858755158029)
                ·
                  refine ⟨5495066397865072033184261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14653510394306858755158029 5495066397865072033184261)
                  ·
                    refine ⟨1030324949599701006222049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5495066397865072033184261 1030324949599701006222049)
                    ·
                      refine ⟨772743712199775754666537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030324949599701006222049 772743712199775754666537)
                      ·
                        rfl

theorem cell23_1504913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 4, 2].length) (baseStart_1504913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504913 prefixEnd_1504913 := by exact prefixLift 1504913
  have htrace : WordTrace (prefixWord ++ tailWord_1504913) baseStart_1504913 baseEnd_1504913 := by
    simpa [prefixWord, tailWord_1504913, baseEnd_1504913] using wordTrace_append hprefix tailTrace_1504913
  have hstable : (prefixWord ++ tailWord_1504913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504913).length < 2 ^ (prefixWord ++ tailWord_1504913).sum := by decide
  have hdescent : baseEnd_1504913 < baseStart_1504913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504924 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1504924 : Nat := 118140960795 + 1504924 * 2 ^ 59
def prefixEnd_1504924 : Nat := 4983230072969 + 3 ^ 40 * 1504924 * 2
def baseEnd_1504924 : Nat := 772749360486975211628987

theorem tailTrace_1504924 : CollatzResearch.WordTrace tailWord_1504924 prefixEnd_1504924 772749360486975211628987 := by
  unfold tailWord_1504924
  simp only [CollatzResearch.WordTrace]
  refine ⟨27444543799962421700928913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36592725066616562267905217 27444543799962421700928913)
  ·
    refine ⟨20583407849971816275696685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27444543799962421700928913 20583407849971816275696685)
    ·
      refine ⟨7718777943739431103386257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20583407849971816275696685 7718777943739431103386257)
      ·
        refine ⟨5789083457804573327539693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7718777943739431103386257 5789083457804573327539693)
        ·
          refine ⟨2170906296676714997827385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5789083457804573327539693 2170906296676714997827385)
          ·
            refine ⟨1628179722507536248370539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2170906296676714997827385 1628179722507536248370539)
            ·
              refine ⟨2442269583761304372555809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628179722507536248370539 2442269583761304372555809)
              ·
                refine ⟨1831702187820978279416857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2442269583761304372555809 1831702187820978279416857)
                ·
                  refine ⟨1373776640865733709562643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1831702187820978279416857 1373776640865733709562643)
                  ·
                    refine ⟨2060664961298600564343965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1373776640865733709562643 2060664961298600564343965)
                    ·
                      refine ⟨772749360486975211628987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2060664961298600564343965 772749360486975211628987)
                      ·
                        rfl

theorem cell23_1504924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1504924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504924 prefixEnd_1504924 := by exact prefixLift 1504924
  have htrace : WordTrace (prefixWord ++ tailWord_1504924) baseStart_1504924 baseEnd_1504924 := by
    simpa [prefixWord, tailWord_1504924, baseEnd_1504924] using wordTrace_append hprefix tailTrace_1504924
  have hstable : (prefixWord ++ tailWord_1504924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504924).length < 2 ^ (prefixWord ++ tailWord_1504924).sum := by decide
  have hdescent : baseEnd_1504924 < baseStart_1504924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504983 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 2, 5]
def baseStart_1504983 : Nat := 118140960795 + 1504983 * 2 ^ 59
def prefixEnd_1504983 : Nat := 4983230072969 + 3 ^ 40 * 1504983 * 2
def baseEnd_1504983 : Nat := 257593218615196826930405

theorem tailTrace_1504983 : CollatzResearch.WordTrace tailWord_1504983 prefixEnd_1504983 257593218615196826930405 := by
  unfold tailWord_1504983
  simp only [CollatzResearch.WordTrace]
  refine ⟨54891239506711096478255603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36594159671140730985503735 54891239506711096478255603)
  ·
    refine ⟨82336859260066644717383405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54891239506711096478255603 82336859260066644717383405)
    ·
      refine ⟨30876322222524991769018777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82336859260066644717383405 30876322222524991769018777)
      ·
        refine ⟨23157241666893743826764083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30876322222524991769018777 23157241666893743826764083)
        ·
          refine ⟨34735862500340615740146125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23157241666893743826764083 34735862500340615740146125)
          ·
            refine ⟨13025948437627730902554797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34735862500340615740146125 13025948437627730902554797)
            ·
              refine ⟨4884730664110399088458049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13025948437627730902554797 4884730664110399088458049)
              ·
                refine ⟨3663547998082799316343537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884730664110399088458049 3663547998082799316343537)
                ·
                  refine ⟨2747660998562099487257653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3663547998082799316343537 2747660998562099487257653)
                  ·
                    refine ⟨257593218615196826930405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2747660998562099487257653 257593218615196826930405)
                    ·
                      rfl

theorem cell23_1504983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_1504983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1504983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1504983 prefixEnd_1504983 := by exact prefixLift 1504983
  have htrace : WordTrace (prefixWord ++ tailWord_1504983) baseStart_1504983 baseEnd_1504983 := by
    simpa [prefixWord, tailWord_1504983, baseEnd_1504983] using wordTrace_append hprefix tailTrace_1504983
  have hstable : (prefixWord ++ tailWord_1504983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504983).length < 2 ^ (prefixWord ++ tailWord_1504983).sum := by decide
  have hdescent : baseEnd_1504983 < baseStart_1504983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505020 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_1505020 : Nat := 118140960795 + 1505020 * 2 ^ 59
def prefixEnd_1505020 : Nat := 4983230072969 + 3 ^ 40 * 1505020 * 2
def baseEnd_1505020 : Nat := 772798654629806836028545

theorem tailTrace_1505020 : CollatzResearch.WordTrace tailWord_1505020 prefixEnd_1505020 772798654629806836028545 := by
  unfold tailWord_1505020
  simp only [CollatzResearch.WordTrace]
  refine ⟨27446294503788525898676257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36595059338384701198235009 27446294503788525898676257)
  ·
    refine ⟨20584720877841394424007193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27446294503788525898676257 20584720877841394424007193)
    ·
      refine ⟨15438540658381045818005395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20584720877841394424007193 15438540658381045818005395)
      ·
        refine ⟨23157810987571568727008093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15438540658381045818005395 23157810987571568727008093)
        ·
          refine ⟨8684179120339338272628035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23157810987571568727008093 8684179120339338272628035)
          ·
            refine ⟨13026268680509007408942053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8684179120339338272628035 13026268680509007408942053)
            ·
              refine ⟨2442425377595438889176635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13026268680509007408942053 2442425377595438889176635)
              ·
                refine ⟨3663638066393158333764953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442425377595438889176635 3663638066393158333764953)
                ·
                  refine ⟨2747728549794868750323715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3663638066393158333764953 2747728549794868750323715)
                  ·
                    refine ⟨4121592824692303125485573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2747728549794868750323715 4121592824692303125485573)
                    ·
                      refine ⟨772798654629806836028545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4121592824692303125485573 772798654629806836028545)
                      ·
                        rfl

theorem cell23_1505020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_1505020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505020 prefixEnd_1505020 := by exact prefixLift 1505020
  have htrace : WordTrace (prefixWord ++ tailWord_1505020) baseStart_1505020 baseEnd_1505020 := by
    simpa [prefixWord, tailWord_1505020, baseEnd_1505020] using wordTrace_append hprefix tailTrace_1505020
  have hstable : (prefixWord ++ tailWord_1505020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505020).length < 2 ^ (prefixWord ++ tailWord_1505020).sum := by decide
  have hdescent : baseEnd_1505020 < baseStart_1505020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505023 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 3]
def baseStart_1505023 : Nat := 118140960795 + 1505023 * 2 ^ 59
def prefixEnd_1505023 : Nat := 4983230072969 + 3 ^ 40 * 1505023 * 2
def baseEnd_1505023 : Nat := 772800195071770324291031

theorem tailTrace_1505023 : CollatzResearch.WordTrace tailWord_1505023 prefixEnd_1505023 772800195071770324291031 := by
  unfold tailWord_1505023
  simp only [CollatzResearch.WordTrace]
  refine ⟨54892698426566183309711723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36595132284377455539807815 54892698426566183309711723)
  ·
    refine ⟨82339047639849274964567585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54892698426566183309711723 82339047639849274964567585)
    ·
      refine ⟨61754285729886956223425689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82339047639849274964567585 61754285729886956223425689)
      ·
        refine ⟨46315714297415217167569267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61754285729886956223425689 46315714297415217167569267)
        ·
          refine ⟨69473571446122825751353901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46315714297415217167569267 69473571446122825751353901)
          ·
            refine ⟨26052589292296059656757713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69473571446122825751353901 26052589292296059656757713)
            ·
              refine ⟨19539441969222044742568285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26052589292296059656757713 19539441969222044742568285)
              ·
                refine ⟨7327290738458266778463107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19539441969222044742568285 7327290738458266778463107)
                ·
                  refine ⟨10990936107687400167694661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7327290738458266778463107 10990936107687400167694661)
                  ·
                    refine ⟨2060800520191387531442749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10990936107687400167694661 2060800520191387531442749)
                    ·
                      refine ⟨772800195071770324291031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2060800520191387531442749 772800195071770324291031)
                      ·
                        rfl

theorem cell23_1505023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_1505023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505023 prefixEnd_1505023 := by exact prefixLift 1505023
  have htrace : WordTrace (prefixWord ++ tailWord_1505023) baseStart_1505023 baseEnd_1505023 := by
    simpa [prefixWord, tailWord_1505023, baseEnd_1505023] using wordTrace_append hprefix tailTrace_1505023
  have hstable : (prefixWord ++ tailWord_1505023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505023).length < 2 ^ (prefixWord ++ tailWord_1505023).sum := by decide
  have hdescent : baseEnd_1505023 < baseStart_1505023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505060 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 6]
def baseStart_1505060 : Nat := 118140960795 + 1505060 * 2 ^ 59
def prefixEnd_1505060 : Nat := 4983230072969 + 3 ^ 40 * 1505060 * 2
def baseEnd_1505060 : Nat := 85868799317331853280929

theorem tailTrace_1505060 : CollatzResearch.WordTrace tailWord_1505060 prefixEnd_1505060 85868799317331853280929 := by
  unfold tailWord_1505060
  simp only [CollatzResearch.WordTrace]
  refine ⟨27447023963716069314404317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36596031951621425752539089 27447023963716069314404317)
  ·
    refine ⟨10292633986393525992901619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27447023963716069314404317 10292633986393525992901619)
    ·
      refine ⟨15438950979590288989352429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10292633986393525992901619 15438950979590288989352429)
      ·
        refine ⟨5789606617346358371007161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15438950979590288989352429 5789606617346358371007161)
        ·
          refine ⟨4342204963009768778255371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5789606617346358371007161 4342204963009768778255371)
          ·
            refine ⟨6513307444514653167383057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342204963009768778255371 6513307444514653167383057)
            ·
              refine ⟨4884980583385989875537293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6513307444514653167383057 4884980583385989875537293)
              ·
                refine ⟨1831867718769746203326485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4884980583385989875537293 1831867718769746203326485)
                ·
                  refine ⟨85868799317331853280929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1831867718769746203326485 85868799317331853280929)
                  ·
                    rfl

theorem cell23_1505060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_1505060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505060 prefixEnd_1505060 := by exact prefixLift 1505060
  have htrace : WordTrace (prefixWord ++ tailWord_1505060) baseStart_1505060 baseEnd_1505060 := by
    simpa [prefixWord, tailWord_1505060, baseEnd_1505060] using wordTrace_append hprefix tailTrace_1505060
  have hstable : (prefixWord ++ tailWord_1505060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505060).length < 2 ^ (prefixWord ++ tailWord_1505060).sum := by decide
  have hdescent : baseEnd_1505060 < baseStart_1505060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505081 : List Nat := [1, 2, 1, 7, 1, 1, 2, 3, 1, 4]
def baseStart_1505081 : Nat := 118140960795 + 1505081 * 2 ^ 59
def prefixEnd_1505081 : Nat := 4983230072969 + 3 ^ 40 * 1505081 * 2
def baseEnd_1505081 : Nat := 257609992316577032455255

theorem tailTrace_1505081 : CollatzResearch.WordTrace tailWord_1505081 prefixEnd_1505081 257609992316577032455255 := by
  unfold tailWord_1505081
  simp only [CollatzResearch.WordTrace]
  refine ⟨54894813860356059215323097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36596542573570706143548731 54894813860356059215323097)
  ·
    refine ⟨41171110395267044411492323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54894813860356059215323097 41171110395267044411492323)
    ·
      refine ⟨61756665592900566617238485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41171110395267044411492323 61756665592900566617238485)
      ·
        refine ⟨1447421849833607030091527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 61756665592900566617238485 1447421849833607030091527)
        ·
          refine ⟨2171132774750410545137291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447421849833607030091527 2171132774750410545137291)
          ·
            refine ⟨3256699162125615817705937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171132774750410545137291 3256699162125615817705937)
            ·
              refine ⟨2442524371594211863279453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3256699162125615817705937 2442524371594211863279453)
              ·
                refine ⟨915946639347829448729795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2442524371594211863279453 915946639347829448729795)
                ·
                  refine ⟨1373919959021744173094693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915946639347829448729795 1373919959021744173094693)
                  ·
                    refine ⟨257609992316577032455255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1373919959021744173094693 257609992316577032455255)
                    ·
                      rfl

theorem cell23_1505081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 1, 4].length) (baseStart_1505081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505081 prefixEnd_1505081 := by exact prefixLift 1505081
  have htrace : WordTrace (prefixWord ++ tailWord_1505081) baseStart_1505081 baseEnd_1505081 := by
    simpa [prefixWord, tailWord_1505081, baseEnd_1505081] using wordTrace_append hprefix tailTrace_1505081
  have hstable : (prefixWord ++ tailWord_1505081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505081).length < 2 ^ (prefixWord ++ tailWord_1505081).sum := by decide
  have hdescent : baseEnd_1505081 < baseStart_1505081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505094 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_1505094 : Nat := 118140960795 + 1505094 * 2 ^ 59
def prefixEnd_1505094 : Nat := 4983230072969 + 3 ^ 40 * 1505094 * 2
def baseEnd_1505094 : Nat := 85870739133137727389245

theorem tailTrace_1505094 : CollatzResearch.WordTrace tailWord_1505094 prefixEnd_1505094 85870739133137727389245 := by
  unfold tailWord_1505094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1715477750290905076110823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36596858672872641623697557 1715477750290905076110823)
  ·
    refine ⟨2573216625436357614166235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1715477750290905076110823 2573216625436357614166235)
    ·
      refine ⟨3859824938154536421249353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2573216625436357614166235 3859824938154536421249353)
      ·
        refine ⟨2894868703615902315937015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3859824938154536421249353 2894868703615902315937015)
        ·
          refine ⟨4342303055423853473905523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894868703615902315937015 4342303055423853473905523)
          ·
            refine ⟨6513454583135780210858285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342303055423853473905523 6513454583135780210858285)
            ·
              refine ⟨2442545468675917579071857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6513454583135780210858285 2442545468675917579071857)
              ·
                refine ⟨1831909101506938184303893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2442545468675917579071857 1831909101506938184303893)
                ·
                  refine ⟨85870739133137727389245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1831909101506938184303893 85870739133137727389245)
                  ·
                    rfl

theorem cell23_1505094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_1505094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505094 prefixEnd_1505094 := by exact prefixLift 1505094
  have htrace : WordTrace (prefixWord ++ tailWord_1505094) baseStart_1505094 baseEnd_1505094 := by
    simpa [prefixWord, tailWord_1505094, baseEnd_1505094] using wordTrace_append hprefix tailTrace_1505094
  have hstable : (prefixWord ++ tailWord_1505094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505094).length < 2 ^ (prefixWord ++ tailWord_1505094).sum := by decide
  have hdescent : baseEnd_1505094 < baseStart_1505094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505120 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 1, 6]
def baseStart_1505120 : Nat := 118140960795 + 1505120 * 2 ^ 59
def prefixEnd_1505120 : Nat := 4983230072969 + 3 ^ 40 * 1505120 * 2
def baseEnd_1505120 : Nat := 257616667565085481592695

theorem tailTrace_1505120 : CollatzResearch.WordTrace tailWord_1505120 prefixEnd_1505120 257616667565085481592695 := by
  unfold tailWord_1505120
  simp only [CollatzResearch.WordTrace]
  refine ⟨27448118153607384437996407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36597490871476512583995209 27448118153607384437996407)
  ·
    refine ⟨41172177230411076656994611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27448118153607384437996407 41172177230411076656994611)
    ·
      refine ⟨61758265845616614985491917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41172177230411076656994611 61758265845616614985491917)
      ·
        refine ⟨23159349692106230619559469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61758265845616614985491917 23159349692106230619559469)
        ·
          refine ⟨8684756134539836482334801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23159349692106230619559469 8684756134539836482334801)
          ·
            refine ⟨6513567100904877361751101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8684756134539836482334801 6513567100904877361751101)
            ·
              refine ⟨2442587662839329010656663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6513567100904877361751101 2442587662839329010656663)
              ·
                refine ⟨3663881494258993515984995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442587662839329010656663 3663881494258993515984995)
                ·
                  refine ⟨5495822241388490273977493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663881494258993515984995 5495822241388490273977493)
                  ·
                    refine ⟨257616667565085481592695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5495822241388490273977493 257616667565085481592695)
                    ·
                      rfl

theorem cell23_1505120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 1, 6].length) (baseStart_1505120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505120 prefixEnd_1505120 := by exact prefixLift 1505120
  have htrace : WordTrace (prefixWord ++ tailWord_1505120) baseStart_1505120 baseEnd_1505120 := by
    simpa [prefixWord, tailWord_1505120, baseEnd_1505120] using wordTrace_append hprefix tailTrace_1505120
  have hstable : (prefixWord ++ tailWord_1505120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505120).length < 2 ^ (prefixWord ++ tailWord_1505120).sum := by decide
  have hdescent : baseEnd_1505120 < baseStart_1505120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505127 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_1505127 : Nat := 118140960795 + 1505127 * 2 ^ 59
def prefixEnd_1505127 : Nat := 4983230072969 + 3 ^ 40 * 1505127 * 2
def baseEnd_1505127 : Nat := 772853597059837917390553

theorem tailTrace_1505127 : CollatzResearch.WordTrace tailWord_1505127 prefixEnd_1505127 772853597059837917390553 := by
  unfold tailWord_1505127
  simp only [CollatzResearch.WordTrace]
  refine ⟨54896491618189409071497635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36597661078792939380998423 54896491618189409071497635)
  ·
    refine ⟨82344737427284113607246453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54896491618189409071497635 82344737427284113607246453)
    ·
      refine ⟨7719819133807885650679355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82344737427284113607246453 7719819133807885650679355)
      ·
        refine ⟨11579728700711828476019033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7719819133807885650679355 11579728700711828476019033)
        ·
          refine ⟨8684796525533871357014275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11579728700711828476019033 8684796525533871357014275)
          ·
            refine ⟨13027194788300807035521413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8684796525533871357014275 13027194788300807035521413)
            ·
              refine ⟨2442599022806401319160265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13027194788300807035521413 2442599022806401319160265)
              ·
                refine ⟨1831949267104800989370199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2442599022806401319160265 1831949267104800989370199)
                ·
                  refine ⟨2747923900657201484055299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831949267104800989370199 2747923900657201484055299)
                  ·
                    refine ⟨4121885850985802226082949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2747923900657201484055299 4121885850985802226082949)
                    ·
                      refine ⟨772853597059837917390553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4121885850985802226082949 772853597059837917390553)
                      ·
                        rfl

theorem cell23_1505127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_1505127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505127 prefixEnd_1505127 := by exact prefixLift 1505127
  have htrace : WordTrace (prefixWord ++ tailWord_1505127) baseStart_1505127 baseEnd_1505127 := by
    simpa [prefixWord, tailWord_1505127, baseEnd_1505127] using wordTrace_append hprefix tailTrace_1505127
  have hstable : (prefixWord ++ tailWord_1505127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505127).length < 2 ^ (prefixWord ++ tailWord_1505127).sum := by decide
  have hdescent : baseEnd_1505127 < baseStart_1505127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505163 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 2, 7]
def baseStart_1505163 : Nat := 118140960795 + 1505163 * 2 ^ 59
def prefixEnd_1505163 : Nat := 4983230072969 + 3 ^ 40 * 1505163 * 2
def baseEnd_1505163 : Nat := 257624027454466592180129

theorem tailTrace_1505163 : CollatzResearch.WordTrace tailWord_1505163 prefixEnd_1505163 257624027454466592180129 := by
  unfold tailWord_1505163
  simp only [CollatzResearch.WordTrace]
  refine ⟨54897804646058987219808143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36598536430705991479872095 54897804646058987219808143)
  ·
    refine ⟨82346706969088480829712215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54897804646058987219808143 82346706969088480829712215)
    ·
      refine ⟨123520060453632721244568323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82346706969088480829712215 123520060453632721244568323)
      ·
        refine ⟨185280090680449081866852485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123520060453632721244568323 185280090680449081866852485)
        ·
          refine ⟨34740017002584202850034841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185280090680449081866852485 34740017002584202850034841)
          ·
            refine ⟨26055012751938152137526131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34740017002584202850034841 26055012751938152137526131)
            ·
              refine ⟨39082519127907228206289197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26055012751938152137526131 39082519127907228206289197)
              ·
                refine ⟨14655944672965210577358449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39082519127907228206289197 14655944672965210577358449)
                ·
                  refine ⟨10991958504723907933018837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14655944672965210577358449 10991958504723907933018837)
                  ·
                    refine ⟨257624027454466592180129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10991958504723907933018837 257624027454466592180129)
                    ·
                      rfl

theorem cell23_1505163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 7].length) (baseStart_1505163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505163 prefixEnd_1505163 := by exact prefixLift 1505163
  have htrace : WordTrace (prefixWord ++ tailWord_1505163) baseStart_1505163 baseEnd_1505163 := by
    simpa [prefixWord, tailWord_1505163, baseEnd_1505163] using wordTrace_append hprefix tailTrace_1505163
  have hstable : (prefixWord ++ tailWord_1505163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505163).length < 2 ^ (prefixWord ++ tailWord_1505163).sum := by decide
  have hdescent : baseEnd_1505163 < baseStart_1505163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505193 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 3, 8]
def baseStart_1505193 : Nat := 118140960795 + 1505193 * 2 ^ 59
def prefixEnd_1505193 : Nat := 4983230072969 + 3 ^ 40 * 1505193 * 2
def baseEnd_1505193 : Nat := 257629162261011553055083

theorem tailTrace_1505193 : CollatzResearch.WordTrace tailWord_1505193 prefixEnd_1505193 257629162261011553055083 := by
  unfold tailWord_1505193
  simp only [CollatzResearch.WordTrace]
  refine ⟨54898898835950302343400233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36599265890633534895600155 54898898835950302343400233)
  ·
    refine ⟨41174174126962726757550175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54898898835950302343400233 41174174126962726757550175)
    ·
      refine ⟨61761261190444090136325263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41174174126962726757550175 61761261190444090136325263)
      ·
        refine ⟨92641891785666135204487895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61761261190444090136325263 92641891785666135204487895)
        ·
          refine ⟨138962837678499202806731843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92641891785666135204487895 138962837678499202806731843)
          ·
            refine ⟨208444256517748804210097765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138962837678499202806731843 208444256517748804210097765)
            ·
              refine ⟨39083298097077900789393331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208444256517748804210097765 39083298097077900789393331)
              ·
                refine ⟨58624947145616851184089997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39083298097077900789393331 58624947145616851184089997)
                ·
                  refine ⟨21984355179606319194033749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58624947145616851184089997 21984355179606319194033749)
                  ·
                    refine ⟨257629162261011553055083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21984355179606319194033749 257629162261011553055083)
                    ·
                      rfl

theorem cell23_1505193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_1505193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505193 prefixEnd_1505193 := by exact prefixLift 1505193
  have htrace : WordTrace (prefixWord ++ tailWord_1505193) baseStart_1505193 baseEnd_1505193 := by
    simpa [prefixWord, tailWord_1505193, baseEnd_1505193] using wordTrace_append hprefix tailTrace_1505193
  have hstable : (prefixWord ++ tailWord_1505193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505193).length < 2 ^ (prefixWord ++ tailWord_1505193).sum := by decide
  have hdescent : baseEnd_1505193 < baseStart_1505193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505198 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1505198 : Nat := 118140960795 + 1505198 * 2 ^ 59
def prefixEnd_1505198 : Nat := 4983230072969 + 3 ^ 40 * 1505198 * 2
def baseEnd_1505198 : Nat := 772890054186307139602727

theorem tailTrace_1505198 : CollatzResearch.WordTrace tailWord_1505198 prefixEnd_1505198 772890054186307139602727 := by
  unfold tailWord_1505198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6862385150116523524666531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36599387467288125464888165 6862385150116523524666531)
  ·
    refine ⟨10293577725174785286999797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6862385150116523524666531 10293577725174785286999797)
    ·
      refine ⟨965022911735136120656231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10293577725174785286999797 965022911735136120656231)
      ·
        refine ⟨1447534367602704180984347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965022911735136120656231 1447534367602704180984347)
        ·
          refine ⟨2171301551404056271476521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447534367602704180984347 2171301551404056271476521)
          ·
            refine ⟨1628476163553042203607391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2171301551404056271476521 1628476163553042203607391)
            ·
              refine ⟨2442714245329563305411087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628476163553042203607391 2442714245329563305411087)
              ·
                refine ⟨3664071367994344958116631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442714245329563305411087 3664071367994344958116631)
                ·
                  refine ⟨5496107051991517437174947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664071367994344958116631 5496107051991517437174947)
                  ·
                    refine ⟨8244160577987276155762421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5496107051991517437174947 8244160577987276155762421)
                    ·
                      refine ⟨772890054186307139602727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8244160577987276155762421 772890054186307139602727)
                      ·
                        rfl

theorem cell23_1505198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1505198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505198 prefixEnd_1505198 := by exact prefixLift 1505198
  have htrace : WordTrace (prefixWord ++ tailWord_1505198) baseStart_1505198 baseEnd_1505198 := by
    simpa [prefixWord, tailWord_1505198, baseEnd_1505198] using wordTrace_append hprefix tailTrace_1505198
  have hstable : (prefixWord ++ tailWord_1505198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505198).length < 2 ^ (prefixWord ++ tailWord_1505198).sum := by decide
  have hdescent : baseEnd_1505198 < baseStart_1505198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505212 : List Nat := [2, 2, 2, 5, 1, 2, 2, 2, 1, 2, 2]
def baseStart_1505212 : Nat := 118140960795 + 1505212 * 2 ^ 59
def prefixEnd_1505212 : Nat := 4983230072969 + 3 ^ 40 * 1505212 * 2
def baseEnd_1505212 : Nat := 772897242915470084827663

theorem tailTrace_1505212 : CollatzResearch.WordTrace tailWord_1505212 prefixEnd_1505212 772897242915470084827663 := by
  unfold tailWord_1505212
  simp only [CollatzResearch.WordTrace]
  refine ⟨27449795911440734294170945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36599727881920979058894593 27449795911440734294170945)
  ·
    refine ⟨20587346933580550720628209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27449795911440734294170945 20587346933580550720628209)
    ·
      refine ⟨15440510200185413040471157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20587346933580550720628209 15440510200185413040471157)
      ·
        refine ⟨1447547831267382472544171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15440510200185413040471157 1447547831267382472544171)
        ·
          refine ⟨2171321746901073708816257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447547831267382472544171 2171321746901073708816257)
          ·
            refine ⟨1628491310175805281612193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2171321746901073708816257 1628491310175805281612193)
            ·
              refine ⟨1221368482631853961209145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628491310175805281612193 1221368482631853961209145)
              ·
                refine ⟨916026361973890470906859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221368482631853961209145 916026361973890470906859)
                ·
                  refine ⟨1374039542960835706360289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 916026361973890470906859 1374039542960835706360289)
                  ·
                    refine ⟨1030529657220626779770217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1374039542960835706360289 1030529657220626779770217)
                    ·
                      refine ⟨772897242915470084827663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030529657220626779770217 772897242915470084827663)
                      ·
                        rfl

theorem cell23_1505212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_1505212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505212 prefixEnd_1505212 := by exact prefixLift 1505212
  have htrace : WordTrace (prefixWord ++ tailWord_1505212) baseStart_1505212 baseEnd_1505212 := by
    simpa [prefixWord, tailWord_1505212, baseEnd_1505212] using wordTrace_append hprefix tailTrace_1505212
  have hstable : (prefixWord ++ tailWord_1505212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505212).length < 2 ^ (prefixWord ++ tailWord_1505212).sum := by decide
  have hdescent : baseEnd_1505212 < baseStart_1505212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505240 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 7]
def baseStart_1505240 : Nat := 118140960795 + 1505240 * 2 ^ 59
def prefixEnd_1505240 : Nat := 4983230072969 + 3 ^ 40 * 1505240 * 2
def baseEnd_1505240 : Nat := 85879068930421775030837

theorem tailTrace_1505240 : CollatzResearch.WordTrace tailWord_1505240 prefixEnd_1505240 85879068930421775030837 := by
  unfold tailWord_1505240
  simp only [CollatzResearch.WordTrace]
  refine ⟨27450306533390014685180587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36600408711186686246907449 27450306533390014685180587)
  ·
    refine ⟨41175459800085022027770881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27450306533390014685180587 41175459800085022027770881)
    ·
      refine ⟨30881594850063766520828161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41175459800085022027770881 30881594850063766520828161)
      ·
        refine ⟨23161196137547824890621121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30881594850063766520828161 23161196137547824890621121)
        ·
          refine ⟨17370897103160868667965841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23161196137547824890621121 17370897103160868667965841)
          ·
            refine ⟨13028172827370651500974381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17370897103160868667965841 13028172827370651500974381)
            ·
              refine ⟨4885564810263994312865393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13028172827370651500974381 4885564810263994312865393)
              ·
                refine ⟨3664173607697995734649045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4885564810263994312865393 3664173607697995734649045)
                ·
                  refine ⟨85879068930421775030837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3664173607697995734649045 85879068930421775030837)
                  ·
                    rfl

theorem cell23_1505240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 7].length) (baseStart_1505240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505240 prefixEnd_1505240 := by exact prefixLift 1505240
  have htrace : WordTrace (prefixWord ++ tailWord_1505240) baseStart_1505240 baseEnd_1505240 := by
    simpa [prefixWord, tailWord_1505240, baseEnd_1505240] using wordTrace_append hprefix tailTrace_1505240
  have hstable : (prefixWord ++ tailWord_1505240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505240).length < 2 ^ (prefixWord ++ tailWord_1505240).sum := by decide
  have hdescent : baseEnd_1505240 < baseStart_1505240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505255 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_1505255 : Nat := 118140960795 + 1505255 * 2 ^ 59
def prefixEnd_1505255 : Nat := 4983230072969 + 3 ^ 40 * 1505255 * 2
def baseEnd_1505255 : Nat := 772919322583613416589965

theorem tailTrace_1505255 : CollatzResearch.WordTrace tailWord_1505255 prefixEnd_1505255 772919322583613416589965 := by
  unfold tailWord_1505255
  simp only [CollatzResearch.WordTrace]
  refine ⟨54901160161725686932157219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36600773441150457954771479 54901160161725686932157219)
  ·
    refine ⟨82351740242588530398235829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54901160161725686932157219 82351740242588530398235829)
    ·
      refine ⟨7720475647742674724834609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82351740242588530398235829 7720475647742674724834609)
      ·
        refine ⟨5790356735807006043625957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7720475647742674724834609 5790356735807006043625957)
        ·
          refine ⟨1085691887963813633179867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5790356735807006043625957 1085691887963813633179867)
          ·
            refine ⟨1628537831945720449769801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085691887963813633179867 1628537831945720449769801)
            ·
              refine ⟨1221403373959290337327351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628537831945720449769801 1221403373959290337327351)
              ·
                refine ⟨1832105060938935505991027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221403373959290337327351 1832105060938935505991027)
                ·
                  refine ⟨2748157591408403258986541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832105060938935505991027 2748157591408403258986541)
                  ·
                    refine ⟨1030559096778151222119953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2748157591408403258986541 1030559096778151222119953)
                    ·
                      refine ⟨772919322583613416589965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030559096778151222119953 772919322583613416589965)
                      ·
                        rfl

theorem cell23_1505255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_1505255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505255 prefixEnd_1505255 := by exact prefixLift 1505255
  have htrace : WordTrace (prefixWord ++ tailWord_1505255) baseStart_1505255 baseEnd_1505255 := by
    simpa [prefixWord, tailWord_1505255, baseEnd_1505255] using wordTrace_append hprefix tailTrace_1505255
  have hstable : (prefixWord ++ tailWord_1505255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505255).length < 2 ^ (prefixWord ++ tailWord_1505255).sum := by decide
  have hdescent : baseEnd_1505255 < baseStart_1505255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505277 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 1, 7, 2]
def baseStart_1505277 : Nat := 118140960795 + 1505277 * 2 ^ 59
def prefixEnd_1505277 : Nat := 4983230072969 + 3 ^ 40 * 1505277 * 2
def baseEnd_1505277 : Nat := 772930619158012330514863

theorem tailTrace_1505277 : CollatzResearch.WordTrace tailWord_1505277 prefixEnd_1505277 772930619158012330514863 := by
  unfold tailWord_1505277
  simp only [CollatzResearch.WordTrace]
  refine ⟨54901962567645984689458085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36601308378430656459638723 54901962567645984689458085)
  ·
    refine ⟨10294117981433622129273391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54901962567645984689458085 10294117981433622129273391)
    ·
      refine ⟨15441176972150433193910087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10294117981433622129273391 15441176972150433193910087)
      ·
        refine ⟨23161765458225649790865131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15441176972150433193910087 23161765458225649790865131)
        ·
          refine ⟨34742648187338474686297697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23161765458225649790865131 34742648187338474686297697)
          ·
            refine ⟨26056986140503856014723273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34742648187338474686297697 26056986140503856014723273)
            ·
              refine ⟨19542739605377892011042455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26056986140503856014723273 19542739605377892011042455)
              ·
                refine ⟨29314109408066838016563683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19542739605377892011042455 29314109408066838016563683)
                ·
                  refine ⟨43971164112100257024845525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29314109408066838016563683 43971164112100257024845525)
                  ·
                    refine ⟨1030574158877349774019817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43971164112100257024845525 1030574158877349774019817)
                    ·
                      refine ⟨772930619158012330514863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030574158877349774019817 772930619158012330514863)
                      ·
                        rfl

theorem cell23_1505277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_1505277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505277 prefixEnd_1505277 := by exact prefixLift 1505277
  have htrace : WordTrace (prefixWord ++ tailWord_1505277) baseStart_1505277 baseEnd_1505277 := by
    simpa [prefixWord, tailWord_1505277, baseEnd_1505277] using wordTrace_append hprefix tailTrace_1505277
  have hstable : (prefixWord ++ tailWord_1505277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505277).length < 2 ^ (prefixWord ++ tailWord_1505277).sum := by decide
  have hdescent : baseEnd_1505277 < baseStart_1505277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505307 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 2]
def baseStart_1505307 : Nat := 118140960795 + 1505307 * 2 ^ 59
def prefixEnd_1505307 : Nat := 4983230072969 + 3 ^ 40 * 1505307 * 2
def baseEnd_1505307 : Nat := 772946023577647213139725

theorem tailTrace_1505307 : CollatzResearch.WordTrace tailWord_1505307 prefixEnd_1505307 772946023577647213139725 := by
  unfold tailWord_1505307
  simp only [CollatzResearch.WordTrace]
  refine ⟨54903056757537299813050175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36602037838358199875366783 54903056757537299813050175)
  ·
    refine ⟨82354585136305949719575263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54903056757537299813050175 82354585136305949719575263)
    ·
      refine ⟨123531877704458924579362895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82354585136305949719575263 123531877704458924579362895)
      ·
        refine ⟨185297816556688386869044343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123531877704458924579362895 185297816556688386869044343)
        ·
          refine ⟨277946724835032580303566515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185297816556688386869044343 277946724835032580303566515)
          ·
            refine ⟨416920087252548870455349773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277946724835032580303566515 416920087252548870455349773)
            ·
              refine ⟨156345032719705826420756165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 416920087252548870455349773 156345032719705826420756165)
              ·
                refine ⟨29314693634944842453891781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156345032719705826420756165 29314693634944842453891781)
                ·
                  refine ⟨5496505056552157960104709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29314693634944842453891781 5496505056552157960104709)
                  ·
                    refine ⟨1030594698103529617519633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5496505056552157960104709 1030594698103529617519633)
                    ·
                      refine ⟨772946023577647213139725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030594698103529617519633 772946023577647213139725)
                      ·
                        rfl

theorem cell23_1505307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4, 2].length) (baseStart_1505307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505307 prefixEnd_1505307 := by exact prefixLift 1505307
  have htrace : WordTrace (prefixWord ++ tailWord_1505307) baseStart_1505307 baseEnd_1505307 := by
    simpa [prefixWord, tailWord_1505307, baseEnd_1505307] using wordTrace_append hprefix tailTrace_1505307
  have hstable : (prefixWord ++ tailWord_1505307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505307).length < 2 ^ (prefixWord ++ tailWord_1505307).sum := by decide
  have hdescent : baseEnd_1505307 < baseStart_1505307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505418 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2]
def baseStart_1505418 : Nat := 118140960795 + 1505418 * 2 ^ 59
def prefixEnd_1505418 : Nat := 4983230072969 + 3 ^ 40 * 1505418 * 2
def baseEnd_1505418 : Nat := 773003019930296278851715

theorem tailTrace_1505418 : CollatzResearch.WordTrace tailWord_1505418 prefixEnd_1505418 773003019930296278851715 := by
  unfold tailWord_1505418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13726776315033791442585227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36604736840090110513560605 13726776315033791442585227)
  ·
    refine ⟨20590164472550687163877841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13726776315033791442585227 20590164472550687163877841)
    ·
      refine ⟨15442623354413015372908381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20590164472550687163877841 15442623354413015372908381)
      ·
        refine ⟨5790983757904880764840643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15442623354413015372908381 5790983757904880764840643)
        ·
          refine ⟨8686475636857321147260965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5790983757904880764840643 8686475636857321147260965)
          ·
            refine ⟨1628714181910747715111431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8686475636857321147260965 1628714181910747715111431)
            ·
              refine ⟨2443071272866121572667147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628714181910747715111431 2443071272866121572667147)
              ·
                refine ⟨3664606909299182359000721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443071272866121572667147 3664606909299182359000721)
                ·
                  refine ⟨2748455181974386769250541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3664606909299182359000721 2748455181974386769250541)
                  ·
                    refine ⟨1030670693240395038468953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2748455181974386769250541 1030670693240395038468953)
                    ·
                      refine ⟨773003019930296278851715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030670693240395038468953 773003019930296278851715)
                      ·
                        rfl

theorem cell23_1505418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_1505418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505418 prefixEnd_1505418 := by exact prefixLift 1505418
  have htrace : WordTrace (prefixWord ++ tailWord_1505418) baseStart_1505418 baseEnd_1505418 := by
    simpa [prefixWord, tailWord_1505418, baseEnd_1505418] using wordTrace_append hprefix tailTrace_1505418
  have hstable : (prefixWord ++ tailWord_1505418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505418).length < 2 ^ (prefixWord ++ tailWord_1505418).sum := by decide
  have hdescent : baseEnd_1505418 < baseStart_1505418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505428 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_1505428 : Nat := 118140960795 + 1505428 * 2 ^ 59
def prefixEnd_1505428 : Nat := 4983230072969 + 3 ^ 40 * 1505428 * 2
def baseEnd_1505428 : Nat := 257669384912280413242223

theorem tailTrace_1505428 : CollatzResearch.WordTrace tailWord_1505428 prefixEnd_1505428 257669384912280413242223 := by
  unfold tailWord_1505428
  simp only [CollatzResearch.WordTrace]
  refine ⟨27453734995049468739102469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36604979993399291652136625 27453734995049468739102469)
  ·
    refine ⟨5147575311571775388581713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27453734995049468739102469 5147575311571775388581713)
    ·
      refine ⟨3860681483678831541436285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5147575311571775388581713 3860681483678831541436285)
      ·
        refine ⟨1447755556379561828038607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3860681483678831541436285 1447755556379561828038607)
        ·
          refine ⟨2171633334569342742057911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447755556379561828038607 2171633334569342742057911)
          ·
            refine ⟨3257450001854014113086867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171633334569342742057911 3257450001854014113086867)
            ·
              refine ⟨4886175002781021169630301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3257450001854014113086867 4886175002781021169630301)
              ·
                refine ⟨1832315626042882938611363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4886175002781021169630301 1832315626042882938611363)
                ·
                  refine ⟨2748473439064324407917045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832315626042882938611363 2748473439064324407917045)
                  ·
                    refine ⟨257669384912280413242223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2748473439064324407917045 257669384912280413242223)
                    ·
                      rfl

theorem cell23_1505428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_1505428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505428 prefixEnd_1505428 := by exact prefixLift 1505428
  have htrace : WordTrace (prefixWord ++ tailWord_1505428) baseStart_1505428 baseEnd_1505428 := by
    simpa [prefixWord, tailWord_1505428, baseEnd_1505428] using wordTrace_append hprefix tailTrace_1505428
  have hstable : (prefixWord ++ tailWord_1505428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505428).length < 2 ^ (prefixWord ++ tailWord_1505428).sum := by decide
  have hdescent : baseEnd_1505428 < baseStart_1505428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505431 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 4]
def baseStart_1505431 : Nat := 118140960795 + 1505431 * 2 ^ 59
def prefixEnd_1505431 : Nat := 4983230072969 + 3 ^ 40 * 1505431 * 2
def baseEnd_1505431 : Nat := 773009695178804727989155

theorem tailTrace_1505431 : CollatzResearch.WordTrace tailWord_1505431 prefixEnd_1505431 773009695178804727989155 := by
  unfold tailWord_1505431
  simp only [CollatzResearch.WordTrace]
  refine ⟨54907579409088068990564147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36605052939392045993709431 54907579409088068990564147)
  ·
    refine ⟨82361369113632103485846221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54907579409088068990564147 82361369113632103485846221)
    ·
      refine ⟨30885513417612038807192333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82361369113632103485846221 30885513417612038807192333)
      ·
        refine ⟨11582067531604514552697125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30885513417612038807192333 11582067531604514552697125)
        ·
          refine ⟨2171637662175846478630711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11582067531604514552697125 2171637662175846478630711)
          ·
            refine ⟨3257456493263769717946067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171637662175846478630711 3257456493263769717946067)
            ·
              refine ⟨4886184739895654576919101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3257456493263769717946067 4886184739895654576919101)
              ·
                refine ⟨1832319277460870466344663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4886184739895654576919101 1832319277460870466344663)
                ·
                  refine ⟨2748478916191305699516995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832319277460870466344663 2748478916191305699516995)
                  ·
                    refine ⟨4122718374286958549275493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2748478916191305699516995 4122718374286958549275493)
                    ·
                      refine ⟨773009695178804727989155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4122718374286958549275493 773009695178804727989155)
                      ·
                        rfl

theorem cell23_1505431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_1505431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505431 prefixEnd_1505431 := by exact prefixLift 1505431
  have htrace : WordTrace (prefixWord ++ tailWord_1505431) baseStart_1505431 baseEnd_1505431 := by
    simpa [prefixWord, tailWord_1505431, baseEnd_1505431] using wordTrace_append hprefix tailTrace_1505431
  have hstable : (prefixWord ++ tailWord_1505431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505431).length < 2 ^ (prefixWord ++ tailWord_1505431).sum := by decide
  have hdescent : baseEnd_1505431 < baseStart_1505431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505437 : List Nat := [1, 4, 2, 1, 1, 4, 10]
def baseStart_1505437 : Nat := 118140960795 + 1505437 * 2 ^ 59
def prefixEnd_1505437 : Nat := 4983230072969 + 3 ^ 40 * 1505437 * 2
def baseEnd_1505437 : Nat := 9543367605712737092767

theorem tailTrace_1505437 : CollatzResearch.WordTrace tailWord_1505437 prefixEnd_1505437 9543367605712737092767 := by
  unfold tailWord_1505437
  simp only [CollatzResearch.WordTrace]
  refine ⟨54907798247066332015282565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36605198831377554676855043 54907798247066332015282565)
  ·
    refine ⟨10295212171324937252865481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54907798247066332015282565 10295212171324937252865481)
    ·
      refine ⟨7721409128493702939649111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10295212171324937252865481 7721409128493702939649111)
      ·
        refine ⟨11582113692740554409473667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7721409128493702939649111 11582113692740554409473667)
        ·
          refine ⟨17373170539110831614210501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11582113692740554409473667 17373170539110831614210501)
          ·
            refine ⟨3257469476083280927664469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17373170539110831614210501 3257469476083280927664469)
            ·
              refine ⟨9543367605712737092767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3257469476083280927664469 9543367605712737092767)
              ·
                rfl

theorem cell23_1505437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 10].length) (baseStart_1505437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505437 prefixEnd_1505437 := by exact prefixLift 1505437
  have htrace : WordTrace (prefixWord ++ tailWord_1505437) baseStart_1505437 baseEnd_1505437 := by
    simpa [prefixWord, tailWord_1505437, baseEnd_1505437] using wordTrace_append hprefix tailTrace_1505437
  have hstable : (prefixWord ++ tailWord_1505437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505437).length < 2 ^ (prefixWord ++ tailWord_1505437).sum := by decide
  have hdescent : baseEnd_1505437 < baseStart_1505437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505441 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 2, 4]
def baseStart_1505441 : Nat := 118140960795 + 1505441 * 2 ^ 59
def prefixEnd_1505441 : Nat := 4983230072969 + 3 ^ 40 * 1505441 * 2
def baseEnd_1505441 : Nat := 257671609995116562954703

theorem tailTrace_1505441 : CollatzResearch.WordTrace tailWord_1505441 prefixEnd_1505441 257671609995116562954703 := by
  unfold tailWord_1505441
  simp only [CollatzResearch.WordTrace]
  refine ⟨54907944139051840698428177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36605296092701227132285451 54907944139051840698428177)
  ·
    refine ⟨41180958104288880523821133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54907944139051840698428177 41180958104288880523821133)
    ·
      refine ⟨15442859289108330196432925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41180958104288880523821133 15442859289108330196432925)
      ·
        refine ⟨5791072233415623823662347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15442859289108330196432925 5791072233415623823662347)
        ·
          refine ⟨8686608350123435735493521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5791072233415623823662347 8686608350123435735493521)
          ·
            refine ⟨6514956262592576801620141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8686608350123435735493521 6514956262592576801620141)
            ·
              refine ⟨2443108598472216300607553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6514956262592576801620141 2443108598472216300607553)
              ·
                refine ⟨1832331448854162225455665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2443108598472216300607553 1832331448854162225455665)
                ·
                  refine ⟨1374248586640621669091749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1832331448854162225455665 1374248586640621669091749)
                  ·
                    refine ⟨257671609995116562954703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1374248586640621669091749 257671609995116562954703)
                    ·
                      rfl

theorem cell23_1505441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_1505441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505441 prefixEnd_1505441 := by exact prefixLift 1505441
  have htrace : WordTrace (prefixWord ++ tailWord_1505441) baseStart_1505441 baseEnd_1505441 := by
    simpa [prefixWord, tailWord_1505441, baseEnd_1505441] using wordTrace_append hprefix tailTrace_1505441
  have hstable : (prefixWord ++ tailWord_1505441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505441).length < 2 ^ (prefixWord ++ tailWord_1505441).sum := by decide
  have hdescent : baseEnd_1505441 < baseStart_1505441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505461 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1505461 : Nat := 118140960795 + 1505461 * 2 ^ 59
def prefixEnd_1505461 : Nat := 4983230072969 + 3 ^ 40 * 1505461 * 2
def baseEnd_1505461 : Nat := 773025099598439610614017

theorem tailTrace_1505461 : CollatzResearch.WordTrace tailWord_1505461 prefixEnd_1505461 773025099598439610614017 := by
  unfold tailWord_1505461
  simp only [CollatzResearch.WordTrace]
  refine ⟨54908673598979384114156237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36605782399319589409437491 54908673598979384114156237)
  ·
    refine ⟨20590752599617269042808589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54908673598979384114156237 20590752599617269042808589)
    ·
      refine ⟨7721532224856475891053221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20590752599617269042808589 7721532224856475891053221)
      ·
        refine ⟨1447787292160589229572479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7721532224856475891053221 1447787292160589229572479)
        ·
          refine ⟨2171680938240883844358719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447787292160589229572479 2171680938240883844358719)
          ·
            refine ⟨3257521407361325766538079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171680938240883844358719 3257521407361325766538079)
            ·
              refine ⟨4886282111041988649807119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3257521407361325766538079 4886282111041988649807119)
              ·
                refine ⟨7329423166562982974710679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4886282111041988649807119 7329423166562982974710679)
                ·
                  refine ⟨10994134749844474462066019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7329423166562982974710679 10994134749844474462066019)
                  ·
                    refine ⟨16491202124766711693099029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10994134749844474462066019 16491202124766711693099029)
                    ·
                      refine ⟨773025099598439610614017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16491202124766711693099029 773025099598439610614017)
                      ·
                        rfl

theorem cell23_1505461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1505461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505461 prefixEnd_1505461 := by exact prefixLift 1505461
  have htrace : WordTrace (prefixWord ++ tailWord_1505461) baseStart_1505461 baseEnd_1505461 := by
    simpa [prefixWord, tailWord_1505461, baseEnd_1505461] using wordTrace_append hprefix tailTrace_1505461
  have hstable : (prefixWord ++ tailWord_1505461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505461).length < 2 ^ (prefixWord ++ tailWord_1505461).sum := by decide
  have hdescent : baseEnd_1505461 < baseStart_1505461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505468 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_1505468 : Nat := 118140960795 + 1505468 * 2 ^ 59
def prefixEnd_1505468 : Nat := 4983230072969 + 3 ^ 40 * 1505468 * 2
def baseEnd_1505468 : Nat := 773028693963021083226485

theorem tailTrace_1505468 : CollatzResearch.WordTrace tailWord_1505468 prefixEnd_1505468 773028693963021083226485 := by
  unfold tailWord_1505468
  simp only [CollatzResearch.WordTrace]
  refine ⟨27454464454977012154830529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36605952606636016206440705 27454464454977012154830529)
  ·
    refine ⟨20590848341232759116122897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27454464454977012154830529 20590848341232759116122897)
    ·
      refine ⟨15443136255924569337092173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20590848341232759116122897 15443136255924569337092173)
      ·
        refine ⟨5791176095971713501409565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15443136255924569337092173 5791176095971713501409565)
        ·
          refine ⟨2171691035989392563028587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5791176095971713501409565 2171691035989392563028587)
          ·
            refine ⟨3257536553984088844542881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171691035989392563028587 3257536553984088844542881)
            ·
              refine ⟨2443152415488066633407161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3257536553984088844542881 2443152415488066633407161)
              ·
                refine ⟨1832364311616049975055371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2443152415488066633407161 1832364311616049975055371)
                ·
                  refine ⟨2748546467424074962583057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832364311616049975055371 2748546467424074962583057)
                  ·
                    refine ⟨2061409850568056221937293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2748546467424074962583057 2061409850568056221937293)
                    ·
                      refine ⟨773028693963021083226485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2061409850568056221937293 773028693963021083226485)
                      ·
                        rfl

theorem cell23_1505468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_1505468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505468 prefixEnd_1505468 := by exact prefixLift 1505468
  have htrace : WordTrace (prefixWord ++ tailWord_1505468) baseStart_1505468 baseEnd_1505468 := by
    simpa [prefixWord, tailWord_1505468, baseEnd_1505468] using wordTrace_append hprefix tailTrace_1505468
  have hstable : (prefixWord ++ tailWord_1505468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505468).length < 2 ^ (prefixWord ++ tailWord_1505468).sum := by decide
  have hdescent : baseEnd_1505468 < baseStart_1505468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505477 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_1505477 : Nat := 118140960795 + 1505477 * 2 ^ 59
def prefixEnd_1505477 : Nat := 4983230072969 + 3 ^ 40 * 1505477 * 2
def baseEnd_1505477 : Nat := 773033315288911548013943

theorem tailTrace_1505477 : CollatzResearch.WordTrace tailWord_1505477 prefixEnd_1505477 773033315288911548013943 := by
  unfold tailWord_1505477
  simp only [CollatzResearch.WordTrace]
  refine ⟨54909257166921418846738685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36606171444614279231159123 54909257166921418846738685)
  ·
    refine ⟨20590971437595532067527007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54909257166921418846738685 20590971437595532067527007)
    ·
      refine ⟨30886457156393298101290511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20590971437595532067527007 30886457156393298101290511)
      ·
        refine ⟨46329685734589947151935767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30886457156393298101290511 46329685734589947151935767)
        ·
          refine ⟨69494528601884920727903651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46329685734589947151935767 69494528601884920727903651)
          ·
            refine ⟨104241792902827381091855477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69494528601884920727903651 104241792902827381091855477)
            ·
              refine ⟨9772668084640066977361451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104241792902827381091855477 9772668084640066977361451)
              ·
                refine ⟨14659002126960100466042177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9772668084640066977361451 14659002126960100466042177)
                ·
                  refine ⟨10994251595220075349531633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14659002126960100466042177 10994251595220075349531633)
                  ·
                    refine ⟨8245688696415056512148725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10994251595220075349531633 8245688696415056512148725)
                    ·
                      refine ⟨773033315288911548013943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8245688696415056512148725 773033315288911548013943)
                      ·
                        rfl

theorem cell23_1505477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_1505477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505477 prefixEnd_1505477 := by exact prefixLift 1505477
  have htrace : WordTrace (prefixWord ++ tailWord_1505477) baseStart_1505477 baseEnd_1505477 := by
    simpa [prefixWord, tailWord_1505477, baseEnd_1505477] using wordTrace_append hprefix tailTrace_1505477
  have hstable : (prefixWord ++ tailWord_1505477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505477).length < 2 ^ (prefixWord ++ tailWord_1505477).sum := by decide
  have hdescent : baseEnd_1505477 < baseStart_1505477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505497 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 4, 6]
def baseStart_1505497 : Nat := 118140960795 + 1505497 * 2 ^ 59
def prefixEnd_1505497 : Nat := 4983230072969 + 3 ^ 40 * 1505497 * 2
def baseEnd_1505497 : Nat := 257681194967333823254617

theorem tailTrace_1505497 : CollatzResearch.WordTrace tailWord_1505497 prefixEnd_1505497 257681194967333823254617 := by
  unfold tailWord_1505497
  simp only [CollatzResearch.WordTrace]
  refine ⟨54909986626848962262466745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36606657751232641508311163 54909986626848962262466745)
  ·
    refine ⟨41182489970136721696850059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54909986626848962262466745 41182489970136721696850059)
    ·
      refine ⟨61773734955205082545275089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41182489970136721696850059 61773734955205082545275089)
      ·
        refine ⟨46330301216403811908956317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61773734955205082545275089 46330301216403811908956317)
        ·
          refine ⟨17373862956151429465858619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46330301216403811908956317 17373862956151429465858619)
          ·
            refine ⟨26060794434227144198787929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17373862956151429465858619 26060794434227144198787929)
            ·
              refine ⟨19545595825670358149090947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26060794434227144198787929 19545595825670358149090947)
              ·
                refine ⟨29318393738505537223636421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19545595825670358149090947 29318393738505537223636421)
                ·
                  refine ⟨5497198825969788229431829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29318393738505537223636421 5497198825969788229431829)
                  ·
                    refine ⟨257681194967333823254617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5497198825969788229431829 257681194967333823254617)
                    ·
                      rfl

theorem cell23_1505497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_1505497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505497 prefixEnd_1505497 := by exact prefixLift 1505497
  have htrace : WordTrace (prefixWord ++ tailWord_1505497) baseStart_1505497 baseEnd_1505497 := by
    simpa [prefixWord, tailWord_1505497, baseEnd_1505497] using wordTrace_append hprefix tailTrace_1505497
  have hstable : (prefixWord ++ tailWord_1505497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505497).length < 2 ^ (prefixWord ++ tailWord_1505497).sum := by decide
  have hdescent : baseEnd_1505497 < baseStart_1505497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505538 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_1505538 : Nat := 118140960795 + 1505538 * 2 ^ 59
def prefixEnd_1505538 : Nat := 4983230072969 + 3 ^ 40 * 1505538 * 2
def baseEnd_1505538 : Nat := 773064637608835809351163

theorem tailTrace_1505538 : CollatzResearch.WordTrace tailWord_1505538 prefixEnd_1505538 773064637608835809351163 := by
  unfold tailWord_1505538
  simp only [CollatzResearch.WordTrace]
  refine ⟨13727870504925106566177317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36607654679800284176472845 13727870504925106566177317)
  ·
    refine ⟨2573975719673457481158247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13727870504925106566177317 2573975719673457481158247)
    ·
      refine ⟨3860963579510186221737371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2573975719673457481158247 3860963579510186221737371)
      ·
        refine ⟨5791445369265279332606057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3860963579510186221737371 5791445369265279332606057)
        ·
          refine ⟨4343584026948959499454543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5791445369265279332606057 4343584026948959499454543)
          ·
            refine ⟨6515376040423439249181815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4343584026948959499454543 6515376040423439249181815)
            ·
              refine ⟨9773064060635158873772723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6515376040423439249181815 9773064060635158873772723)
              ·
                refine ⟨14659596090952738310659085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9773064060635158873772723 14659596090952738310659085)
                ·
                  refine ⟨5497348534107276866497157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14659596090952738310659085 5497348534107276866497157)
                  ·
                    refine ⟨1030752850145114412468217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5497348534107276866497157 1030752850145114412468217)
                    ·
                      refine ⟨773064637608835809351163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030752850145114412468217 773064637608835809351163)
                      ·
                        rfl

theorem cell23_1505538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_1505538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505538 prefixEnd_1505538 := by exact prefixLift 1505538
  have htrace : WordTrace (prefixWord ++ tailWord_1505538) baseStart_1505538 baseEnd_1505538 := by
    simpa [prefixWord, tailWord_1505538, baseEnd_1505538] using wordTrace_append hprefix tailTrace_1505538
  have hstable : (prefixWord ++ tailWord_1505538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505538).length < 2 ^ (prefixWord ++ tailWord_1505538).sum := by decide
  have hdescent : baseEnd_1505538 < baseStart_1505538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505577 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_1505577 : Nat := 118140960795 + 1505577 * 2 ^ 59
def prefixEnd_1505577 : Nat := 4983230072969 + 3 ^ 40 * 1505577 * 2
def baseEnd_1505577 : Nat := 773084663354361156763483

theorem tailTrace_1505577 : CollatzResearch.WordTrace tailWord_1505577 prefixEnd_1505577 773084663354361156763483 := by
  unfold tailWord_1505577
  simp only [CollatzResearch.WordTrace]
  refine ⟨54912904466559135925378985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36608602977706090616919323 54912904466559135925378985)
  ·
    refine ⟨41184678349919351944034239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54912904466559135925378985 41184678349919351944034239)
    ·
      refine ⟨61777017524879027916051359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41184678349919351944034239 61777017524879027916051359)
      ·
        refine ⟨92665526287318541874077039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61777017524879027916051359 92665526287318541874077039)
        ·
          refine ⟨138998289430977812811115559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92665526287318541874077039 138998289430977812811115559)
          ·
            refine ⟨208497434146466719216673339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138998289430977812811115559 208497434146466719216673339)
            ·
              refine ⟨312746151219700078825010009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208497434146466719216673339 312746151219700078825010009)
              ·
                refine ⟨234559613414775059118757507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312746151219700078825010009 234559613414775059118757507)
                ·
                  refine ⟨351839420122162588678136261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234559613414775059118757507 351839420122162588678136261)
                  ·
                    refine ⟨65969891272905485377150549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 351839420122162588678136261 65969891272905485377150549)
                    ·
                      refine ⟨773084663354361156763483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 65969891272905485377150549 773084663354361156763483)
                      ·
                        rfl

theorem cell23_1505577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_1505577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505577 prefixEnd_1505577 := by exact prefixLift 1505577
  have htrace : WordTrace (prefixWord ++ tailWord_1505577) baseStart_1505577 baseEnd_1505577 := by
    simpa [prefixWord, tailWord_1505577, baseEnd_1505577] using wordTrace_append hprefix tailTrace_1505577
  have hstable : (prefixWord ++ tailWord_1505577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505577).length < 2 ^ (prefixWord ++ tailWord_1505577).sum := by decide
  have hdescent : baseEnd_1505577 < baseStart_1505577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505664 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 7, 5]
def baseStart_1505664 : Nat := 118140960795 + 1505664 * 2 ^ 59
def prefixEnd_1505664 : Nat := 4983230072969 + 3 ^ 40 * 1505664 * 2
def baseEnd_1505664 : Nat := 257709778723767438791861

theorem tailTrace_1505664 : CollatzResearch.WordTrace tailWord_1505664 prefixEnd_1505664 257709778723767438791861 := by
  unfold tailWord_1505664
  simp only [CollatzResearch.WordTrace]
  refine ⟨27458038808621974891898023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36610718411495966522530697 27458038808621974891898023)
  ·
    refine ⟨41187058212932962337847035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27458038808621974891898023 41187058212932962337847035)
    ·
      refine ⟨61780587319399443506770553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41187058212932962337847035 61780587319399443506770553)
      ·
        refine ⟨46335440489549582630077915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61780587319399443506770553 46335440489549582630077915)
        ·
          refine ⟨69503160734324373945116873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46335440489549582630077915 69503160734324373945116873)
          ·
            refine ⟨52127370550743280458837655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69503160734324373945116873 52127370550743280458837655)
            ·
              refine ⟨78191055826114920688256483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52127370550743280458837655 78191055826114920688256483)
              ·
                refine ⟨117286583739172381032384725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78191055826114920688256483 117286583739172381032384725)
                ·
                  refine ⟨2748904306386852680446517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 117286583739172381032384725 2748904306386852680446517)
                  ·
                    refine ⟨257709778723767438791861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2748904306386852680446517 257709778723767438791861)
                    ·
                      rfl

theorem cell23_1505664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_1505664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505664 prefixEnd_1505664 := by exact prefixLift 1505664
  have htrace : WordTrace (prefixWord ++ tailWord_1505664) baseStart_1505664 baseEnd_1505664 := by
    simpa [prefixWord, tailWord_1505664, baseEnd_1505664] using wordTrace_append hprefix tailTrace_1505664
  have hstable : (prefixWord ++ tailWord_1505664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505664).length < 2 ^ (prefixWord ++ tailWord_1505664).sum := by decide
  have hdescent : baseEnd_1505664 < baseStart_1505664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505701 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_1505701 : Nat := 118140960795 + 1505701 * 2 ^ 59
def prefixEnd_1505701 : Nat := 4983230072969 + 3 ^ 40 * 1505701 * 2
def baseEnd_1505701 : Nat := 773148334955518671612913

theorem tailTrace_1505701 : CollatzResearch.WordTrace tailWord_1505701 prefixEnd_1505701 773148334955518671612913 := by
  unfold tailWord_1505701
  simp only [CollatzResearch.WordTrace]
  refine ⟨54917427118109905102892957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36611618078739936735261971 54917427118109905102892957)
  ·
    refine ⟨20594035169291214413584859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54917427118109905102892957 20594035169291214413584859)
    ·
      refine ⟨30891052753936821620377289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20594035169291214413584859 30891052753936821620377289)
      ·
        refine ⟨23168289565452616215282967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30891052753936821620377289 23168289565452616215282967)
        ·
          refine ⟨34752434348178924322924451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23168289565452616215282967 34752434348178924322924451)
          ·
            refine ⟨52128651522268386484386677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34752434348178924322924451 52128651522268386484386677)
            ·
              refine ⟨4887061080212661232911251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52128651522268386484386677 4887061080212661232911251)
              ·
                refine ⟨7330591620318991849366877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4887061080212661232911251 7330591620318991849366877)
                ·
                  refine ⟨2748971857619621943512579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7330591620318991849366877 2748971857619621943512579)
                  ·
                    refine ⟨4123457786429432915268869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2748971857619621943512579 4123457786429432915268869)
                    ·
                      refine ⟨773148334955518671612913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4123457786429432915268869 773148334955518671612913)
                      ·
                        rfl

theorem cell23_1505701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_1505701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505701 prefixEnd_1505701 := by exact prefixLift 1505701
  have htrace : WordTrace (prefixWord ++ tailWord_1505701) baseStart_1505701 baseEnd_1505701 := by
    simpa [prefixWord, tailWord_1505701, baseEnd_1505701] using wordTrace_append hprefix tailTrace_1505701
  have hstable : (prefixWord ++ tailWord_1505701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505701).length < 2 ^ (prefixWord ++ tailWord_1505701).sum := by decide
  have hdescent : baseEnd_1505701 < baseStart_1505701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505748 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1505748 : Nat := 118140960795 + 1505748 * 2 ^ 59
def prefixEnd_1505748 : Nat := 4983230072969 + 3 ^ 40 * 1505748 * 2
def baseEnd_1505748 : Nat := 773172468546279987725197

theorem tailTrace_1505748 : CollatzResearch.WordTrace tailWord_1505748 prefixEnd_1505748 773172468546279987725197 := by
  unfold tailWord_1505748
  simp only [CollatzResearch.WordTrace]
  refine ⟨27459570674469816064926949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36612760899293088086569265 27459570674469816064926949)
  ·
    refine ⟨5148669501463090512173803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27459570674469816064926949 5148669501463090512173803)
    ·
      refine ⟨7723004252194635768260705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5148669501463090512173803 7723004252194635768260705)
      ·
        refine ⟨5792253189145976826195529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7723004252194635768260705 5792253189145976826195529)
        ·
          refine ⟨4344189891859482619646647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5792253189145976826195529 4344189891859482619646647)
          ·
            refine ⟨6516284837789223929469971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4344189891859482619646647 6516284837789223929469971)
            ·
              refine ⟨9774427256683835894204957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6516284837789223929469971 9774427256683835894204957)
              ·
                refine ⟨3665410221256438460326859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9774427256683835894204957 3665410221256438460326859)
                ·
                  refine ⟨5498115331884657690490289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665410221256438460326859 5498115331884657690490289)
                  ·
                    refine ⟨4123586498913493267867717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5498115331884657690490289 4123586498913493267867717)
                    ·
                      refine ⟨773172468546279987725197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4123586498913493267867717 773172468546279987725197)
                      ·
                        rfl

theorem cell23_1505748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1505748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505748 prefixEnd_1505748 := by exact prefixLift 1505748
  have htrace : WordTrace (prefixWord ++ tailWord_1505748) baseStart_1505748 baseEnd_1505748 := by
    simpa [prefixWord, tailWord_1505748, baseEnd_1505748] using wordTrace_append hprefix tailTrace_1505748
  have hstable : (prefixWord ++ tailWord_1505748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505748).length < 2 ^ (prefixWord ++ tailWord_1505748).sum := by decide
  have hdescent : baseEnd_1505748 < baseStart_1505748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505768 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_1505768 : Nat := 118140960795 + 1505768 * 2 ^ 59
def prefixEnd_1505768 : Nat := 4983230072969 + 3 ^ 40 * 1505768 * 2
def baseEnd_1505768 : Nat := 773182738159369909475105

theorem tailTrace_1505768 : CollatzResearch.WordTrace tailWord_1505768 prefixEnd_1505768 773182738159369909475105 := by
  unfold tailWord_1505768
  simp only [CollatzResearch.WordTrace]
  refine ⟨27459935404433587772790979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36613247205911450363721305 27459935404433587772790979)
  ·
    refine ⟨41189903106650381659186469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27459935404433587772790979 41189903106650381659186469)
    ·
      refine ⟨7723106832496946561097463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41189903106650381659186469 7723106832496946561097463)
      ·
        refine ⟨11584660248745419841646195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7723106832496946561097463 11584660248745419841646195)
        ·
          refine ⟨17376990373118129762469293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11584660248745419841646195 17376990373118129762469293)
          ·
            refine ⟨6516371389919298660925985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17376990373118129762469293 6516371389919298660925985)
            ·
              refine ⟨4887278542439473995694489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6516371389919298660925985 4887278542439473995694489)
              ·
                refine ⟨3665458906829605496770867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4887278542439473995694489 3665458906829605496770867)
                ·
                  refine ⟨5498188360244408245156301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665458906829605496770867 5498188360244408245156301)
                  ·
                    refine ⟨2061820635091653091933613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5498188360244408245156301 2061820635091653091933613)
                    ·
                      refine ⟨773182738159369909475105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2061820635091653091933613 773182738159369909475105)
                      ·
                        rfl

theorem cell23_1505768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_1505768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505768 prefixEnd_1505768 := by exact prefixLift 1505768
  have htrace : WordTrace (prefixWord ++ tailWord_1505768) baseStart_1505768 baseEnd_1505768 := by
    simpa [prefixWord, tailWord_1505768, baseEnd_1505768] using wordTrace_append hprefix tailTrace_1505768
  have hstable : (prefixWord ++ tailWord_1505768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505768).length < 2 ^ (prefixWord ++ tailWord_1505768).sum := by decide
  have hdescent : baseEnd_1505768 < baseStart_1505768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505785 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 2, 1, 3]
def baseStart_1505785 : Nat := 118140960795 + 1505785 * 2 ^ 59
def prefixEnd_1505785 : Nat := 4983230072969 + 3 ^ 40 * 1505785 * 2
def baseEnd_1505785 : Nat := 773191467330496342962527

theorem tailTrace_1505785 : CollatzResearch.WordTrace tailWord_1505785 prefixEnd_1505785 773191467330496342962527 := by
  unfold tailWord_1505785
  simp only [CollatzResearch.WordTrace]
  refine ⟨54920490849805587448950809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36613660566537058299300539 54920490849805587448950809)
  ·
    refine ⟨41190368137354190586713107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54920490849805587448950809 41190368137354190586713107)
    ·
      refine ⟨61785552206031285880069661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41190368137354190586713107 61785552206031285880069661)
      ·
        refine ⟨23169582077261732205026123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61785552206031285880069661 23169582077261732205026123)
        ·
          refine ⟨34754373115892598307539185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23169582077261732205026123 34754373115892598307539185)
          ·
            refine ⟨26065779836919448730654389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34754373115892598307539185 26065779836919448730654389)
            ·
              refine ⟨2443666859711198318498849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26065779836919448730654389 2443666859711198318498849)
              ·
                refine ⟨1832750144783398738874137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2443666859711198318498849 1832750144783398738874137)
                ·
                  refine ⟨1374562608587549054155603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1832750144783398738874137 1374562608587549054155603)
                  ·
                    refine ⟨2061843912881323581233405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1374562608587549054155603 2061843912881323581233405)
                    ·
                      refine ⟨773191467330496342962527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2061843912881323581233405 773191467330496342962527)
                      ·
                        rfl

theorem cell23_1505785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_1505785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505785 prefixEnd_1505785 := by exact prefixLift 1505785
  have htrace : WordTrace (prefixWord ++ tailWord_1505785) baseStart_1505785 baseEnd_1505785 := by
    simpa [prefixWord, tailWord_1505785, baseEnd_1505785] using wordTrace_append hprefix tailTrace_1505785
  have hstable : (prefixWord ++ tailWord_1505785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505785).length < 2 ^ (prefixWord ++ tailWord_1505785).sum := by decide
  have hdescent : baseEnd_1505785 < baseStart_1505785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505802 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3]
def baseStart_1505802 : Nat := 118140960795 + 1505802 * 2 ^ 59
def prefixEnd_1505802 : Nat := 4983230072969 + 3 ^ 40 * 1505802 * 2
def baseEnd_1505802 : Nat := 773200196501622776449949

theorem tailTrace_1505802 : CollatzResearch.WordTrace tailWord_1505802 prefixEnd_1505802 773200196501622776449949 := by
  unfold tailWord_1505802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13730277722685999838079915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36614073927162666234879773 13730277722685999838079915)
  ·
    refine ⟨20595416584028999757119873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13730277722685999838079915 20595416584028999757119873)
    ·
      refine ⟨15446562438021749817839905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20595416584028999757119873 15446562438021749817839905)
      ·
        refine ⟨11584921828516312363379929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15446562438021749817839905 11584921828516312363379929)
        ·
          refine ⟨8688691371387234272534947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11584921828516312363379929 8688691371387234272534947)
          ·
            refine ⟨13033037057080851408802421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8688691371387234272534947 13033037057080851408802421)
            ·
              refine ⟨1221847224101329819575227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13033037057080851408802421 1221847224101329819575227)
              ·
                refine ⟨1832770836151994729362841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221847224101329819575227 1832770836151994729362841)
                ·
                  refine ⟨1374578127113996047022131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1832770836151994729362841 1374578127113996047022131)
                  ·
                    refine ⟨2061867190670994070533197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1374578127113996047022131 2061867190670994070533197)
                    ·
                      refine ⟨773200196501622776449949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2061867190670994070533197 773200196501622776449949)
                      ·
                        rfl

theorem cell23_1505802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_1505802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505802 prefixEnd_1505802 := by exact prefixLift 1505802
  have htrace : WordTrace (prefixWord ++ tailWord_1505802) baseStart_1505802 baseEnd_1505802 := by
    simpa [prefixWord, tailWord_1505802, baseEnd_1505802] using wordTrace_append hprefix tailTrace_1505802
  have hstable : (prefixWord ++ tailWord_1505802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505802).length < 2 ^ (prefixWord ++ tailWord_1505802).sum := by decide
  have hdescent : baseEnd_1505802 < baseStart_1505802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505811 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 5]
def baseStart_1505811 : Nat := 118140960795 + 1505811 * 2 ^ 59
def prefixEnd_1505811 : Nat := 4983230072969 + 3 ^ 40 * 1505811 * 2
def baseEnd_1505811 : Nat := 773204817827513241237407

theorem tailTrace_1505811 : CollatzResearch.WordTrace tailWord_1505811 prefixEnd_1505811 773204817827513241237407 := by
  unfold tailWord_1505811
  simp only [CollatzResearch.WordTrace]
  refine ⟨54921439147711393889397287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36614292765140929259598191 54921439147711393889397287)
  ·
    refine ⟨82382158721567090834095931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54921439147711393889397287 82382158721567090834095931)
    ·
      refine ⟨123573238082350636251143897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82382158721567090834095931 123573238082350636251143897)
      ·
        refine ⟨92679928561762977188357923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123573238082350636251143897 92679928561762977188357923)
        ·
          refine ⟨139019892842644465782536885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92679928561762977188357923 139019892842644465782536885)
          ·
            refine ⟨13033114953997918667112833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139019892842644465782536885 13033114953997918667112833)
            ·
              refine ⟨9774836215498439000334625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13033114953997918667112833 9774836215498439000334625)
              ·
                refine ⟨7331127161623829250250969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9774836215498439000334625 7331127161623829250250969)
                ·
                  refine ⟨5498345371217871937688227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7331127161623829250250969 5498345371217871937688227)
                  ·
                    refine ⟨8247518056826807906532341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5498345371217871937688227 8247518056826807906532341)
                    ·
                      refine ⟨773204817827513241237407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8247518056826807906532341 773204817827513241237407)
                      ·
                        rfl

theorem cell23_1505811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_1505811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505811 prefixEnd_1505811 := by exact prefixLift 1505811
  have htrace : WordTrace (prefixWord ++ tailWord_1505811) baseStart_1505811 baseEnd_1505811 := by
    simpa [prefixWord, tailWord_1505811, baseEnd_1505811] using wordTrace_append hprefix tailTrace_1505811
  have hstable : (prefixWord ++ tailWord_1505811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505811).length < 2 ^ (prefixWord ++ tailWord_1505811).sum := by decide
  have hdescent : baseEnd_1505811 < baseStart_1505811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505825 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 6, 2, 2]
def baseStart_1505825 : Nat := 118140960795 + 1505825 * 2 ^ 59
def prefixEnd_1505825 : Nat := 4983230072969 + 3 ^ 40 * 1505825 * 2
def baseEnd_1505825 : Nat := 773212006556676186462343

theorem tailTrace_1505825 : CollatzResearch.WordTrace tailWord_1505825 prefixEnd_1505825 773212006556676186462343 := by
  unfold tailWord_1505825
  simp only [CollatzResearch.WordTrace]
  refine ⟨54921949769660674280406929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36614633179773782853604619 54921949769660674280406929)
  ·
    refine ⟨41191462327245505710305197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54921949769660674280406929 41191462327245505710305197)
    ·
      refine ⟨15446798372717064641364449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41191462327245505710305197 15446798372717064641364449)
      ·
        refine ⟨11585098779537798481023337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15446798372717064641364449 11585098779537798481023337)
        ·
          refine ⟨8688824084653348860767503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11585098779537798481023337 8688824084653348860767503)
          ·
            refine ⟨13033236126980023291151255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8688824084653348860767503 13033236126980023291151255)
            ·
              refine ⟨19549854190470034936726883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13033236126980023291151255 19549854190470034936726883)
              ·
                refine ⟨29324781285705052405090325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19549854190470034936726883 29324781285705052405090325)
                ·
                  refine ⟨1374599122767424331488609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29324781285705052405090325 1374599122767424331488609)
                  ·
                    refine ⟨1030949342075568248616457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1374599122767424331488609 1030949342075568248616457)
                    ·
                      refine ⟨773212006556676186462343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1030949342075568248616457 773212006556676186462343)
                      ·
                        rfl

theorem cell23_1505825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_1505825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505825 prefixEnd_1505825 := by exact prefixLift 1505825
  have htrace : WordTrace (prefixWord ++ tailWord_1505825) baseStart_1505825 baseEnd_1505825 := by
    simpa [prefixWord, tailWord_1505825, baseEnd_1505825] using wordTrace_append hprefix tailTrace_1505825
  have hstable : (prefixWord ++ tailWord_1505825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505825).length < 2 ^ (prefixWord ++ tailWord_1505825).sum := by decide
  have hdescent : baseEnd_1505825 < baseStart_1505825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505925 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 3, 4]
def baseStart_1505925 : Nat := 118140960795 + 1505925 * 2 ^ 59
def prefixEnd_1505925 : Nat := 4983230072969 + 3 ^ 40 * 1505925 * 2
def baseEnd_1505925 : Nat := 257754451540708598403961

theorem tailTrace_1505925 : CollatzResearch.WordTrace tailWord_1505925 prefixEnd_1505925 257754451540708598403961 := by
  unfold tailWord_1505925
  simp only [CollatzResearch.WordTrace]
  refine ⟨54925597069298391359047229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36617064712865594239364819 54925597069298391359047229)
  ·
    refine ⟨20597098900986896759642711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54925597069298391359047229 20597098900986896759642711)
    ·
      refine ⟨30895648351480345139464067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20597098900986896759642711 30895648351480345139464067)
      ·
        refine ⟨46343472527220517709196101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30895648351480345139464067 46343472527220517709196101)
        ·
          refine ⟨8689401098853847070474269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46343472527220517709196101 8689401098853847070474269)
          ·
            refine ⟨3258525412070192651427851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8689401098853847070474269 3258525412070192651427851)
            ·
              refine ⟨4887788118105288977141777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258525412070192651427851 4887788118105288977141777)
              ·
                refine ⟨3665841088578966732856333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4887788118105288977141777 3665841088578966732856333)
                ·
                  refine ⟨1374690408217112524821125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3665841088578966732856333 1374690408217112524821125)
                  ·
                    refine ⟨257754451540708598403961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1374690408217112524821125 257754451540708598403961)
                    ·
                      rfl

theorem cell23_1505925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_1505925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505925 prefixEnd_1505925 := by exact prefixLift 1505925
  have htrace : WordTrace (prefixWord ++ tailWord_1505925) baseStart_1505925 baseEnd_1505925 := by
    simpa [prefixWord, tailWord_1505925, baseEnd_1505925] using wordTrace_append hprefix tailTrace_1505925
  have hstable : (prefixWord ++ tailWord_1505925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505925).length < 2 ^ (prefixWord ++ tailWord_1505925).sum := by decide
  have hdescent : baseEnd_1505925 < baseStart_1505925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505959 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1505959 : Nat := 118140960795 + 1505959 * 2 ^ 59
def prefixEnd_1505959 : Nat := 4983230072969 + 3 ^ 40 * 1505959 * 2
def baseEnd_1505959 : Nat := 257760270988126220728909

theorem tailTrace_1505959 : CollatzResearch.WordTrace tailWord_1505959 prefixEnd_1505959 257760270988126220728909 := by
  unfold tailWord_1505959
  simp only [CollatzResearch.WordTrace]
  refine ⟨54926837151175215165784931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36617891434116810110523287 54926837151175215165784931)
  ·
    refine ⟨82390255726762822748677397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54926837151175215165784931 82390255726762822748677397)
    ·
      refine ⟨3862043237192007316344253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82390255726762822748677397 3862043237192007316344253)
      ·
        refine ⟨1448266213947002743629095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3862043237192007316344253 1448266213947002743629095)
        ·
          refine ⟨2172399320920504115443643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448266213947002743629095 2172399320920504115443643)
          ·
            refine ⟨3258598981380756173165465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172399320920504115443643 3258598981380756173165465)
            ·
              refine ⟨2443949236035567129874099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3258598981380756173165465 2443949236035567129874099)
              ·
                refine ⟨3665923854053350694811149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443949236035567129874099 3665923854053350694811149)
                ·
                  refine ⟨1374721445270006510554181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3665923854053350694811149 1374721445270006510554181)
                  ·
                    refine ⟨257760270988126220728909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1374721445270006510554181 257760270988126220728909)
                    ·
                      rfl

theorem cell23_1505959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1505959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505959 prefixEnd_1505959 := by exact prefixLift 1505959
  have htrace : WordTrace (prefixWord ++ tailWord_1505959) baseStart_1505959 baseEnd_1505959 := by
    simpa [prefixWord, tailWord_1505959, baseEnd_1505959] using wordTrace_append hprefix tailTrace_1505959
  have hstable : (prefixWord ++ tailWord_1505959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505959).length < 2 ^ (prefixWord ++ tailWord_1505959).sum := by decide
  have hdescent : baseEnd_1505959 < baseStart_1505959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505982 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_1505982 : Nat := 118140960795 + 1505982 * 2 ^ 59
def prefixEnd_1505982 : Nat := 4983230072969 + 3 ^ 40 * 1505982 * 2
def baseEnd_1505982 : Nat := 773292623019432072199121

theorem tailTrace_1505982 : CollatzResearch.WordTrace tailWord_1505982 prefixEnd_1505982 773292623019432072199121 := by
  unfold tailWord_1505982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6865959503761486261734025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36618450686727926729248133 6865959503761486261734025)
  ·
    refine ⟨5149469627821114696300519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6865959503761486261734025 5149469627821114696300519)
    ·
      refine ⟨7724204441731672044450779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5149469627821114696300519 7724204441731672044450779)
      ·
        refine ⟨11586306662597508066676169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7724204441731672044450779 11586306662597508066676169)
        ·
          refine ⟨8689729996948131050007127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11586306662597508066676169 8689729996948131050007127)
          ·
            refine ⟨13034594995422196575010691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8689729996948131050007127 13034594995422196575010691)
            ·
              refine ⟨19551892493133294862516037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13034594995422196575010691 19551892493133294862516037)
              ·
                refine ⟨3665979842462492786721757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19551892493133294862516037 3665979842462492786721757)
                ·
                  refine ⟨1374742440923434795020659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3665979842462492786721757 1374742440923434795020659)
                  ·
                    refine ⟨2062113661385152192530989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1374742440923434795020659 2062113661385152192530989)
                    ·
                      refine ⟨773292623019432072199121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2062113661385152192530989 773292623019432072199121)
                      ·
                        rfl

theorem cell23_1505982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_1505982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1505982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1505982 prefixEnd_1505982 := by exact prefixLift 1505982
  have htrace : WordTrace (prefixWord ++ tailWord_1505982) baseStart_1505982 baseEnd_1505982 := by
    simpa [prefixWord, tailWord_1505982, baseEnd_1505982] using wordTrace_append hprefix tailTrace_1505982
  have hstable : (prefixWord ++ tailWord_1505982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505982).length < 2 ^ (prefixWord ++ tailWord_1505982).sum := by decide
  have hdescent : baseEnd_1505982 < baseStart_1505982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506015 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 4, 4]
def baseStart_1506015 : Nat := 118140960795 + 1506015 * 2 ^ 59
def prefixEnd_1506015 : Nat := 4983230072969 + 3 ^ 40 * 1506015 * 2
def baseEnd_1506015 : Nat := 257769855960343481028823

theorem tailTrace_1506015 : CollatzResearch.WordTrace tailWord_1506015 prefixEnd_1506015 257769855960343481028823 := by
  unfold tailWord_1506015
  simp only [CollatzResearch.WordTrace]
  refine ⟨54928879638972336729823499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36619253092648224486548999 54928879638972336729823499)
  ·
    refine ⟨82393319458458505094735249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54928879638972336729823499 82393319458458505094735249)
    ·
      refine ⟨61794989593843878821051437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82393319458458505094735249 61794989593843878821051437)
      ·
        refine ⟨23173121097691454557894289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61794989593843878821051437 23173121097691454557894289)
        ·
          refine ⟨17379840823268590918420717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23173121097691454557894289 17379840823268590918420717)
          ·
            refine ⟨6517440308725721594407769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17379840823268590918420717 6517440308725721594407769)
            ·
              refine ⟨4888080231544291195805827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6517440308725721594407769 4888080231544291195805827)
              ·
                refine ⟨7332120347316436793708741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888080231544291195805827 7332120347316436793708741)
                ·
                  refine ⟨1374772565121831898820389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7332120347316436793708741 1374772565121831898820389)
                  ·
                    refine ⟨257769855960343481028823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1374772565121831898820389 257769855960343481028823)
                    ·
                      rfl

theorem cell23_1506015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 4].length) (baseStart_1506015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506015 prefixEnd_1506015 := by exact prefixLift 1506015
  have htrace : WordTrace (prefixWord ++ tailWord_1506015) baseStart_1506015 baseEnd_1506015 := by
    simpa [prefixWord, tailWord_1506015, baseEnd_1506015] using wordTrace_append hprefix tailTrace_1506015
  have hstable : (prefixWord ++ tailWord_1506015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506015).length < 2 ^ (prefixWord ++ tailWord_1506015).sum := by decide
  have hdescent : baseEnd_1506015 < baseStart_1506015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506042 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3]
def baseStart_1506042 : Nat := 118140960795 + 1506042 * 2 ^ 59
def prefixEnd_1506042 : Nat := 4983230072969 + 3 ^ 40 * 1506042 * 2
def baseEnd_1506042 : Nat := 773323431858701837448845

theorem tailTrace_1506042 : CollatzResearch.WordTrace tailWord_1506042 prefixEnd_1506042 773323431858701837448845 := by
  unfold tailWord_1506042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13732466102468630085264095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36619909606583013560704253 13732466102468630085264095)
  ·
    refine ⟨20598699153702945127896143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13732466102468630085264095 20598699153702945127896143)
    ·
      refine ⟨30898048730554417691844215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20598699153702945127896143 30898048730554417691844215)
      ·
        refine ⟨46347073095831626537766323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30898048730554417691844215 46347073095831626537766323)
        ·
          refine ⟨69520609643747439806649485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46347073095831626537766323 69520609643747439806649485)
          ·
            refine ⟨26070228616405289927493557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69520609643747439806649485 26070228616405289927493557)
            ·
              refine ⟨2444083932787995930702521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26070228616405289927493557 2444083932787995930702521)
              ·
                refine ⟨1833062949590996948026891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2444083932787995930702521 1833062949590996948026891)
                ·
                  refine ⟨2749594424386495422040337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833062949590996948026891 2749594424386495422040337)
                  ·
                    refine ⟨2062195818289871566530253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2749594424386495422040337 2062195818289871566530253)
                    ·
                      refine ⟨773323431858701837448845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2062195818289871566530253 773323431858701837448845)
                      ·
                        rfl

theorem cell23_1506042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_1506042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506042 prefixEnd_1506042 := by exact prefixLift 1506042
  have htrace : WordTrace (prefixWord ++ tailWord_1506042) baseStart_1506042 baseEnd_1506042 := by
    simpa [prefixWord, tailWord_1506042, baseEnd_1506042] using wordTrace_append hprefix tailTrace_1506042
  have hstable : (prefixWord ++ tailWord_1506042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506042).length < 2 ^ (prefixWord ++ tailWord_1506042).sum := by decide
  have hdescent : baseEnd_1506042 < baseStart_1506042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506066 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1506066 : Nat := 118140960795 + 1506066 * 2 ^ 59
def prefixEnd_1506066 : Nat := 4983230072969 + 3 ^ 40 * 1506066 * 2
def baseEnd_1506066 : Nat := 257778585131469914516245

theorem tailTrace_1506066 : CollatzResearch.WordTrace tailWord_1506066 prefixEnd_1506066 257778585131469914516245 := by
  unfold tailWord_1506066
  simp only [CollatzResearch.WordTrace]
  refine ⟨13732684940446893109982513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36620493174525048293286701 13732684940446893109982513)
  ·
    refine ⟨10299513705335169832486885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13732684940446893109982513 10299513705335169832486885)
    ·
      refine ⟨1931158819750344343591291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10299513705335169832486885 1931158819750344343591291)
      ·
        refine ⟨2896738229625516515386937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1931158819750344343591291 2896738229625516515386937)
        ·
          refine ⟨2172553672219137386540203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2896738229625516515386937 2172553672219137386540203)
          ·
            refine ⟨3258830508328706079810305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172553672219137386540203 3258830508328706079810305)
            ·
              refine ⟨2444122881246529559857729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3258830508328706079810305 2444122881246529559857729)
              ·
                refine ⟨1833092160934897169893297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2444122881246529559857729 1833092160934897169893297)
                ·
                  refine ⟨1374819120701172877419973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1833092160934897169893297 1374819120701172877419973)
                  ·
                    refine ⟨257778585131469914516245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1374819120701172877419973 257778585131469914516245)
                    ·
                      rfl

theorem cell23_1506066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1506066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506066 prefixEnd_1506066 := by exact prefixLift 1506066
  have htrace : WordTrace (prefixWord ++ tailWord_1506066) baseStart_1506066 baseEnd_1506066 := by
    simpa [prefixWord, tailWord_1506066, baseEnd_1506066] using wordTrace_append hprefix tailTrace_1506066
  have hstable : (prefixWord ++ tailWord_1506066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506066).length < 2 ^ (prefixWord ++ tailWord_1506066).sum := by decide
  have hdescent : baseEnd_1506066 < baseStart_1506066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506135 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 7]
def baseStart_1506135 : Nat := 118140960795 + 1506135 * 2 ^ 59
def prefixEnd_1506135 : Nat := 4983230072969 + 3 ^ 40 * 1506135 * 2
def baseEnd_1506135 : Nat := 85930131728841108176213

theorem tailTrace_1506135 : CollatzResearch.WordTrace tailWord_1506135 prefixEnd_1506135 85930131728841108176213 := by
  unfold tailWord_1506135
  simp only [CollatzResearch.WordTrace]
  refine ⟨54933256398537597224191859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36622170932358398149461239 54933256398537597224191859)
  ·
    refine ⟨82399884597806395836287789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54933256398537597224191859 82399884597806395836287789)
    ·
      refine ⟨30899956724177398438607921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82399884597806395836287789 30899956724177398438607921)
      ·
        refine ⟨23174967543133048828955941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30899956724177398438607921 23174967543133048828955941)
        ·
          refine ⟨4345306414337446655429239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23174967543133048828955941 4345306414337446655429239)
          ·
            refine ⟨6517959621506169983143859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4345306414337446655429239 6517959621506169983143859)
            ·
              refine ⟨9776939432259254974715789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6517959621506169983143859 9776939432259254974715789)
              ·
                refine ⟨3666352287097220615518421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9776939432259254974715789 3666352287097220615518421)
                ·
                  refine ⟨85930131728841108176213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3666352287097220615518421 85930131728841108176213)
                  ·
                    rfl

theorem cell23_1506135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 7].length) (baseStart_1506135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506135 prefixEnd_1506135 := by exact prefixLift 1506135
  have htrace : WordTrace (prefixWord ++ tailWord_1506135) baseStart_1506135 baseEnd_1506135 := by
    simpa [prefixWord, tailWord_1506135, baseEnd_1506135] using wordTrace_append hprefix tailTrace_1506135
  have hstable : (prefixWord ++ tailWord_1506135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506135).length < 2 ^ (prefixWord ++ tailWord_1506135).sum := by decide
  have hdescent : baseEnd_1506135 < baseStart_1506135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506145 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_1506145 : Nat := 118140960795 + 1506145 * 2 ^ 59
def prefixEnd_1506145 : Nat := 4983230072969 + 3 ^ 40 * 1506145 * 2
def baseEnd_1506145 : Nat := 773376320366114934460871

theorem tailTrace_1506145 : CollatzResearch.WordTrace tailWord_1506145 prefixEnd_1506145 773376320366114934460871 := by
  unfold tailWord_1506145
  simp only [CollatzResearch.WordTrace]
  refine ⟨54933621128501368932055889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36622414085667579288037259 54933621128501368932055889)
  ·
    refine ⟨41200215846376026699041917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54933621128501368932055889 41200215846376026699041917)
    ·
      refine ⟨15450080942391010012140719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41200215846376026699041917 15450080942391010012140719)
      ·
        refine ⟨23175121413586515018211079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15450080942391010012140719 23175121413586515018211079)
        ·
          refine ⟨34762682120379772527316619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23175121413586515018211079 34762682120379772527316619)
          ·
            refine ⟨52144023180569658790974929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34762682120379772527316619 52144023180569658790974929)
            ·
              refine ⟨39108017385427244093231197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52144023180569658790974929 39108017385427244093231197)
              ·
                refine ⟨14665506519535216534961699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39108017385427244093231197 14665506519535216534961699)
                ·
                  refine ⟨21998259779302824802442549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14665506519535216534961699 21998259779302824802442549)
                  ·
                    refine ⟨2062336854309639825228989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21998259779302824802442549 2062336854309639825228989)
                    ·
                      refine ⟨773376320366114934460871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2062336854309639825228989 773376320366114934460871)
                      ·
                        rfl

theorem cell23_1506145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_1506145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506145 prefixEnd_1506145 := by exact prefixLift 1506145
  have htrace : WordTrace (prefixWord ++ tailWord_1506145) baseStart_1506145 baseEnd_1506145 := by
    simpa [prefixWord, tailWord_1506145, baseEnd_1506145] using wordTrace_append hprefix tailTrace_1506145
  have hstable : (prefixWord ++ tailWord_1506145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506145).length < 2 ^ (prefixWord ++ tailWord_1506145).sum := by decide
  have hdescent : baseEnd_1506145 < baseStart_1506145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506169 : List Nat := [1, 2, 1, 3, 2, 5, 1, 3, 5]
def baseStart_1506169 : Nat := 118140960795 + 1506169 * 2 ^ 59
def prefixEnd_1506169 : Nat := 4983230072969 + 3 ^ 40 * 1506169 * 2
def baseEnd_1506169 : Nat := 85932071544646982284529

theorem tailTrace_1506169 : CollatzResearch.WordTrace tailWord_1506169 prefixEnd_1506169 85932071544646982284529 := by
  unfold tailWord_1506169
  simp only [CollatzResearch.WordTrace]
  refine ⟨54934496480414421030929561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36622997653609614020619707 54934496480414421030929561)
  ·
    refine ⟨41200872360310815773197171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54934496480414421030929561 41200872360310815773197171)
    ·
      refine ⟨61801308540466223659795757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41200872360310815773197171 61801308540466223659795757)
      ·
        refine ⟨23175490702674833872423409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61801308540466223659795757 23175490702674833872423409)
        ·
          refine ⟨17381618027006125404317557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23175490702674833872423409 17381618027006125404317557)
          ·
            refine ⟨1629526690031824256654771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17381618027006125404317557 1629526690031824256654771)
            ·
              refine ⟨2444290035047736384982157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629526690031824256654771 2444290035047736384982157)
              ·
                refine ⟨916608763142901144368309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2444290035047736384982157 916608763142901144368309)
                ·
                  refine ⟨85932071544646982284529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 916608763142901144368309 85932071544646982284529)
                  ·
                    rfl

theorem cell23_1506169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 5].length) (baseStart_1506169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506169 prefixEnd_1506169 := by exact prefixLift 1506169
  have htrace : WordTrace (prefixWord ++ tailWord_1506169) baseStart_1506169 baseEnd_1506169 := by
    simpa [prefixWord, tailWord_1506169, baseEnd_1506169] using wordTrace_append hprefix tailTrace_1506169
  have hstable : (prefixWord ++ tailWord_1506169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506169).length < 2 ^ (prefixWord ++ tailWord_1506169).sum := by decide
  have hdescent : baseEnd_1506169 < baseStart_1506169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506186 : List Nat := [3, 1, 2, 4, 1, 2, 3, 2, 5]
def baseStart_1506186 : Nat := 118140960795 + 1506186 * 2 ^ 59
def prefixEnd_1506186 : Nat := 4983230072969 + 3 ^ 40 * 1506186 * 2
def baseEnd_1506186 : Nat := 85933041452549919338687

theorem tailTrace_1506186 : CollatzResearch.WordTrace tailWord_1506186 prefixEnd_1506186 85933041452549919338687 := by
  unfold tailWord_1506186
  simp only [CollatzResearch.WordTrace]
  refine ⟨13733779130338208233574603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36623411014235221956198941 13733779130338208233574603)
  ·
    refine ⟨20600668695507312350361905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13733779130338208233574603 20600668695507312350361905)
    ·
      refine ⟨15450501521630484262771429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20600668695507312350361905 15450501521630484262771429)
      ·
        refine ⟨2896969035305715799269643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15450501521630484262771429 2896969035305715799269643)
        ·
          refine ⟨4345453552958573698904465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896969035305715799269643 4345453552958573698904465)
          ·
            refine ⟨3259090164718930274178349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4345453552958573698904465 3259090164718930274178349)
            ·
              refine ⟨1222158811769598852816881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3259090164718930274178349 1222158811769598852816881)
              ·
                refine ⟨916619108827199139612661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222158811769598852816881 916619108827199139612661)
                ·
                  refine ⟨85933041452549919338687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 916619108827199139612661 85933041452549919338687)
                  ·
                    rfl

theorem cell23_1506186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_1506186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506186 prefixEnd_1506186 := by exact prefixLift 1506186
  have htrace : WordTrace (prefixWord ++ tailWord_1506186) baseStart_1506186 baseEnd_1506186 := by
    simpa [prefixWord, tailWord_1506186, baseEnd_1506186] using wordTrace_append hprefix tailTrace_1506186
  have hstable : (prefixWord ++ tailWord_1506186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506186).length < 2 ^ (prefixWord ++ tailWord_1506186).sum := by decide
  have hdescent : baseEnd_1506186 < baseStart_1506186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506212 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_1506212 : Nat := 118140960795 + 1506212 * 2 ^ 59
def prefixEnd_1506212 : Nat := 4983230072969 + 3 ^ 40 * 1506212 * 2
def baseEnd_1506212 : Nat := 257803574523322057441021

theorem tailTrace_1506212 : CollatzResearch.WordTrace tailWord_1506212 prefixEnd_1506212 257803574523322057441021 := by
  unfold tailWord_1506212
  simp only [CollatzResearch.WordTrace]
  refine ⟨27468032409629319687372445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36624043212839092916496593 27468032409629319687372445)
  ·
    refine ⟨10300512153610994882764667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27468032409629319687372445 10300512153610994882764667)
    ·
      refine ⟨15450768230416492324147001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10300512153610994882764667 15450768230416492324147001)
      ·
        refine ⟨11588076172812369243110251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15450768230416492324147001 11588076172812369243110251)
        ·
          refine ⟨17382114259218553864665377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11588076172812369243110251 17382114259218553864665377)
          ·
            refine ⟨13036585694413915398499033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17382114259218553864665377 13036585694413915398499033)
            ·
              refine ⟨9777439270810436548874275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13036585694413915398499033 9777439270810436548874275)
              ·
                refine ⟨14666158906215654823311413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9777439270810436548874275 14666158906215654823311413)
                ·
                  refine ⟨1374952397457717639685445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14666158906215654823311413 1374952397457717639685445)
                  ·
                    refine ⟨257803574523322057441021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1374952397457717639685445 257803574523322057441021)
                    ·
                      rfl

theorem cell23_1506212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_1506212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506212 prefixEnd_1506212 := by exact prefixLift 1506212
  have htrace : WordTrace (prefixWord ++ tailWord_1506212) baseStart_1506212 baseEnd_1506212 := by
    simpa [prefixWord, tailWord_1506212, baseEnd_1506212] using wordTrace_append hprefix tailTrace_1506212
  have hstable : (prefixWord ++ tailWord_1506212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506212).length < 2 ^ (prefixWord ++ tailWord_1506212).sum := by decide
  have hdescent : baseEnd_1506212 < baseStart_1506212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506289 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 1, 5]
def baseStart_1506289 : Nat := 118140960795 + 1506289 * 2 ^ 59
def prefixEnd_1506289 : Nat := 4983230072969 + 3 ^ 40 * 1506289 * 2
def baseEnd_1506289 : Nat := 257816753860120790353403

theorem tailTrace_1506289 : CollatzResearch.WordTrace tailWord_1506289 prefixEnd_1506289 257816753860120790353403 := by
  unfold tailWord_1506289
  simp only [CollatzResearch.WordTrace]
  refine ⟨54938873239979681525297921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36625915493319787683531947 54938873239979681525297921)
  ·
    refine ⟨41204154929984761143973441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54938873239979681525297921 41204154929984761143973441)
    ·
      refine ⟨30903116197488570857980081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41204154929984761143973441 30903116197488570857980081)
      ·
        refine ⟨23177337148116428143485061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30903116197488570857980081 23177337148116428143485061)
        ·
          refine ⟨4345750715271830276903449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23177337148116428143485061 4345750715271830276903449)
          ·
            refine ⟨3259313036453872707677587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4345750715271830276903449 3259313036453872707677587)
            ·
              refine ⟨4888969554680809061516381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3259313036453872707677587 4888969554680809061516381)
              ·
                refine ⟨1833363583005303398068643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4888969554680809061516381 1833363583005303398068643)
                ·
                  refine ⟨2750045374507955097102965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833363583005303398068643 2750045374507955097102965)
                  ·
                    refine ⟨257816753860120790353403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2750045374507955097102965 257816753860120790353403)
                    ·
                      rfl

theorem cell23_1506289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_1506289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506289 prefixEnd_1506289 := by exact prefixLift 1506289
  have htrace : WordTrace (prefixWord ++ tailWord_1506289) baseStart_1506289 baseEnd_1506289 := by
    simpa [prefixWord, tailWord_1506289, baseEnd_1506289] using wordTrace_append hprefix tailTrace_1506289
  have hstable : (prefixWord ++ tailWord_1506289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506289).length < 2 ^ (prefixWord ++ tailWord_1506289).sum := by decide
  have hdescent : baseEnd_1506289 < baseStart_1506289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506293 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 6]
def baseStart_1506293 : Nat := 118140960795 + 1506293 * 2 ^ 59
def prefixEnd_1506293 : Nat := 4983230072969 + 3 ^ 40 * 1506293 * 2
def baseEnd_1506293 : Nat := 85939146166997817267799

theorem tailTrace_1506293 : CollatzResearch.WordTrace tailWord_1506293 prefixEnd_1506293 85939146166997817267799 := by
  unfold tailWord_1506293
  simp only [CollatzResearch.WordTrace]
  refine ⟨54939019131965190208443533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36626012754643460138962355 54939019131965190208443533)
  ·
    refine ⟨20602132174486946328166325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54939019131965190208443533 20602132174486946328166325)
    ·
      refine ⟨1931449891358151218265593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20602132174486946328166325 1931449891358151218265593)
      ·
        refine ⟨1448587418518613413699195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1931449891358151218265593 1448587418518613413699195)
        ·
          refine ⟨2172881127777920120548793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448587418518613413699195 2172881127777920120548793)
          ·
            refine ⟨1629660845833440090411595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2172881127777920120548793 1629660845833440090411595)
            ·
              refine ⟨2444491268750160135617393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629660845833440090411595 2444491268750160135617393)
              ·
                refine ⟨1833368451562620101713045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2444491268750160135617393 1833368451562620101713045)
                ·
                  refine ⟨85939146166997817267799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1833368451562620101713045 85939146166997817267799)
                  ·
                    rfl

theorem cell23_1506293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_1506293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506293 prefixEnd_1506293 := by exact prefixLift 1506293
  have htrace : WordTrace (prefixWord ++ tailWord_1506293) baseStart_1506293 baseEnd_1506293 := by
    simpa [prefixWord, tailWord_1506293, baseEnd_1506293] using wordTrace_append hprefix tailTrace_1506293
  have hstable : (prefixWord ++ tailWord_1506293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506293).length < 2 ^ (prefixWord ++ tailWord_1506293).sum := by decide
  have hdescent : baseEnd_1506293 < baseStart_1506293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506312 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_1506312 : Nat := 118140960795 + 1506312 * 2 ^ 59
def prefixEnd_1506312 : Nat := 4983230072969 + 3 ^ 40 * 1506312 * 2
def baseEnd_1506312 : Nat := 773462071635415781072603

theorem tailTrace_1506312 : CollatzResearch.WordTrace tailWord_1506312 prefixEnd_1506312 773462071635415781072603 := by
  unfold tailWord_1506312
  simp only [CollatzResearch.WordTrace]
  refine ⟨27469856059448178226692595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36626474745930904302256793 27469856059448178226692595)
  ·
    refine ⟨41204784089172267340038893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27469856059448178226692595 41204784089172267340038893)
    ·
      refine ⟨15451794033439600252514585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41204784089172267340038893 15451794033439600252514585)
      ·
        refine ⟨11588845525079700189385939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15451794033439600252514585 11588845525079700189385939)
        ·
          refine ⟨17383268287619550284078909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11588845525079700189385939 17383268287619550284078909)
          ·
            refine ⟨6518725607857331356529591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17383268287619550284078909 6518725607857331356529591)
            ·
              refine ⟨9778088411785997034794387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6518725607857331356529591 9778088411785997034794387)
              ·
                refine ⟨14667132617678995552191581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9778088411785997034794387 14667132617678995552191581)
                ·
                  refine ⟨5500174731629623332071843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14667132617678995552191581 5500174731629623332071843)
                  ·
                    refine ⟨8250262097444434998107765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5500174731629623332071843 8250262097444434998107765)
                    ·
                      refine ⟨773462071635415781072603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8250262097444434998107765 773462071635415781072603)
                      ·
                        rfl

theorem cell23_1506312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_1506312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506312 prefixEnd_1506312 := by exact prefixLift 1506312
  have htrace : WordTrace (prefixWord ++ tailWord_1506312) baseStart_1506312 baseEnd_1506312 := by
    simpa [prefixWord, tailWord_1506312, baseEnd_1506312] using wordTrace_append hprefix tailTrace_1506312
  have hstable : (prefixWord ++ tailWord_1506312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506312).length < 2 ^ (prefixWord ++ tailWord_1506312).sum := by decide
  have hdescent : baseEnd_1506312 < baseStart_1506312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506329 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 1, 2, 3]
def baseStart_1506329 : Nat := 118140960795 + 1506329 * 2 ^ 59
def prefixEnd_1506329 : Nat := 4983230072969 + 3 ^ 40 * 1506329 * 2
def baseEnd_1506329 : Nat := 773470800806542214560025

theorem tailTrace_1506329 : CollatzResearch.WordTrace tailWord_1506329 prefixEnd_1506329 773470800806542214560025 := by
  unfold tailWord_1506329
  simp only [CollatzResearch.WordTrace]
  refine ⟨54940332159834768356754041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36626888106556512237836027 54940332159834768356754041)
  ·
    refine ⟨41205249119876076267565531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54940332159834768356754041 41205249119876076267565531)
    ·
      refine ⟨61807873679814114401348297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41205249119876076267565531 61807873679814114401348297)
      ·
        refine ⟨46355905259860585801011223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61807873679814114401348297 46355905259860585801011223)
        ·
          refine ⟨69533857889790878701516835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46355905259860585801011223 69533857889790878701516835)
          ·
            refine ⟨104300786834686318052275253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69533857889790878701516835 104300786834686318052275253)
            ·
              refine ⟨9778198765751842317400805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104300786834686318052275253 9778198765751842317400805)
              ·
                refine ⟨1833412268578470434512651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9778198765751842317400805 1833412268578470434512651)
                ·
                  refine ⟨2750118402867705651768977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833412268578470434512651 2750118402867705651768977)
                  ·
                    refine ⟨2062588802150779238826733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2750118402867705651768977 2062588802150779238826733)
                    ·
                      refine ⟨773470800806542214560025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2062588802150779238826733 773470800806542214560025)
                      ·
                        rfl

theorem cell23_1506329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_1506329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506329 prefixEnd_1506329 := by exact prefixLift 1506329
  have htrace : WordTrace (prefixWord ++ tailWord_1506329) baseStart_1506329 baseEnd_1506329 := by
    simpa [prefixWord, tailWord_1506329, baseEnd_1506329] using wordTrace_append hprefix tailTrace_1506329
  have hstable : (prefixWord ++ tailWord_1506329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506329).length < 2 ^ (prefixWord ++ tailWord_1506329).sum := by decide
  have hdescent : baseEnd_1506329 < baseStart_1506329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506346 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1506346 : Nat := 118140960795 + 1506346 * 2 ^ 59
def prefixEnd_1506346 : Nat := 4983230072969 + 3 ^ 40 * 1506346 * 2
def baseEnd_1506346 : Nat := 773479529977668648047447

theorem tailTrace_1506346 : CollatzResearch.WordTrace tailWord_1506346 prefixEnd_1506346 773479529977668648047447 := by
  unfold tailWord_1506346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13735238050193295065030723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36627301467182120173415261 13735238050193295065030723)
  ·
    refine ⟨20602857075289942597546085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13735238050193295065030723 20602857075289942597546085)
    ·
      refine ⟨3863035701616864237039891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20602857075289942597546085 3863035701616864237039891)
      ·
        refine ⟨5794553552425296355559837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3863035701616864237039891 5794553552425296355559837)
        ·
          refine ⟨2172957582159486133334939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5794553552425296355559837 2172957582159486133334939)
          ·
            refine ⟨3259436373239229200002409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172957582159486133334939 3259436373239229200002409)
            ·
              refine ⟨2444577279929421900001807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3259436373239229200002409 2444577279929421900001807)
              ·
                refine ⟨3666865919894132850002711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444577279929421900001807 3666865919894132850002711)
                ·
                  refine ⟨5500298879841199275004067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3666865919894132850002711 5500298879841199275004067)
                  ·
                    refine ⟨8250448319761798912506101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5500298879841199275004067 8250448319761798912506101)
                    ·
                      refine ⟨773479529977668648047447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8250448319761798912506101 773479529977668648047447)
                      ·
                        rfl

theorem cell23_1506346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1506346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506346 prefixEnd_1506346 := by exact prefixLift 1506346
  have htrace : WordTrace (prefixWord ++ tailWord_1506346) baseStart_1506346 baseEnd_1506346 := by
    simpa [prefixWord, tailWord_1506346, baseEnd_1506346] using wordTrace_append hprefix tailTrace_1506346
  have hstable : (prefixWord ++ tailWord_1506346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506346).length < 2 ^ (prefixWord ++ tailWord_1506346).sum := by decide
  have hdescent : baseEnd_1506346 < baseStart_1506346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506376 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_1506376 : Nat := 118140960795 + 1506376 * 2 ^ 59
def prefixEnd_1506376 : Nat := 4983230072969 + 3 ^ 40 * 1506376 * 2
def baseEnd_1506376 : Nat := 773494934397303530672309

theorem tailTrace_1506376 : CollatzResearch.WordTrace tailWord_1506376 prefixEnd_1506376 773494934397303530672309 := by
  unfold tailWord_1506376
  simp only [CollatzResearch.WordTrace]
  refine ⟨27471023195332247691857491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36628030927109663589143321 27471023195332247691857491)
  ·
    refine ⟨41206534792998371537786237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27471023195332247691857491 41206534792998371537786237)
    ·
      refine ⟨15452450547374389326669839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41206534792998371537786237 15452450547374389326669839)
      ·
        refine ⟨23178675821061583990004759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15452450547374389326669839 23178675821061583990004759)
        ·
          refine ⟨34768013731592375985007139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23178675821061583990004759 34768013731592375985007139)
          ·
            refine ⟨52152020597388563977510709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34768013731592375985007139 52152020597388563977510709)
            ·
              refine ⟨4889251931005177872891629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52152020597388563977510709 4889251931005177872891629)
              ·
                refine ⟨1833469474126941702334361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4889251931005177872891629 1833469474126941702334361)
                ·
                  refine ⟨1375102105595206276750771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1833469474126941702334361 1375102105595206276750771)
                  ·
                    refine ⟨2062653158392809415126157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1375102105595206276750771 2062653158392809415126157)
                    ·
                      refine ⟨773494934397303530672309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2062653158392809415126157 773494934397303530672309)
                      ·
                        rfl

theorem cell23_1506376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_1506376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506376 prefixEnd_1506376 := by exact prefixLift 1506376
  have htrace : WordTrace (prefixWord ++ tailWord_1506376) baseStart_1506376 baseEnd_1506376 := by
    simpa [prefixWord, tailWord_1506376, baseEnd_1506376] using wordTrace_append hprefix tailTrace_1506376
  have hstable : (prefixWord ++ tailWord_1506376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506376).length < 2 ^ (prefixWord ++ tailWord_1506376).sum := by decide
  have hdescent : baseEnd_1506376 < baseStart_1506376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506429 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_1506429 : Nat := 118140960795 + 1506429 * 2 ^ 59
def prefixEnd_1506429 : Nat := 4983230072969 + 3 ^ 40 * 1506429 * 2
def baseEnd_1506429 : Nat := 773522148871991823309565

theorem tailTrace_1506429 : CollatzResearch.WordTrace tailWord_1506429 prefixEnd_1506429 773522148871991823309565 := by
  unfold tailWord_1506429
  simp only [CollatzResearch.WordTrace]
  refine ⟨54943979459472485435394341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36629319639648323623596227 54943979459472485435394341)
  ·
    refine ⟨10301996148651091019136439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54943979459472485435394341 10301996148651091019136439)
    ·
      refine ⟨15452994222976636528704659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10301996148651091019136439 15452994222976636528704659)
      ·
        refine ⟨23179491334464954793056989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15452994222976636528704659 23179491334464954793056989)
        ·
          refine ⟨8692309250424358047396371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23179491334464954793056989 8692309250424358047396371)
          ·
            refine ⟨13038463875636537071094557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8692309250424358047396371 13038463875636537071094557)
            ·
              refine ⟨4889423953363701401660459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13038463875636537071094557 4889423953363701401660459)
              ·
                refine ⟨7334135930045552102490689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4889423953363701401660459 7334135930045552102490689)
                ·
                  refine ⟨5500601947534164076868017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7334135930045552102490689 5500601947534164076868017)
                  ·
                    refine ⟨4125451460650623057651013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5500601947534164076868017 4125451460650623057651013)
                    ·
                      refine ⟨773522148871991823309565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4125451460650623057651013 773522148871991823309565)
                      ·
                        rfl

theorem cell23_1506429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_1506429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506429 prefixEnd_1506429 := by exact prefixLift 1506429
  have htrace : WordTrace (prefixWord ++ tailWord_1506429) baseStart_1506429 baseEnd_1506429 := by
    simpa [prefixWord, tailWord_1506429, baseEnd_1506429] using wordTrace_append hprefix tailTrace_1506429
  have hstable : (prefixWord ++ tailWord_1506429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506429).length < 2 ^ (prefixWord ++ tailWord_1506429).sum := by decide
  have hdescent : baseEnd_1506429 < baseStart_1506429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506433 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_1506433 : Nat := 118140960795 + 1506433 * 2 ^ 59
def prefixEnd_1506433 : Nat := 4983230072969 + 3 ^ 40 * 1506433 * 2
def baseEnd_1506433 : Nat := 773524202794609807659547

theorem tailTrace_1506433 : CollatzResearch.WordTrace tailWord_1506433 prefixEnd_1506433 773524202794609807659547 := by
  unfold tailWord_1506433
  simp only [CollatzResearch.WordTrace]
  refine ⟨54944125351457994118539953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36629416900971996079026635 54944125351457994118539953)
  ·
    refine ⟨41208094013593495588904965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54944125351457994118539953 41208094013593495588904965)
    ·
      refine ⟨7726517627548780422919681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41208094013593495588904965 7726517627548780422919681)
      ·
        refine ⟨5794888220661585317189761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7726517627548780422919681 5794888220661585317189761)
        ·
          refine ⟨4346166165496188987892321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5794888220661585317189761 4346166165496188987892321)
          ·
            refine ⟨3259624624122141740919241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4346166165496188987892321 3259624624122141740919241)
            ·
              refine ⟨2444718468091606305689431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3259624624122141740919241 2444718468091606305689431)
              ·
                refine ⟨3667077702137409458534147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444718468091606305689431 3667077702137409458534147)
                ·
                  refine ⟨5500616553206114187801221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3667077702137409458534147 5500616553206114187801221)
                  ·
                    refine ⟨1031365603726146410212729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5500616553206114187801221 1031365603726146410212729)
                    ·
                      refine ⟨773524202794609807659547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1031365603726146410212729 773524202794609807659547)
                      ·
                        rfl

theorem cell23_1506433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_1506433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506433 prefixEnd_1506433 := by exact prefixLift 1506433
  have htrace : WordTrace (prefixWord ++ tailWord_1506433) baseStart_1506433 baseEnd_1506433 := by
    simpa [prefixWord, tailWord_1506433, baseEnd_1506433] using wordTrace_append hprefix tailTrace_1506433
  have hstable : (prefixWord ++ tailWord_1506433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506433).length < 2 ^ (prefixWord ++ tailWord_1506433).sum := by decide
  have hdescent : baseEnd_1506433 < baseStart_1506433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506456 : List Nat := [2, 1, 2, 4, 2, 1, 1, 5, 5]
def baseStart_1506456 : Nat := 118140960795 + 1506456 * 2 ^ 59
def prefixEnd_1506456 : Nat := 4983230072969 + 3 ^ 40 * 1506456 * 2
def baseEnd_1506456 : Nat := 85948445872184801963549

theorem tailTrace_1506456 : CollatzResearch.WordTrace tailWord_1506456 prefixEnd_1506456 85948445872184801963549 := by
  unfold tailWord_1506456
  simp only [CollatzResearch.WordTrace]
  refine ⟨27472482115187334523313611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36629976153583112697751481 27472482115187334523313611)
  ·
    refine ⟨41208723172781001784970417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27472482115187334523313611 41208723172781001784970417)
    ·
      refine ⟨30906542379585751338727813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41208723172781001784970417 30906542379585751338727813)
      ·
        refine ⟨5794976696172328376011465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30906542379585751338727813 5794976696172328376011465)
        ·
          refine ⟨4346232522129246282008599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5794976696172328376011465 4346232522129246282008599)
          ·
            refine ⟨6519348783193869423012899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4346232522129246282008599 6519348783193869423012899)
            ·
              refine ⟨9779023174790804134519349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6519348783193869423012899 9779023174790804134519349)
              ·
                refine ⟨916783422636637887611189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9779023174790804134519349 916783422636637887611189)
                ·
                  refine ⟨85948445872184801963549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 916783422636637887611189 85948445872184801963549)
                  ·
                    rfl

theorem cell23_1506456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 5].length) (baseStart_1506456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506456 prefixEnd_1506456 := by exact prefixLift 1506456
  have htrace : WordTrace (prefixWord ++ tailWord_1506456) baseStart_1506456 baseEnd_1506456 := by
    simpa [prefixWord, tailWord_1506456, baseEnd_1506456] using wordTrace_append hprefix tailTrace_1506456
  have hstable : (prefixWord ++ tailWord_1506456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506456).length < 2 ^ (prefixWord ++ tailWord_1506456).sum := by decide
  have hdescent : baseEnd_1506456 < baseStart_1506456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506459 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 3, 7, 2]
def baseStart_1506459 : Nat := 118140960795 + 1506459 * 2 ^ 59
def prefixEnd_1506459 : Nat := 4983230072969 + 3 ^ 40 * 1506459 * 2
def baseEnd_1506459 : Nat := 773537553291626705934427

theorem tailTrace_1506459 : CollatzResearch.WordTrace tailWord_1506459 prefixEnd_1506459 773537553291626705934427 := by
  unfold tailWord_1506459
  simp only [CollatzResearch.WordTrace]
  refine ⟨54945073649363800558986431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36630049099575867039324287 54945073649363800558986431)
  ·
    refine ⟨82417610474045700838479647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54945073649363800558986431 82417610474045700838479647)
    ·
      refine ⟨123626415711068551257719471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82417610474045700838479647 123626415711068551257719471)
      ·
        refine ⟨185439623566602826886579207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123626415711068551257719471 185439623566602826886579207)
        ·
          refine ⟨278159435349904240329868811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185439623566602826886579207 278159435349904240329868811)
          ·
            refine ⟨417239153024856360494803217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278159435349904240329868811 417239153024856360494803217)
            ·
              refine ⟨312929364768642270371102413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417239153024856360494803217 312929364768642270371102413)
              ·
                refine ⟨117348511788240851389163405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312929364768642270371102413 117348511788240851389163405)
                ·
                  refine ⟨44005691920590319270936277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117348511788240851389163405 44005691920590319270936277)
                  ·
                    refine ⟨1031383404388835607912569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44005691920590319270936277 1031383404388835607912569)
                    ·
                      refine ⟨773537553291626705934427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1031383404388835607912569 773537553291626705934427)
                      ·
                        rfl

theorem cell23_1506459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 7, 2].length) (baseStart_1506459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506459 prefixEnd_1506459 := by exact prefixLift 1506459
  have htrace : WordTrace (prefixWord ++ tailWord_1506459) baseStart_1506459 baseEnd_1506459 := by
    simpa [prefixWord, tailWord_1506459, baseEnd_1506459] using wordTrace_append hprefix tailTrace_1506459
  have hstable : (prefixWord ++ tailWord_1506459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506459).length < 2 ^ (prefixWord ++ tailWord_1506459).sum := by decide
  have hdescent : baseEnd_1506459 < baseStart_1506459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506489 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1506489 : Nat := 118140960795 + 1506489 * 2 ^ 59
def prefixEnd_1506489 : Nat := 4983230072969 + 3 ^ 40 * 1506489 * 2
def baseEnd_1506489 : Nat := 773552957711261588559289

theorem tailTrace_1506489 : CollatzResearch.WordTrace tailWord_1506489 prefixEnd_1506489 773552957711261588559289 := by
  unfold tailWord_1506489
  simp only [CollatzResearch.WordTrace]
  refine ⟨54946167839255115682578521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36630778559503410455052347 54946167839255115682578521)
  ·
    refine ⟨41209625879441336761933891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54946167839255115682578521 41209625879441336761933891)
    ·
      refine ⟨61814438819162005142900837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41209625879441336761933891 61814438819162005142900837)
      ·
        refine ⟨11590207278592875964293907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61814438819162005142900837 11590207278592875964293907)
        ·
          refine ⟨17385310917889313946440861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11590207278592875964293907 17385310917889313946440861)
          ·
            refine ⟨6519491594208492729915323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17385310917889313946440861 6519491594208492729915323)
            ·
              refine ⟨9779237391312739094872985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6519491594208492729915323 9779237391312739094872985)
              ·
                refine ⟨7334428043484554321154739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9779237391312739094872985 7334428043484554321154739)
                ·
                  refine ⟨11001642065226831481732109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7334428043484554321154739 11001642065226831481732109)
                  ·
                    refine ⟨4125615774460061805649541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11001642065226831481732109 4125615774460061805649541)
                    ·
                      refine ⟨773552957711261588559289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4125615774460061805649541 773552957711261588559289)
                      ·
                        rfl

theorem cell23_1506489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1506489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506489 prefixEnd_1506489 := by exact prefixLift 1506489
  have htrace : WordTrace (prefixWord ++ tailWord_1506489) baseStart_1506489 baseEnd_1506489 := by
    simpa [prefixWord, tailWord_1506489, baseEnd_1506489] using wordTrace_append hprefix tailTrace_1506489
  have hstable : (prefixWord ++ tailWord_1506489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506489).length < 2 ^ (prefixWord ++ tailWord_1506489).sum := by decide
  have hdescent : baseEnd_1506489 < baseStart_1506489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506499 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 5, 4]
def baseStart_1506499 : Nat := 118140960795 + 1506499 * 2 ^ 59
def prefixEnd_1506499 : Nat := 4983230072969 + 3 ^ 40 * 1506499 * 2
def baseEnd_1506499 : Nat := 257852697505935516478081

theorem tailTrace_1506499 : CollatzResearch.WordTrace tailWord_1506499 prefixEnd_1506499 257852697505935516478081 := by
  unfold tailWord_1506499
  simp only [CollatzResearch.WordTrace]
  refine ⟨54946532569218887390442551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36631021712812591593628367 54946532569218887390442551)
  ·
    refine ⟨82419798853828331085663827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54946532569218887390442551 82419798853828331085663827)
    ·
      refine ⟨123629698280742496628495741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82419798853828331085663827 123629698280742496628495741)
      ·
        refine ⟨46361136855278436235685903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123629698280742496628495741 46361136855278436235685903)
        ·
          refine ⟨69541705282917654353528855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46361136855278436235685903 69541705282917654353528855)
          ·
            refine ⟨104312557924376481530293283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69541705282917654353528855 104312557924376481530293283)
            ·
              refine ⟨156468836886564722295439925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104312557924376481530293283 156468836886564722295439925)
              ·
                refine ⟨14668953458115442715197493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156468836886564722295439925 14668953458115442715197493)
                ·
                  refine ⟨1375214386698322754549765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14668953458115442715197493 1375214386698322754549765)
                  ·
                    refine ⟨257852697505935516478081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1375214386698322754549765 257852697505935516478081)
                    ·
                      rfl

theorem cell23_1506499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 4].length) (baseStart_1506499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506499 prefixEnd_1506499 := by exact prefixLift 1506499
  have htrace : WordTrace (prefixWord ++ tailWord_1506499) baseStart_1506499 baseEnd_1506499 := by
    simpa [prefixWord, tailWord_1506499, baseEnd_1506499] using wordTrace_append hprefix tailTrace_1506499
  have hstable : (prefixWord ++ tailWord_1506499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506499).length < 2 ^ (prefixWord ++ tailWord_1506499).sum := by decide
  have hdescent : baseEnd_1506499 < baseStart_1506499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506529 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 8]
def baseStart_1506529 : Nat := 118140960795 + 1506529 * 2 ^ 59
def prefixEnd_1506529 : Nat := 4983230072969 + 3 ^ 40 * 1506529 * 2
def baseEnd_1506529 : Nat := 85952610770826825784345

theorem tailTrace_1506529 : CollatzResearch.WordTrace tailWord_1506529 prefixEnd_1506529 85952610770826825784345 := by
  unfold tailWord_1506529
  simp only [CollatzResearch.WordTrace]
  refine ⟨54947626759110202514034641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36631751172740135009356427 54947626759110202514034641)
  ·
    refine ⟨41210720069332651885525981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54947626759110202514034641 41210720069332651885525981)
    ·
      refine ⟨15454020025999744457072243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41210720069332651885525981 15454020025999744457072243)
      ·
        refine ⟨23181030038999616685608365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15454020025999744457072243 23181030038999616685608365)
        ·
          refine ⟨8692886264624856257103137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23181030038999616685608365 8692886264624856257103137)
          ·
            refine ⟨6519664698468642192827353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8692886264624856257103137 6519664698468642192827353)
            ·
              refine ⟨4889748523851481644620515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6519664698468642192827353 4889748523851481644620515)
              ·
                refine ⟨7334622785777222466930773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4889748523851481644620515 7334622785777222466930773)
                ·
                  refine ⟨85952610770826825784345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7334622785777222466930773 85952610770826825784345)
                  ·
                    rfl

theorem cell23_1506529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 8].length) (baseStart_1506529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506529 prefixEnd_1506529 := by exact prefixLift 1506529
  have htrace : WordTrace (prefixWord ++ tailWord_1506529) baseStart_1506529 baseEnd_1506529 := by
    simpa [prefixWord, tailWord_1506529, baseEnd_1506529] using wordTrace_append hprefix tailTrace_1506529
  have hstable : (prefixWord ++ tailWord_1506529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506529).length < 2 ^ (prefixWord ++ tailWord_1506529).sum := by decide
  have hdescent : baseEnd_1506529 < baseStart_1506529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506583 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 2, 3, 2]
def baseStart_1506583 : Nat := 118140960795 + 1506583 * 2 ^ 59
def prefixEnd_1506583 : Nat := 4983230072969 + 3 ^ 40 * 1506583 * 2
def baseEnd_1506583 : Nat := 773601224892784220783857

theorem tailTrace_1506583 : CollatzResearch.WordTrace tailWord_1506583 prefixEnd_1506583 773601224892784220783857 := by
  unfold tailWord_1506583
  simp only [CollatzResearch.WordTrace]
  refine ⟨54949596300914569736500403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36633064200609713157666935 54949596300914569736500403)
  ·
    refine ⟨82424394451371854604750605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54949596300914569736500403 82424394451371854604750605)
    ·
      refine ⟨30909147919264445476781477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82424394451371854604750605 30909147919264445476781477)
      ·
        refine ⟨5795465234862083526896527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30909147919264445476781477 5795465234862083526896527)
        ·
          refine ⟨8693197852293125290344791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5795465234862083526896527 8693197852293125290344791)
          ·
            refine ⟨13039796778439687935517187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8693197852293125290344791 13039796778439687935517187)
            ·
              refine ⟨19559695167659531903275781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13039796778439687935517187 19559695167659531903275781)
              ·
                refine ⟨3667442843936162231864209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19559695167659531903275781 3667442843936162231864209)
                ·
                  refine ⟨2750582132952121673898157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3667442843936162231864209 2750582132952121673898157)
                  ·
                    refine ⟨1031468299857045627711809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2750582132952121673898157 1031468299857045627711809)
                    ·
                      refine ⟨773601224892784220783857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1031468299857045627711809 773601224892784220783857)
                      ·
                        rfl

theorem cell23_1506583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_1506583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506583 prefixEnd_1506583 := by exact prefixLift 1506583
  have htrace : WordTrace (prefixWord ++ tailWord_1506583) baseStart_1506583 baseEnd_1506583 := by
    simpa [prefixWord, tailWord_1506583, baseEnd_1506583] using wordTrace_append hprefix tailTrace_1506583
  have hstable : (prefixWord ++ tailWord_1506583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506583).length < 2 ^ (prefixWord ++ tailWord_1506583).sum := by decide
  have hdescent : baseEnd_1506583 < baseStart_1506583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506596 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_1506596 : Nat := 118140960795 + 1506596 * 2 ^ 59
def prefixEnd_1506596 : Nat := 4983230072969 + 3 ^ 40 * 1506596 * 2
def baseEnd_1506596 : Nat := 773607900141292669921297

theorem tailTrace_1506596 : CollatzResearch.WordTrace tailWord_1506596 prefixEnd_1506596 773607900141292669921297 := by
  unfold tailWord_1506596
  simp only [CollatzResearch.WordTrace]
  refine ⟨27475035224933736478361821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36633380299911648637815761 27475035224933736478361821)
  ·
    refine ⟨10303138209350151179385683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27475035224933736478361821 10303138209350151179385683)
    ·
      refine ⟨15454707314025226769078525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10303138209350151179385683 15454707314025226769078525)
      ·
        refine ⟨5795515242759460038404447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15454707314025226769078525 5795515242759460038404447)
        ·
          refine ⟨8693272864139190057606671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5795515242759460038404447 8693272864139190057606671)
          ·
            refine ⟨13039909296208785086410007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8693272864139190057606671 13039909296208785086410007)
            ·
              refine ⟨19559863944313177629615011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13039909296208785086410007 19559863944313177629615011)
              ·
                refine ⟨29339795916469766444422517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19559863944313177629615011 29339795916469766444422517)
                ·
                  refine ⟨2750605867169040604164611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29339795916469766444422517 2750605867169040604164611)
                  ·
                    refine ⟨4125908800753560906246917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2750605867169040604164611 4125908800753560906246917)
                    ·
                      refine ⟨773607900141292669921297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4125908800753560906246917 773607900141292669921297)
                      ·
                        rfl

theorem cell23_1506596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_1506596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506596 prefixEnd_1506596 := by exact prefixLift 1506596
  have htrace : WordTrace (prefixWord ++ tailWord_1506596) baseStart_1506596 baseEnd_1506596 := by
    simpa [prefixWord, tailWord_1506596, baseEnd_1506596] using wordTrace_append hprefix tailTrace_1506596
  have hstable : (prefixWord ++ tailWord_1506596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506596).length < 2 ^ (prefixWord ++ tailWord_1506596).sum := by decide
  have hdescent : baseEnd_1506596 < baseStart_1506596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506617 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1506617 : Nat := 118140960795 + 1506617 * 2 ^ 59
def prefixEnd_1506617 : Nat := 4983230072969 + 3 ^ 40 * 1506617 * 2
def baseEnd_1506617 : Nat := 773618683235037087758701

theorem tailTrace_1506617 : CollatzResearch.WordTrace tailWord_1506617 prefixEnd_1506617 773618683235037087758701 := by
  unfold tailWord_1506617
  simp only [CollatzResearch.WordTrace]
  refine ⟨54950836382791393543238105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36633890921860929028825403 54950836382791393543238105)
  ·
    refine ⟨41213127287093545157428579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54950836382791393543238105 41213127287093545157428579)
    ·
      refine ⟨61819690930640317736142869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41213127287093545157428579 61819690930640317736142869)
      ·
        refine ⟨2897798012373764893881697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61819690930640317736142869 2897798012373764893881697)
        ·
          refine ⟨2173348509280323670411273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2897798012373764893881697 2173348509280323670411273)
          ·
            refine ⟨1630011381960242752808455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2173348509280323670411273 1630011381960242752808455)
            ·
              refine ⟨2445017072940364129212683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630011381960242752808455 2445017072940364129212683)
              ·
                refine ⟨3667525609410546193819025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445017072940364129212683 3667525609410546193819025)
                ·
                  refine ⟨2750644207057909645364269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3667525609410546193819025 2750644207057909645364269)
                  ·
                    refine ⟨1031491577646716117011601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2750644207057909645364269 1031491577646716117011601)
                    ·
                      refine ⟨773618683235037087758701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1031491577646716117011601 773618683235037087758701)
                      ·
                        rfl

theorem cell23_1506617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1506617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506617 prefixEnd_1506617 := by exact prefixLift 1506617
  have htrace : WordTrace (prefixWord ++ tailWord_1506617) baseStart_1506617 baseEnd_1506617 := by
    simpa [prefixWord, tailWord_1506617, baseEnd_1506617] using wordTrace_append hprefix tailTrace_1506617
  have hstable : (prefixWord ++ tailWord_1506617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506617).length < 2 ^ (prefixWord ++ tailWord_1506617).sum := by decide
  have hdescent : baseEnd_1506617 < baseStart_1506617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506647 : List Nat := [1, 1, 3, 2, 3, 2, 2, 4, 1, 2, 2]
def baseStart_1506647 : Nat := 118140960795 + 1506647 * 2 ^ 59
def prefixEnd_1506647 : Nat := 4983230072969 + 3 ^ 40 * 1506647 * 2
def baseEnd_1506647 : Nat := 773634087654671970383563

theorem tailTrace_1506647 : CollatzResearch.WordTrace tailWord_1506647 prefixEnd_1506647 773634087654671970383563 := by
  unfold tailWord_1506647
  simp only [CollatzResearch.WordTrace]
  refine ⟨54951930572682708666830195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36634620381788472444553463 54951930572682708666830195)
  ·
    refine ⟨82427895859024063000245293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54951930572682708666830195 82427895859024063000245293)
    ·
      refine ⟨30910460947134023625091985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82427895859024063000245293 30910460947134023625091985)
      ·
        refine ⟨23182845710350517718818989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30910460947134023625091985 23182845710350517718818989)
        ·
          refine ⟨8693567141381444144557121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23182845710350517718818989 8693567141381444144557121)
          ·
            refine ⟨6520175356036083108417841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8693567141381444144557121 6520175356036083108417841)
            ·
              refine ⟨4890131517027062331313381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6520175356036083108417841 4890131517027062331313381)
              ·
                refine ⟨916899659442574187121259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4890131517027062331313381 916899659442574187121259)
                ·
                  refine ⟨1375349489163861280681889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 916899659442574187121259 1375349489163861280681889)
                  ·
                    refine ⟨1031512116872895960511417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1375349489163861280681889 1031512116872895960511417)
                    ·
                      refine ⟨773634087654671970383563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1031512116872895960511417 773634087654671970383563)
                      ·
                        rfl

theorem cell23_1506647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_1506647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506647 prefixEnd_1506647 := by exact prefixLift 1506647
  have htrace : WordTrace (prefixWord ++ tailWord_1506647) baseStart_1506647 baseEnd_1506647 := by
    simpa [prefixWord, tailWord_1506647, baseEnd_1506647] using wordTrace_append hprefix tailTrace_1506647
  have hstable : (prefixWord ++ tailWord_1506647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506647).length < 2 ^ (prefixWord ++ tailWord_1506647).sum := by decide
  have hdescent : baseEnd_1506647 < baseStart_1506647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506649 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 1, 9]
def baseStart_1506649 : Nat := 118140960795 + 1506649 * 2 ^ 59
def prefixEnd_1506649 : Nat := 4983230072969 + 3 ^ 40 * 1506649 * 2
def baseEnd_1506649 : Nat := 257878371538660320852851

theorem tailTrace_1506649 : CollatzResearch.WordTrace tailWord_1506649 prefixEnd_1506649 257878371538660320852851 := by
  unfold tailWord_1506649
  simp only [CollatzResearch.WordTrace]
  refine ⟨54952003518675463008403001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36634669012450308672268667 54952003518675463008403001)
  ·
    refine ⟨41214002639006597256302251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54952003518675463008403001 41214002639006597256302251)
    ·
      refine ⟨61821003958509895884453377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41214002639006597256302251 61821003958509895884453377)
      ·
        refine ⟨46365752968882421913340033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61821003958509895884453377 46365752968882421913340033)
        ·
          refine ⟨34774314726661816435005025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46365752968882421913340033 34774314726661816435005025)
          ·
            refine ⟨26080736044996362326253769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34774314726661816435005025 26080736044996362326253769)
            ·
              refine ⟨19560552033747271744690327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26080736044996362326253769 19560552033747271744690327)
              ·
                refine ⟨29340828050620907617035491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19560552033747271744690327 29340828050620907617035491)
                ·
                  refine ⟨44011242075931361425553237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29340828050620907617035491 44011242075931361425553237)
                  ·
                    refine ⟨257878371538660320852851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 44011242075931361425553237 257878371538660320852851)
                    ·
                      rfl

theorem cell23_1506649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_1506649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506649 prefixEnd_1506649 := by exact prefixLift 1506649
  have htrace : WordTrace (prefixWord ++ tailWord_1506649) baseStart_1506649 baseEnd_1506649 := by
    simpa [prefixWord, tailWord_1506649, baseEnd_1506649] using wordTrace_append hprefix tailTrace_1506649
  have hstable : (prefixWord ++ tailWord_1506649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506649).length < 2 ^ (prefixWord ++ tailWord_1506649).sum := by decide
  have hdescent : baseEnd_1506649 < baseStart_1506649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506673 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 3, 3, 2]
def baseStart_1506673 : Nat := 118140960795 + 1506673 * 2 ^ 59
def prefixEnd_1506673 : Nat := 4983230072969 + 3 ^ 40 * 1506673 * 2
def baseEnd_1506673 : Nat := 773647438151688868658443

theorem tailTrace_1506673 : CollatzResearch.WordTrace tailWord_1506673 prefixEnd_1506673 773647438151688868658443 := by
  unfold tailWord_1506673
  simp only [CollatzResearch.WordTrace]
  refine ⟨54952878870588515107276673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36635252580392343404851115 54952878870588515107276673)
  ·
    refine ⟨41214659152941386330457505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54952878870588515107276673 41214659152941386330457505)
    ·
      refine ⟨30910994364706039747843129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41214659152941386330457505 30910994364706039747843129)
      ·
        refine ⟨23183245773529529810882347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30910994364706039747843129 23183245773529529810882347)
        ·
          refine ⟨34774868660294294716323521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23183245773529529810882347 34774868660294294716323521)
          ·
            refine ⟨26081151495220721037242641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34774868660294294716323521 26081151495220721037242641)
            ·
              refine ⟨19560863621415540777931981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26081151495220721037242641 19560863621415540777931981)
              ·
                refine ⟨7335323858030827791724493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19560863621415540777931981 7335323858030827791724493)
                ·
                  refine ⟨2750746446761560421896685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7335323858030827791724493 2750746446761560421896685)
                  ·
                    refine ⟨1031529917535585158211257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2750746446761560421896685 1031529917535585158211257)
                    ·
                      refine ⟨773647438151688868658443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1031529917535585158211257 773647438151688868658443)
                      ·
                        rfl

theorem cell23_1506673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_1506673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506673 prefixEnd_1506673 := by exact prefixLift 1506673
  have htrace : WordTrace (prefixWord ++ tailWord_1506673) baseStart_1506673 baseEnd_1506673 := by
    simpa [prefixWord, tailWord_1506673, baseEnd_1506673] using wordTrace_append hprefix tailTrace_1506673
  have hstable : (prefixWord ++ tailWord_1506673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506673).length < 2 ^ (prefixWord ++ tailWord_1506673).sum := by decide
  have hdescent : baseEnd_1506673 < baseStart_1506673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506736 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 3]
def baseStart_1506736 : Nat := 118140960795 + 1506736 * 2 ^ 59
def prefixEnd_1506736 : Nat := 4983230072969 + 3 ^ 40 * 1506736 * 2
def baseEnd_1506736 : Nat := 773679787432922122170653

theorem tailTrace_1506736 : CollatzResearch.WordTrace tailWord_1506736 prefixEnd_1506736 773679787432922122170653 := by
  unfold tailWord_1506736
  simp only [CollatzResearch.WordTrace]
  refine ⟨27477588334680138433410031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36636784446240184577880041 27477588334680138433410031)
  ·
    refine ⟨41216382502020207650115047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27477588334680138433410031 41216382502020207650115047)
    ·
      refine ⟨61824573753030311475172571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41216382502020207650115047 61824573753030311475172571)
      ·
        refine ⟨92736860629545467212758857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61824573753030311475172571 92736860629545467212758857)
        ·
          refine ⟨69552645472159100409569143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92736860629545467212758857 69552645472159100409569143)
          ·
            refine ⟨104328968208238650614353715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69552645472159100409569143 104328968208238650614353715)
            ·
              refine ⟨156493452312357975921530573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104328968208238650614353715 156493452312357975921530573)
              ·
                refine ⟨58685044617134240970573965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156493452312357975921530573 58685044617134240970573965)
                ·
                  refine ⟨22006891731425340363965237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58685044617134240970573965 22006891731425340363965237)
                  ·
                    refine ⟨2063146099821125659121741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22006891731425340363965237 2063146099821125659121741)
                    ·
                      refine ⟨773679787432922122170653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2063146099821125659121741 773679787432922122170653)
                      ·
                        rfl

theorem cell23_1506736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 3].length) (baseStart_1506736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506736 prefixEnd_1506736 := by exact prefixLift 1506736
  have htrace : WordTrace (prefixWord ++ tailWord_1506736) baseStart_1506736 baseEnd_1506736 := by
    simpa [prefixWord, tailWord_1506736, baseEnd_1506736] using wordTrace_append hprefix tailTrace_1506736
  have hstable : (prefixWord ++ tailWord_1506736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506736).length < 2 ^ (prefixWord ++ tailWord_1506736).sum := by decide
  have hdescent : baseEnd_1506736 < baseStart_1506736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506743 : List Nat := [1, 1, 3, 1, 3, 2, 2, 5, 5]
def baseStart_1506743 : Nat := 118140960795 + 1506743 * 2 ^ 59
def prefixEnd_1506743 : Nat := 4983230072969 + 3 ^ 40 * 1506743 * 2
def baseEnd_1506743 : Nat := 85964820199722621642569

theorem tailTrace_1506743 : CollatzResearch.WordTrace tailWord_1506743 prefixEnd_1506743 85964820199722621642569 := by
  unfold tailWord_1506743
  simp only [CollatzResearch.WordTrace]
  refine ⟨54955431980334917062324883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36636954653556611374883255 54955431980334917062324883)
  ·
    refine ⟨82433147970502375593487325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54955431980334917062324883 82433147970502375593487325)
    ·
      refine ⟨30912430488938390847557747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82433147970502375593487325 30912430488938390847557747)
      ·
        refine ⟨46368645733407586271336621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30912430488938390847557747 46368645733407586271336621)
        ·
          refine ⟨17388242150027844851751233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46368645733407586271336621 17388242150027844851751233)
          ·
            refine ⟨13041181612520883638813425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17388242150027844851751233 13041181612520883638813425)
            ·
              refine ⟨9780886209390662729110069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13041181612520883638813425 9780886209390662729110069)
              ·
                refine ⟨916958082130374630854069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9780886209390662729110069 916958082130374630854069)
                ·
                  refine ⟨85964820199722621642569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 916958082130374630854069 85964820199722621642569)
                  ·
                    rfl

theorem cell23_1506743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 5].length) (baseStart_1506743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506743 prefixEnd_1506743 := by exact prefixLift 1506743
  have htrace : WordTrace (prefixWord ++ tailWord_1506743) baseStart_1506743 baseEnd_1506743 := by
    simpa [prefixWord, tailWord_1506743, baseEnd_1506743] using wordTrace_append hprefix tailTrace_1506743
  have hstable : (prefixWord ++ tailWord_1506743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506743).length < 2 ^ (prefixWord ++ tailWord_1506743).sum := by decide
  have hdescent : baseEnd_1506743 < baseStart_1506743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506763 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 2, 5, 2]
def baseStart_1506763 : Nat := 118140960795 + 1506763 * 2 ^ 59
def prefixEnd_1506763 : Nat := 4983230072969 + 3 ^ 40 * 1506763 * 2
def baseEnd_1506763 : Nat := 773693651410593516533029

theorem tailTrace_1506763 : CollatzResearch.WordTrace tailWord_1506763 prefixEnd_1506763 773693651410593516533029 := by
  unfold tailWord_1506763
  simp only [CollatzResearch.WordTrace]
  refine ⟨54956161440262460478052943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36637440960174973652035295 54956161440262460478052943)
  ·
    refine ⟨82434242160393690717079415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54956161440262460478052943 82434242160393690717079415)
    ·
      refine ⟨123651363240590536075619123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82434242160393690717079415 123651363240590536075619123)
      ·
        refine ⟨185477044860885804113428685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123651363240590536075619123 185477044860885804113428685)
        ·
          refine ⟨69553891822832176542535757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185477044860885804113428685 69553891822832176542535757)
          ·
            refine ⟨26082709433562066203450909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69553891822832176542535757 26082709433562066203450909)
            ·
              refine ⟨9781016037585774826294091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26082709433562066203450909 9781016037585774826294091)
              ·
                refine ⟨14671524056378662239441137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9781016037585774826294091 14671524056378662239441137)
                ·
                  refine ⟨11003643042283996679580853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14671524056378662239441137 11003643042283996679580853)
                  ·
                    refine ⟨1031591535214124688710705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11003643042283996679580853 1031591535214124688710705)
                    ·
                      refine ⟨773693651410593516533029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1031591535214124688710705 773693651410593516533029)
                      ·
                        rfl

theorem cell23_1506763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 5, 2].length) (baseStart_1506763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506763 prefixEnd_1506763 := by exact prefixLift 1506763
  have htrace : WordTrace (prefixWord ++ tailWord_1506763) baseStart_1506763 baseEnd_1506763 := by
    simpa [prefixWord, tailWord_1506763, baseEnd_1506763] using wordTrace_append hprefix tailTrace_1506763
  have hstable : (prefixWord ++ tailWord_1506763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506763).length < 2 ^ (prefixWord ++ tailWord_1506763).sum := by decide
  have hdescent : baseEnd_1506763 < baseStart_1506763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506796 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_1506796 : Nat := 118140960795 + 1506796 * 2 ^ 59
def prefixEnd_1506796 : Nat := 4983230072969 + 3 ^ 40 * 1506796 * 2
def baseEnd_1506796 : Nat := 773710596272191887420377

theorem tailTrace_1506796 : CollatzResearch.WordTrace tailWord_1506796 prefixEnd_1506796 773710596272191887420377 := by
  unfold tailWord_1506796
  simp only [CollatzResearch.WordTrace]
  refine ⟨27478682524571453557002121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36638243366095271409336161 27478682524571453557002121)
  ·
    refine ⟨20609011893428590167751591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27478682524571453557002121 20609011893428590167751591)
    ·
      refine ⟨30913517840142885251627387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20609011893428590167751591 30913517840142885251627387)
      ·
        refine ⟨46370276760214327877441081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30913517840142885251627387 46370276760214327877441081)
        ·
          refine ⟨34777707570160745908080811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46370276760214327877441081 34777707570160745908080811)
          ·
            refine ⟨52166561355241118862121217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34777707570160745908080811 52166561355241118862121217)
            ·
              refine ⟨39124921016430839146590913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52166561355241118862121217 39124921016430839146590913)
              ·
                refine ⟨29343690762323129359943185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39124921016430839146590913 29343690762323129359943185)
                ·
                  refine ⟨22007768071742347019957389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29343690762323129359943185 22007768071742347019957389)
                  ·
                    refine ⟨8252913026903380132484021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22007768071742347019957389 8252913026903380132484021)
                    ·
                      refine ⟨773710596272191887420377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8252913026903380132484021 773710596272191887420377)
                      ·
                        rfl

theorem cell23_1506796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_1506796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506796 prefixEnd_1506796 := by exact prefixLift 1506796
  have htrace : WordTrace (prefixWord ++ tailWord_1506796) baseStart_1506796 baseEnd_1506796 := by
    simpa [prefixWord, tailWord_1506796, baseEnd_1506796] using wordTrace_append hprefix tailTrace_1506796
  have hstable : (prefixWord ++ tailWord_1506796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506796).length < 2 ^ (prefixWord ++ tailWord_1506796).sum := by decide
  have hdescent : baseEnd_1506796 < baseStart_1506796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506900 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1506900 : Nat := 118140960795 + 1506900 * 2 ^ 59
def prefixEnd_1506900 : Nat := 4983230072969 + 3 ^ 40 * 1506900 * 2
def baseEnd_1506900 : Nat := 773763998260259480519899

theorem tailTrace_1506900 : CollatzResearch.WordTrace tailWord_1506900 prefixEnd_1506900 773763998260259480519899 := by
  unfold tailWord_1506900
  simp only [CollatzResearch.WordTrace]
  refine ⟨27480579120383066437895077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36640772160510755250526769 27480579120383066437895077)
  ·
    refine ⟨5152608585071824957105327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27480579120383066437895077 5152608585071824957105327)
    ·
      refine ⟨7728912877607737435657991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5152608585071824957105327 7728912877607737435657991)
      ·
        refine ⟨11593369316411606153486987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7728912877607737435657991 11593369316411606153486987)
        ·
          refine ⟨17390053974617409230230481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11593369316411606153486987 17390053974617409230230481)
          ·
            refine ⟨13042540480963056922672861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17390053974617409230230481 13042540480963056922672861)
            ·
              refine ⟨4890952680361146346002323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13042540480963056922672861 4890952680361146346002323)
              ·
                refine ⟨7336429020541719519003485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4890952680361146346002323 7336429020541719519003485)
                ·
                  refine ⟨2751160882703144819626307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7336429020541719519003485 2751160882703144819626307)
                  ·
                    refine ⟨4126741324054717229439461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2751160882703144819626307 4126741324054717229439461)
                    ·
                      refine ⟨773763998260259480519899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4126741324054717229439461 773763998260259480519899)
                      ·
                        rfl

theorem cell23_1506900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1506900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506900 prefixEnd_1506900 := by exact prefixLift 1506900
  have htrace : WordTrace (prefixWord ++ tailWord_1506900) baseStart_1506900 baseEnd_1506900 := by
    simpa [prefixWord, tailWord_1506900, baseEnd_1506900] using wordTrace_append hprefix tailTrace_1506900
  have hstable : (prefixWord ++ tailWord_1506900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506900).length < 2 ^ (prefixWord ++ tailWord_1506900).sum := by decide
  have hdescent : baseEnd_1506900 < baseStart_1506900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506978 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_1506978 : Nat := 118140960795 + 1506978 * 2 ^ 59
def prefixEnd_1506978 : Nat := 4983230072969 + 3 ^ 40 * 1506978 * 2
def baseEnd_1506978 : Nat := 257934683250436725114847

theorem tailTrace_1506978 : CollatzResearch.WordTrace tailWord_1506978 prefixEnd_1506978 257934683250436725114847 := by
  unfold tailWord_1506978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13741000783620888049282397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36642668756322368131419725 13741000783620888049282397)
  ·
    refine ⟨5152875293857833018480899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13741000783620888049282397 5152875293857833018480899)
    ·
      refine ⟨7729312940786749527721349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5152875293857833018480899 7729312940786749527721349)
      ·
        refine ⟨1449246176397515536447753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7729312940786749527721349 1449246176397515536447753)
        ·
          refine ⟨1086934632298136652335815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1449246176397515536447753 1086934632298136652335815)
          ·
            refine ⟨1630401948447204978503723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086934632298136652335815 1630401948447204978503723)
            ·
              refine ⟨2445602922670807467755585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630401948447204978503723 2445602922670807467755585)
              ·
                refine ⟨1834202192003105600816689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2445602922670807467755585 1834202192003105600816689)
                ·
                  refine ⟨1375651644002329200612517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1834202192003105600816689 1375651644002329200612517)
                  ·
                    refine ⟨257934683250436725114847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1375651644002329200612517 257934683250436725114847)
                    ·
                      rfl

theorem cell23_1506978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_1506978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1506978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1506978 prefixEnd_1506978 := by exact prefixLift 1506978
  have htrace : WordTrace (prefixWord ++ tailWord_1506978) baseStart_1506978 baseEnd_1506978 := by
    simpa [prefixWord, tailWord_1506978, baseEnd_1506978] using wordTrace_append hprefix tailTrace_1506978
  have hstable : (prefixWord ++ tailWord_1506978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506978).length < 2 ^ (prefixWord ++ tailWord_1506978).sum := by decide
  have hdescent : baseEnd_1506978 < baseStart_1506978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507014 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1507014 : Nat := 118140960795 + 1507014 * 2 ^ 59
def prefixEnd_1507014 : Nat := 4983230072969 + 3 ^ 40 * 1507014 * 2
def baseEnd_1507014 : Nat := 773822535054872034494375

theorem tailTrace_1507014 : CollatzResearch.WordTrace tailWord_1507014 prefixEnd_1507014 773822535054872034494375 := by
  unfold tailWord_1507014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1717666130073535323295003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36643544108235420230293397 1717666130073535323295003)
  ·
    refine ⟨2576499195110302984942505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1717666130073535323295003 2576499195110302984942505)
    ·
      refine ⟨1932374396332727238706879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2576499195110302984942505 1932374396332727238706879)
      ·
        refine ⟨2898561594499090858060319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1932374396332727238706879 2898561594499090858060319)
        ·
          refine ⟨4347842391748636287090479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898561594499090858060319 4347842391748636287090479)
          ·
            refine ⟨6521763587622954430635719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4347842391748636287090479 6521763587622954430635719)
            ·
              refine ⟨9782645381434431645953579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6521763587622954430635719 9782645381434431645953579)
              ·
                refine ⟨14673968072151647468930369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9782645381434431645953579 14673968072151647468930369)
                ·
                  refine ⟨11005476054113735601697777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14673968072151647468930369 11005476054113735601697777)
                  ·
                    refine ⟨8254107040585301701273333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11005476054113735601697777 8254107040585301701273333)
                    ·
                      refine ⟨773822535054872034494375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8254107040585301701273333 773822535054872034494375)
                      ·
                        rfl

theorem cell23_1507014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1507014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507014 prefixEnd_1507014 := by exact prefixLift 1507014
  have htrace : WordTrace (prefixWord ++ tailWord_1507014) baseStart_1507014 baseEnd_1507014 := by
    simpa [prefixWord, tailWord_1507014, baseEnd_1507014] using wordTrace_append hprefix tailTrace_1507014
  have hstable : (prefixWord ++ tailWord_1507014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507014).length < 2 ^ (prefixWord ++ tailWord_1507014).sum := by decide
  have hdescent : baseEnd_1507014 < baseStart_1507014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507040 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 3]
def baseStart_1507040 : Nat := 118140960795 + 1507040 * 2 ^ 59
def prefixEnd_1507040 : Nat := 4983230072969 + 3 ^ 40 * 1507040 * 2
def baseEnd_1507040 : Nat := 773835885551888932769255

theorem tailTrace_1507040 : CollatzResearch.WordTrace tailWord_1507040 prefixEnd_1507040 773835885551888932769255 := by
  unfold tailWord_1507040
  simp only [CollatzResearch.WordTrace]
  refine ⟨27483132230129468392943287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36644176306839291190591049 27483132230129468392943287)
  ·
    refine ⟨41224698345194202589414931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27483132230129468392943287 41224698345194202589414931)
    ·
      refine ⟨61837047517791303884122397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41224698345194202589414931 61837047517791303884122397)
      ·
        refine ⟨23188892819171738956545899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61837047517791303884122397 23188892819171738956545899)
        ·
          refine ⟨34783339228757608434818849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23188892819171738956545899 34783339228757608434818849)
          ·
            refine ⟨26087504421568206326114137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34783339228757608434818849 26087504421568206326114137)
            ·
              refine ⟨19565628316176154744585603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26087504421568206326114137 19565628316176154744585603)
              ·
                refine ⟨29348442474264232116878405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19565628316176154744585603 29348442474264232116878405)
                ·
                  refine ⟨5502832963924543521914701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29348442474264232116878405 5502832963924543521914701)
                  ·
                    refine ⟨2063562361471703820718013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5502832963924543521914701 2063562361471703820718013)
                    ·
                      refine ⟨773835885551888932769255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2063562361471703820718013 773835885551888932769255)
                      ·
                        rfl

theorem cell23_1507040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_1507040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507040 prefixEnd_1507040 := by exact prefixLift 1507040
  have htrace : WordTrace (prefixWord ++ tailWord_1507040) baseStart_1507040 baseEnd_1507040 := by
    simpa [prefixWord, tailWord_1507040, baseEnd_1507040] using wordTrace_append hprefix tailTrace_1507040
  have hstable : (prefixWord ++ tailWord_1507040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507040).length < 2 ^ (prefixWord ++ tailWord_1507040).sum := by decide
  have hdescent : baseEnd_1507040 < baseStart_1507040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507092 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1507092 : Nat := 118140960795 + 1507092 * 2 ^ 59
def prefixEnd_1507092 : Nat := 4983230072969 + 3 ^ 40 * 1507092 * 2
def baseEnd_1507092 : Nat := 773862586545922729319017

theorem tailTrace_1507092 : CollatzResearch.WordTrace tailWord_1507092 prefixEnd_1507092 773862586545922729319017 := by
  unfold tailWord_1507092
  simp only [CollatzResearch.WordTrace]
  refine ⟨27484080528035274833389765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36645440704047033111186353 27484080528035274833389765)
  ·
    refine ⟨5153265099006614031260581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27484080528035274833389765 5153265099006614031260581)
    ·
      refine ⟨966237206063740130861359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5153265099006614031260581 966237206063740130861359)
      ·
        refine ⟨1449355809095610196292039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966237206063740130861359 1449355809095610196292039)
        ·
          refine ⟨2174033713643415294438059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1449355809095610196292039 2174033713643415294438059)
          ·
            refine ⟨3261050570465122941657089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174033713643415294438059 3261050570465122941657089)
            ·
              refine ⟨2445787927848842206242817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3261050570465122941657089 2445787927848842206242817)
              ·
                refine ⟨1834340945886631654682113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2445787927848842206242817 1834340945886631654682113)
                ·
                  refine ⟨1375755709414973741011585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1834340945886631654682113 1375755709414973741011585)
                  ·
                    refine ⟨1031816782061230305758689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1375755709414973741011585 1031816782061230305758689)
                    ·
                      refine ⟨773862586545922729319017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1031816782061230305758689 773862586545922729319017)
                      ·
                        rfl

theorem cell23_1507092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1507092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507092 prefixEnd_1507092 := by exact prefixLift 1507092
  have htrace : WordTrace (prefixWord ++ tailWord_1507092) baseStart_1507092 baseEnd_1507092 := by
    simpa [prefixWord, tailWord_1507092, baseEnd_1507092] using wordTrace_append hprefix tailTrace_1507092
  have hstable : (prefixWord ++ tailWord_1507092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507092).length < 2 ^ (prefixWord ++ tailWord_1507092).sum := by decide
  have hdescent : baseEnd_1507092 < baseStart_1507092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507100 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1507100 : Nat := 118140960795 + 1507100 * 2 ^ 59
def prefixEnd_1507100 : Nat := 4983230072969 + 3 ^ 40 * 1507100 * 2
def baseEnd_1507100 : Nat := 773866694391158698018979

theorem tailTrace_1507100 : CollatzResearch.WordTrace tailWord_1507100 prefixEnd_1507100 773866694391158698018979 := by
  unfold tailWord_1507100
  simp only [CollatzResearch.WordTrace]
  refine ⟨27484226420020783516535377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36645635226694378022047169 27484226420020783516535377)
  ·
    refine ⟨20613169815015587637401533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27484226420020783516535377 20613169815015587637401533)
    ·
      refine ⟨7729938680630845364025575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20613169815015587637401533 7729938680630845364025575)
      ·
        refine ⟨11594908020946268046038363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7729938680630845364025575 11594908020946268046038363)
        ·
          refine ⟨17392362031419402069057545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11594908020946268046038363 17392362031419402069057545)
          ·
            refine ⟨13044271523564551551793159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17392362031419402069057545 13044271523564551551793159)
            ·
              refine ⟨19566407285346827327689739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13044271523564551551793159 19566407285346827327689739)
              ·
                refine ⟨29349610928020240991534609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19566407285346827327689739 29349610928020240991534609)
                ·
                  refine ⟨22012208196015180743650957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29349610928020240991534609 22012208196015180743650957)
                  ·
                    refine ⟨8254578073505692778869109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22012208196015180743650957 8254578073505692778869109)
                    ·
                      refine ⟨773866694391158698018979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8254578073505692778869109 773866694391158698018979)
                      ·
                        rfl

theorem cell23_1507100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1507100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507100 prefixEnd_1507100 := by exact prefixLift 1507100
  have htrace : WordTrace (prefixWord ++ tailWord_1507100) baseStart_1507100 baseEnd_1507100 := by
    simpa [prefixWord, tailWord_1507100, baseEnd_1507100] using wordTrace_append hprefix tailTrace_1507100
  have hstable : (prefixWord ++ tailWord_1507100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507100).length < 2 ^ (prefixWord ++ tailWord_1507100).sum := by decide
  have hdescent : baseEnd_1507100 < baseStart_1507100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507124 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1507124 : Nat := 118140960795 + 1507124 * 2 ^ 59
def prefixEnd_1507124 : Nat := 4983230072969 + 3 ^ 40 * 1507124 * 2
def baseEnd_1507124 : Nat := 257959672642288868039623

theorem tailTrace_1507124 : CollatzResearch.WordTrace tailWord_1507124 prefixEnd_1507124 257959672642288868039623 := by
  unfold tailWord_1507124
  simp only [CollatzResearch.WordTrace]
  refine ⟨27484664095977309565972213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36646218794636412754629617 27484664095977309565972213)
  ·
    refine ⟨2576687258997872771809895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27484664095977309565972213 2576687258997872771809895)
    ·
      refine ⟨3865030888496809157714843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576687258997872771809895 3865030888496809157714843)
      ·
        refine ⟨5797546332745213736572265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3865030888496809157714843 5797546332745213736572265)
        ·
          refine ⟨4348159749558910302429199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5797546332745213736572265 4348159749558910302429199)
          ·
            refine ⟨6522239624338365453643799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4348159749558910302429199 6522239624338365453643799)
            ·
              refine ⟨9783359436507548180465699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6522239624338365453643799 9783359436507548180465699)
              ·
                refine ⟨14675039154761322270698549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9783359436507548180465699 14675039154761322270698549)
                ·
                  refine ⟨1375784920758873962877989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14675039154761322270698549 1375784920758873962877989)
                  ·
                    refine ⟨257959672642288868039623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1375784920758873962877989 257959672642288868039623)
                    ·
                      rfl

theorem cell23_1507124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1507124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507124 prefixEnd_1507124 := by exact prefixLift 1507124
  have htrace : WordTrace (prefixWord ++ tailWord_1507124) baseStart_1507124 baseEnd_1507124 := by
    simpa [prefixWord, tailWord_1507124, baseEnd_1507124] using wordTrace_append hprefix tailTrace_1507124
  have hstable : (prefixWord ++ tailWord_1507124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507124).length < 2 ^ (prefixWord ++ tailWord_1507124).sum := by decide
  have hdescent : baseEnd_1507124 < baseStart_1507124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507134 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_1507134 : Nat := 118140960795 + 1507134 * 2 ^ 59
def prefixEnd_1507134 : Nat := 4983230072969 + 3 ^ 40 * 1507134 * 2
def baseEnd_1507134 : Nat := 773884152733411564993823

theorem tailTrace_1507134 : CollatzResearch.WordTrace tailWord_1507134 prefixEnd_1507134 773884152733411564993823 := by
  unfold tailWord_1507134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6871211615239798854976057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36646461947945593893205637 6871211615239798854976057)
  ·
    refine ⟨5153408711429849141232043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6871211615239798854976057 5153408711429849141232043)
    ·
      refine ⟨7730113067144773711848065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5153408711429849141232043 7730113067144773711848065)
      ·
        refine ⟨5797584800358580283886049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7730113067144773711848065 5797584800358580283886049)
        ·
          refine ⟨4348188600268935212914537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5797584800358580283886049 4348188600268935212914537)
          ·
            refine ⟨3261141450201701409685903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4348188600268935212914537 3261141450201701409685903)
            ·
              refine ⟨4891712175302552114528855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3261141450201701409685903 4891712175302552114528855)
              ·
                refine ⟨7337568262953828171793283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4891712175302552114528855 7337568262953828171793283)
                ·
                  refine ⟨11006352394430742257689925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7337568262953828171793283 11006352394430742257689925)
                  ·
                    refine ⟨2063691073955764173316861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11006352394430742257689925 2063691073955764173316861)
                    ·
                      refine ⟨773884152733411564993823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2063691073955764173316861 773884152733411564993823)
                      ·
                        rfl

theorem cell23_1507134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_1507134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507134 prefixEnd_1507134 := by exact prefixLift 1507134
  have htrace : WordTrace (prefixWord ++ tailWord_1507134) baseStart_1507134 baseEnd_1507134 := by
    simpa [prefixWord, tailWord_1507134, baseEnd_1507134] using wordTrace_append hprefix tailTrace_1507134
  have hstable : (prefixWord ++ tailWord_1507134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507134).length < 2 ^ (prefixWord ++ tailWord_1507134).sum := by decide
  have hdescent : baseEnd_1507134 < baseStart_1507134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507154 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 6]
def baseStart_1507154 : Nat := 118140960795 + 1507154 * 2 ^ 59
def prefixEnd_1507154 : Nat := 4983230072969 + 3 ^ 40 * 1507154 * 2
def baseEnd_1507154 : Nat := 85988269149611276304859

theorem tailTrace_1507154 : CollatzResearch.WordTrace tailWord_1507154 prefixEnd_1507154 85988269149611276304859 := by
  unfold tailWord_1507154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13742605595461483563884129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36646948254563956170357677 13742605595461483563884129)
  ·
    refine ⟨10306954196596112672913097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13742605595461483563884129 10306954196596112672913097)
    ·
      refine ⟨7730215647447084504684823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10306954196596112672913097 7730215647447084504684823)
      ·
        refine ⟨11595323471170626757027235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7730215647447084504684823 11595323471170626757027235)
        ·
          refine ⟨17392985206755940135540853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11595323471170626757027235 17392985206755940135540853)
          ·
            refine ⟨1630592363133369387706955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17392985206755940135540853 1630592363133369387706955)
            ·
              refine ⟨2445888544700054081560433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630592363133369387706955 2445888544700054081560433)
              ·
                refine ⟨1834416408525040561170325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2445888544700054081560433 1834416408525040561170325)
                ·
                  refine ⟨85988269149611276304859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1834416408525040561170325 85988269149611276304859)
                  ·
                    rfl

theorem cell23_1507154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_1507154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507154 prefixEnd_1507154 := by exact prefixLift 1507154
  have htrace : WordTrace (prefixWord ++ tailWord_1507154) baseStart_1507154 baseEnd_1507154 := by
    simpa [prefixWord, tailWord_1507154, baseEnd_1507154] using wordTrace_append hprefix tailTrace_1507154
  have hstable : (prefixWord ++ tailWord_1507154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507154).length < 2 ^ (prefixWord ++ tailWord_1507154).sum := by decide
  have hdescent : baseEnd_1507154 < baseStart_1507154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507187 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 1, 8, 2]
def baseStart_1507187 : Nat := 118140960795 + 1507187 * 2 ^ 59
def prefixEnd_1507187 : Nat := 4983230072969 + 3 ^ 40 * 1507187 * 2
def baseEnd_1507187 : Nat := 773911367208099857631079

theorem tailTrace_1507187 : CollatzResearch.WordTrace tailWord_1507187 prefixEnd_1507187 773911367208099857631079 := by
  unfold tailWord_1507187
  simp only [CollatzResearch.WordTrace]
  refine ⟨54971625990726380891487815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36647750660484253927658543 54971625990726380891487815)
  ·
    refine ⟨82457438986089571337231723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54971625990726380891487815 82457438986089571337231723)
    ·
      refine ⟨123686158479134357005847585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82457438986089571337231723 123686158479134357005847585)
      ·
        refine ⟨92764618859350767754385689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123686158479134357005847585 92764618859350767754385689)
        ·
          refine ⟨69573464144513075815789267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92764618859350767754385689 69573464144513075815789267)
          ·
            refine ⟨104360196216769613723683901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69573464144513075815789267 104360196216769613723683901)
            ·
              refine ⟨39135073581288605146381463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104360196216769613723683901 39135073581288605146381463)
              ·
                refine ⟨58702610371932907719572195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39135073581288605146381463 58702610371932907719572195)
                ·
                  refine ⟨88053915557899361579358293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58702610371932907719572195 88053915557899361579358293)
                  ·
                    refine ⟨1031881822944133143508105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88053915557899361579358293 1031881822944133143508105)
                    ·
                      refine ⟨773911367208099857631079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1031881822944133143508105 773911367208099857631079)
                      ·
                        rfl

theorem cell23_1507187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 8, 2].length) (baseStart_1507187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507187 prefixEnd_1507187 := by exact prefixLift 1507187
  have htrace : WordTrace (prefixWord ++ tailWord_1507187) baseStart_1507187 baseEnd_1507187 := by
    simpa [prefixWord, tailWord_1507187, baseEnd_1507187] using wordTrace_append hprefix tailTrace_1507187
  have hstable : (prefixWord ++ tailWord_1507187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507187).length < 2 ^ (prefixWord ++ tailWord_1507187).sum := by decide
  have hdescent : baseEnd_1507187 < baseStart_1507187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507204 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_1507204 : Nat := 118140960795 + 1507204 * 2 ^ 59
def prefixEnd_1507204 : Nat := 4983230072969 + 3 ^ 40 * 1507204 * 2
def baseEnd_1507204 : Nat := 773920096379226291118501

theorem tailTrace_1507204 : CollatzResearch.WordTrace tailWord_1507204 prefixEnd_1507204 773920096379226291118501 := by
  unfold tailWord_1507204
  simp only [CollatzResearch.WordTrace]
  refine ⟨27486123015832396397428333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36648164021109861863237777 27486123015832396397428333)
  ·
    refine ⟨10307296130937148649035625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27486123015832396397428333 10307296130937148649035625)
    ·
      refine ⟨7730472098202861486776719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10307296130937148649035625 7730472098202861486776719)
      ·
        refine ⟨11595708147304292230165079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7730472098202861486776719 11595708147304292230165079)
        ·
          refine ⟨17393562220956438345247619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11595708147304292230165079 17393562220956438345247619)
          ·
            refine ⟨26090343331434657517871429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17393562220956438345247619 26090343331434657517871429)
            ·
              refine ⟨4891939374643998284600893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26090343331434657517871429 4891939374643998284600893)
              ·
                refine ⟨1834477265491499356725335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4891939374643998284600893 1834477265491499356725335)
                ·
                  refine ⟨2751715898237249035088003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834477265491499356725335 2751715898237249035088003)
                  ·
                    refine ⟨4127573847355873552632005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2751715898237249035088003 4127573847355873552632005)
                    ·
                      refine ⟨773920096379226291118501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4127573847355873552632005 773920096379226291118501)
                      ·
                        rfl

theorem cell23_1507204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_1507204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507204 prefixEnd_1507204 := by exact prefixLift 1507204
  have htrace : WordTrace (prefixWord ++ tailWord_1507204) baseStart_1507204 baseEnd_1507204 := by
    simpa [prefixWord, tailWord_1507204, baseEnd_1507204] using wordTrace_append hprefix tailTrace_1507204
  have hstable : (prefixWord ++ tailWord_1507204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507204).length < 2 ^ (prefixWord ++ tailWord_1507204).sum := by decide
  have hdescent : baseEnd_1507204 < baseStart_1507204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507222 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_1507222 : Nat := 118140960795 + 1507222 * 2 ^ 59
def prefixEnd_1507222 : Nat := 4983230072969 + 3 ^ 40 * 1507222 * 2
def baseEnd_1507222 : Nat := 85992148781223024521491

theorem tailTrace_1507222 : CollatzResearch.WordTrace tailWord_1507222 prefixEnd_1507222 85992148781223024521491 := by
  unfold tailWord_1507222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435806409099973866813245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36648601697066387912674613 3435806409099973866813245)
  ·
    refine ⟨1288427403412490200054967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3435806409099973866813245 1288427403412490200054967)
    ·
      refine ⟨1932641105118735300082451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1288427403412490200054967 1932641105118735300082451)
      ·
        refine ⟨2898961657678102950123677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1932641105118735300082451 2898961657678102950123677)
        ·
          refine ⟨1087110621629288606296379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2898961657678102950123677 1087110621629288606296379)
          ·
            refine ⟨1630665932443932909444569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087110621629288606296379 1630665932443932909444569)
            ·
              refine ⟨1222999449332949682083427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1630665932443932909444569 1222999449332949682083427)
              ·
                refine ⟨1834499173999424523125141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1222999449332949682083427 1834499173999424523125141)
                ·
                  refine ⟨85992148781223024521491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1834499173999424523125141 85992148781223024521491)
                  ·
                    rfl

theorem cell23_1507222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_1507222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507222 prefixEnd_1507222 := by exact prefixLift 1507222
  have htrace : WordTrace (prefixWord ++ tailWord_1507222) baseStart_1507222 baseEnd_1507222 := by
    simpa [prefixWord, tailWord_1507222, baseEnd_1507222] using wordTrace_append hprefix tailTrace_1507222
  have hstable : (prefixWord ++ tailWord_1507222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507222).length < 2 ^ (prefixWord ++ tailWord_1507222).sum := by decide
  have hdescent : baseEnd_1507222 < baseStart_1507222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507231 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 2, 4]
def baseStart_1507231 : Nat := 118140960795 + 1507231 * 2 ^ 59
def prefixEnd_1507231 : Nat := 4983230072969 + 3 ^ 40 * 1507231 * 2
def baseEnd_1507231 : Nat := 257977986785632561826959

theorem tailTrace_1507231 : CollatzResearch.WordTrace tailWord_1507231 prefixEnd_1507231 257977986785632561826959 := by
  unfold tailWord_1507231
  simp only [CollatzResearch.WordTrace]
  refine ⟨54973230802566976406089547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36648820535044650937393031 54973230802566976406089547)
  ·
    refine ⟨82459846203850464609134321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54973230802566976406089547 82459846203850464609134321)
    ·
      refine ⟨61844884652887848456850741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82459846203850464609134321 61844884652887848456850741)
      ·
        refine ⟨5797957936208235792829757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61844884652887848456850741 5797957936208235792829757)
        ·
          refine ⟨2174234226078088422311159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5797957936208235792829757 2174234226078088422311159)
          ·
            refine ⟨3261351339117132633466739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174234226078088422311159 3261351339117132633466739)
            ·
              refine ⟨4892027008675698950200109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3261351339117132633466739 4892027008675698950200109)
              ·
                refine ⟨1834510128253387106325041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4892027008675698950200109 1834510128253387106325041)
                ·
                  refine ⟨1375882596190040329743781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1834510128253387106325041 1375882596190040329743781)
                  ·
                    refine ⟨257977986785632561826959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1375882596190040329743781 257977986785632561826959)
                    ·
                      rfl

theorem cell23_1507231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 4].length) (baseStart_1507231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507231 prefixEnd_1507231 := by exact prefixLift 1507231
  have htrace : WordTrace (prefixWord ++ tailWord_1507231) baseStart_1507231 baseEnd_1507231 := by
    simpa [prefixWord, tailWord_1507231, baseEnd_1507231] using wordTrace_append hprefix tailTrace_1507231
  have hstable : (prefixWord ++ tailWord_1507231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507231).length < 2 ^ (prefixWord ++ tailWord_1507231).sum := by decide
  have hdescent : baseEnd_1507231 < baseStart_1507231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507237 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 5, 3, 3]
def baseStart_1507237 : Nat := 118140960795 + 1507237 * 2 ^ 59
def prefixEnd_1507237 : Nat := 4983230072969 + 3 ^ 40 * 1507237 * 2
def baseEnd_1507237 : Nat := 773937041240824662005849

theorem tailTrace_1507237 : CollatzResearch.WordTrace tailWord_1507237 prefixEnd_1507237 773937041240824662005849 := by
  unfold tailWord_1507237
  simp only [CollatzResearch.WordTrace]
  refine ⟨54973449640545239430807965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36648966427030159620538643 54973449640545239430807965)
  ·
    refine ⟨20615043615204464786552987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54973449640545239430807965 20615043615204464786552987)
    ·
      refine ⟨30922565422806697179829481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20615043615204464786552987 30922565422806697179829481)
      ·
        refine ⟨23191924067105022884872111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30922565422806697179829481 23191924067105022884872111)
        ·
          refine ⟨34787886100657534327308167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23191924067105022884872111 34787886100657534327308167)
          ·
            refine ⟨52181829150986301490962251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34787886100657534327308167 52181829150986301490962251)
            ·
              refine ⟨78272743726479452236443377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52181829150986301490962251 78272743726479452236443377)
              ·
                refine ⟨58704557794859589177332533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78272743726479452236443377 58704557794859589177332533)
                ·
                  refine ⟨5503552293268086485374925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58704557794859589177332533 5503552293268086485374925)
                  ·
                    refine ⟨2063832109975532432015597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5503552293268086485374925 2063832109975532432015597)
                    ·
                      refine ⟨773937041240824662005849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2063832109975532432015597 773937041240824662005849)
                      ·
                        rfl

theorem cell23_1507237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_1507237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507237 prefixEnd_1507237 := by exact prefixLift 1507237
  have htrace : WordTrace (prefixWord ++ tailWord_1507237) baseStart_1507237 baseEnd_1507237 := by
    simpa [prefixWord, tailWord_1507237, baseEnd_1507237] using wordTrace_append hprefix tailTrace_1507237
  have hstable : (prefixWord ++ tailWord_1507237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507237).length < 2 ^ (prefixWord ++ tailWord_1507237).sum := by decide
  have hdescent : baseEnd_1507237 < baseStart_1507237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507272 : List Nat := [2, 1, 3, 1, 4, 3, 2, 2, 1, 2, 2]
def baseStart_1507272 : Nat := 118140960795 + 1507272 * 2 ^ 59
def prefixEnd_1507272 : Nat := 4983230072969 + 3 ^ 40 * 1507272 * 2
def baseEnd_1507272 : Nat := 773955013063732025068189

theorem tailTrace_1507272 : CollatzResearch.WordTrace tailWord_1507272 prefixEnd_1507272 773955013063732025068189 := by
  unfold tailWord_1507272
  simp only [CollatzResearch.WordTrace]
  refine ⟨27487363097709220204166035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36649817463612293605554713 27487363097709220204166035)
  ·
    refine ⟨41231044646563830306249053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27487363097709220204166035 41231044646563830306249053)
    ·
      refine ⟨15461641742461436364843395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41231044646563830306249053 15461641742461436364843395)
      ·
        refine ⟨23192462613692154547265093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15461641742461436364843395 23192462613692154547265093)
        ·
          refine ⟨4348586740067278977612205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23192462613692154547265093 4348586740067278977612205)
          ·
            refine ⟨1630720027525229616604577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4348586740067278977612205 1630720027525229616604577)
            ·
              refine ⟨1223040020643922212453433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1630720027525229616604577 1223040020643922212453433)
              ·
                refine ⟨917280015482941659340075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223040020643922212453433 917280015482941659340075)
                ·
                  refine ⟨1375920023224412489010113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 917280015482941659340075 1375920023224412489010113)
                  ·
                    refine ⟨1031940017418309366757585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1375920023224412489010113 1031940017418309366757585)
                    ·
                      refine ⟨773955013063732025068189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1031940017418309366757585 773955013063732025068189)
                      ·
                        rfl

theorem cell23_1507272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_1507272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507272 prefixEnd_1507272 := by exact prefixLift 1507272
  have htrace : WordTrace (prefixWord ++ tailWord_1507272) baseStart_1507272 baseEnd_1507272 := by
    simpa [prefixWord, tailWord_1507272, baseEnd_1507272] using wordTrace_append hprefix tailTrace_1507272
  have hstable : (prefixWord ++ tailWord_1507272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507272).length < 2 ^ (prefixWord ++ tailWord_1507272).sum := by decide
  have hdescent : baseEnd_1507272 < baseStart_1507272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507287 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 2, 6]
def baseStart_1507287 : Nat := 118140960795 + 1507287 * 2 ^ 59
def prefixEnd_1507287 : Nat := 4983230072969 + 3 ^ 40 * 1507287 * 2
def baseEnd_1507287 : Nat := 257987571757849822126873

theorem tailTrace_1507287 : CollatzResearch.WordTrace tailWord_1507287 prefixEnd_1507287 257987571757849822126873 := by
  unfold tailWord_1507287
  simp only [CollatzResearch.WordTrace]
  refine ⟨54975273290364097970128115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36650182193576065313418743 54975273290364097970128115)
  ·
    refine ⟨82462909935546146955192173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54975273290364097970128115 82462909935546146955192173)
    ·
      refine ⟨30923591225829805108197065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82462909935546146955192173 30923591225829805108197065)
      ·
        refine ⟨23192693419372353831147799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30923591225829805108197065 23192693419372353831147799)
        ·
          refine ⟨34789040129058530746721699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23192693419372353831147799 34789040129058530746721699)
          ·
            refine ⟨52183560193587796120082549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34789040129058530746721699 52183560193587796120082549)
            ·
              refine ⟨4892208768148855886257739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52183560193587796120082549 4892208768148855886257739)
              ·
                refine ⟨7338313152223283829386609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4892208768148855886257739 7338313152223283829386609)
                ·
                  refine ⟨5503734864167462872039957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7338313152223283829386609 5503734864167462872039957)
                  ·
                    refine ⟨257987571757849822126873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5503734864167462872039957 257987571757849822126873)
                    ·
                      rfl

theorem cell23_1507287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_1507287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507287 prefixEnd_1507287 := by exact prefixLift 1507287
  have htrace : WordTrace (prefixWord ++ tailWord_1507287) baseStart_1507287 baseEnd_1507287 := by
    simpa [prefixWord, tailWord_1507287, baseEnd_1507287] using wordTrace_append hprefix tailTrace_1507287
  have hstable : (prefixWord ++ tailWord_1507287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507287).length < 2 ^ (prefixWord ++ tailWord_1507287).sum := by decide
  have hdescent : baseEnd_1507287 < baseStart_1507287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507297 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_1507297 : Nat := 118140960795 + 1507297 * 2 ^ 59
def prefixEnd_1507297 : Nat := 4983230072969 + 3 ^ 40 * 1507297 * 2
def baseEnd_1507297 : Nat := 773967850080094427255573

theorem tailTrace_1507297 : CollatzResearch.WordTrace tailWord_1507297 prefixEnd_1507297 773967850080094427255573 := by
  unfold tailWord_1507297
  simp only [CollatzResearch.WordTrace]
  refine ⟨54975638020327869677992145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36650425346885246451994763 54975638020327869677992145)
  ·
    refine ⟨41231728515245902258494109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54975638020327869677992145 41231728515245902258494109)
    ·
      refine ⟨15461898193217213346935291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41231728515245902258494109 15461898193217213346935291)
      ·
        refine ⟨23192847289825820020402937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15461898193217213346935291 23192847289825820020402937)
        ·
          refine ⟨17394635467369365015302203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23192847289825820020402937 17394635467369365015302203)
          ·
            refine ⟨26091953201054047522953305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17394635467369365015302203 26091953201054047522953305)
            ·
              refine ⟨19568964900790535642214979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26091953201054047522953305 19568964900790535642214979)
              ·
                refine ⟨29353447351185803463322469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19568964900790535642214979 29353447351185803463322469)
                ·
                  refine ⟨5503771378347338149372963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29353447351185803463322469 5503771378347338149372963)
                  ·
                    refine ⟨8255657067521007224059445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5503771378347338149372963 8255657067521007224059445)
                    ·
                      refine ⟨773967850080094427255573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8255657067521007224059445 773967850080094427255573)
                      ·
                        rfl

theorem cell23_1507297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_1507297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507297 prefixEnd_1507297 := by exact prefixLift 1507297
  have htrace : WordTrace (prefixWord ++ tailWord_1507297) baseStart_1507297 baseEnd_1507297 := by
    simpa [prefixWord, tailWord_1507297, baseEnd_1507297] using wordTrace_append hprefix tailTrace_1507297
  have hstable : (prefixWord ++ tailWord_1507297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507297).length < 2 ^ (prefixWord ++ tailWord_1507297).sum := by decide
  have hdescent : baseEnd_1507297 < baseStart_1507297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507311 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 4, 2, 2]
def baseStart_1507311 : Nat := 118140960795 + 1507311 * 2 ^ 59
def prefixEnd_1507311 : Nat := 4983230072969 + 3 ^ 40 * 1507311 * 2
def baseEnd_1507311 : Nat := 773975038809257372480509

theorem tailTrace_1507311 : CollatzResearch.WordTrace tailWord_1507311 prefixEnd_1507311 773975038809257372480509 := by
  unfold tailWord_1507311
  simp only [CollatzResearch.WordTrace]
  refine ⟨54976148642277150069001787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36650765761518100046001191 54976148642277150069001787)
  ·
    refine ⟨82464222963415725103502681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54976148642277150069001787 82464222963415725103502681)
    ·
      refine ⟨61848167222561793827627011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82464222963415725103502681 61848167222561793827627011)
      ·
        refine ⟨92772250833842690741440517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61848167222561793827627011 92772250833842690741440517)
        ·
          refine ⟨17394797031345504514020097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92772250833842690741440517 17394797031345504514020097)
          ·
            refine ⟨13046097773509128385515073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17394797031345504514020097 13046097773509128385515073)
            ·
              refine ⟨9784573330131846289136305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13046097773509128385515073 9784573330131846289136305)
              ·
                refine ⟨7338429997598884716852229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9784573330131846289136305 7338429997598884716852229)
                ·
                  refine ⟨1375955624549790884409793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7338429997598884716852229 1375955624549790884409793)
                  ·
                    refine ⟨1031966718412343163307345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1375955624549790884409793 1031966718412343163307345)
                    ·
                      refine ⟨773975038809257372480509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1031966718412343163307345 773975038809257372480509)
                      ·
                        rfl

theorem cell23_1507311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 2, 2].length) (baseStart_1507311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507311 prefixEnd_1507311 := by exact prefixLift 1507311
  have htrace : WordTrace (prefixWord ++ tailWord_1507311) baseStart_1507311 baseEnd_1507311 := by
    simpa [prefixWord, tailWord_1507311, baseEnd_1507311] using wordTrace_append hprefix tailTrace_1507311
  have hstable : (prefixWord ++ tailWord_1507311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507311).length < 2 ^ (prefixWord ++ tailWord_1507311).sum := by decide
  have hdescent : baseEnd_1507311 < baseStart_1507311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507347 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 1, 7]
def baseStart_1507347 : Nat := 118140960795 + 1507347 * 2 ^ 59
def prefixEnd_1507347 : Nat := 4983230072969 + 3 ^ 40 * 1507347 * 2
def baseEnd_1507347 : Nat := 257997841370939743876781

theorem tailTrace_1507347 : CollatzResearch.WordTrace tailWord_1507347 prefixEnd_1507347 257997841370939743876781 := by
  unfold tailWord_1507347
  simp only [CollatzResearch.WordTrace]
  refine ⟨54977461670146728217312295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36651641113431152144874863 54977461670146728217312295)
  ·
    refine ⟨82466192505220092325968443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54977461670146728217312295 82466192505220092325968443)
    ·
      refine ⟨123699288757830138488952665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82466192505220092325968443 123699288757830138488952665)
      ·
        refine ⟨92774466568372603866714499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123699288757830138488952665 92774466568372603866714499)
        ·
          refine ⟨139161699852558905800071749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92774466568372603866714499 139161699852558905800071749)
          ·
            refine ⟨26092818722354794837513453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139161699852558905800071749 26092818722354794837513453)
            ·
              refine ⟨9784807020883048064067545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26092818722354794837513453 9784807020883048064067545)
              ·
                refine ⟨7338605265662286048050659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9784807020883048064067545 7338605265662286048050659)
                ·
                  refine ⟨11007907898493429072075989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7338605265662286048050659 11007907898493429072075989)
                  ·
                    refine ⟨257997841370939743876781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11007907898493429072075989 257997841370939743876781)
                    ·
                      rfl

theorem cell23_1507347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 7].length) (baseStart_1507347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507347 prefixEnd_1507347 := by exact prefixLift 1507347
  have htrace : WordTrace (prefixWord ++ tailWord_1507347) baseStart_1507347 baseEnd_1507347 := by
    simpa [prefixWord, tailWord_1507347, baseEnd_1507347] using wordTrace_append hprefix tailTrace_1507347
  have hstable : (prefixWord ++ tailWord_1507347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507347).length < 2 ^ (prefixWord ++ tailWord_1507347).sum := by decide
  have hdescent : baseEnd_1507347 < baseStart_1507347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507387 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 5]
def baseStart_1507387 : Nat := 118140960795 + 1507387 * 2 ^ 59
def prefixEnd_1507387 : Nat := 4983230072969 + 3 ^ 40 * 1507387 * 2
def baseEnd_1507387 : Nat := 774014063338999075130159

theorem tailTrace_1507387 : CollatzResearch.WordTrace tailWord_1507387 prefixEnd_1507387 774014063338999075130159 := by
  unfold tailWord_1507387
  simp only [CollatzResearch.WordTrace]
  refine ⟨54978920590001815048768415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36652613726667876699178943 54978920590001815048768415)
  ·
    refine ⟨82468380885002722573152623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54978920590001815048768415 82468380885002722573152623)
    ·
      refine ⟨123702571327504083859728935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82468380885002722573152623 123702571327504083859728935)
      ·
        refine ⟨185553856991256125789593403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123702571327504083859728935 185553856991256125789593403)
        ·
          refine ⟨278330785486884188684390105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185553856991256125789593403 278330785486884188684390105)
          ·
            refine ⟨208748089115163141513292579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278330785486884188684390105 208748089115163141513292579)
            ·
              refine ⟨313122133672744712269938869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208748089115163141513292579 313122133672744712269938869)
              ·
                refine ⟨29355200031819816775306769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 313122133672744712269938869 29355200031819816775306769)
                ·
                  refine ⟨22016400023864862581480077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29355200031819816775306769 22016400023864862581480077)
                  ·
                    refine ⟨8256150008949323468055029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22016400023864862581480077 8256150008949323468055029)
                    ·
                      refine ⟨774014063338999075130159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8256150008949323468055029 774014063338999075130159)
                      ·
                        rfl

theorem cell23_1507387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_1507387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507387 prefixEnd_1507387 := by exact prefixLift 1507387
  have htrace : WordTrace (prefixWord ++ tailWord_1507387) baseStart_1507387 baseEnd_1507387 := by
    simpa [prefixWord, tailWord_1507387, baseEnd_1507387] using wordTrace_append hprefix tailTrace_1507387
  have hstable : (prefixWord ++ tailWord_1507387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507387).length < 2 ^ (prefixWord ++ tailWord_1507387).sum := by decide
  have hdescent : baseEnd_1507387 < baseStart_1507387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507404 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 3, 4, 3]
def baseStart_1507404 : Nat := 118140960795 + 1507404 * 2 ^ 59
def prefixEnd_1507404 : Nat := 4983230072969 + 3 ^ 40 * 1507404 * 2
def baseEnd_1507404 : Nat := 774022792510125508617581

theorem tailTrace_1507404 : CollatzResearch.WordTrace tailWord_1507404 prefixEnd_1507404 774022792510125508617581 := by
  unfold tailWord_1507404
  simp only [CollatzResearch.WordTrace]
  refine ⟨27489770315470113476068633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36653027087293484634758177 27489770315470113476068633)
  ·
    refine ⟨20617327736602585107051475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27489770315470113476068633 20617327736602585107051475)
    ·
      refine ⟨30925991604903877660577213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20617327736602585107051475 30925991604903877660577213)
      ·
        refine ⟨11597246851838954122716455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30925991604903877660577213 11597246851838954122716455)
        ·
          refine ⟨17395870277758431184074683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11597246851838954122716455 17395870277758431184074683)
          ·
            refine ⟨26093805416637646776112025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17395870277758431184074683 26093805416637646776112025)
            ·
              refine ⟨19570354062478235082084019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26093805416637646776112025 19570354062478235082084019)
              ·
                refine ⟨29355531093717352623126029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19570354062478235082084019 29355531093717352623126029)
                ·
                  refine ⟨11008324160144007233672261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29355531093717352623126029 11008324160144007233672261)
                  ·
                    refine ⟨2064060780027001356313549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11008324160144007233672261 2064060780027001356313549)
                    ·
                      refine ⟨774022792510125508617581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2064060780027001356313549 774022792510125508617581)
                      ·
                        rfl

theorem cell23_1507404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_1507404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507404 prefixEnd_1507404 := by exact prefixLift 1507404
  have htrace : WordTrace (prefixWord ++ tailWord_1507404) baseStart_1507404 baseEnd_1507404 := by
    simpa [prefixWord, tailWord_1507404, baseEnd_1507404] using wordTrace_append hprefix tailTrace_1507404
  have hstable : (prefixWord ++ tailWord_1507404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507404).length < 2 ^ (prefixWord ++ tailWord_1507404).sum := by decide
  have hdescent : baseEnd_1507404 < baseStart_1507404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507485 : List Nat := [1, 4, 2, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_1507485 : Nat := 118140960795 + 1507485 * 2 ^ 59
def prefixEnd_1507485 : Nat := 4983230072969 + 3 ^ 40 * 1507485 * 2
def baseEnd_1507485 : Nat := 774064384443139691704709

theorem tailTrace_1507485 : CollatzResearch.WordTrace tailWord_1507485 prefixEnd_1507485 774064384443139691704709 := by
  unfold tailWord_1507485
  simp only [CollatzResearch.WordTrace]
  refine ⟨54982494943646777785835909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36654996629097851857223939 54982494943646777785835909)
  ·
    refine ⟨10309217801933770834844233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54982494943646777785835909 10309217801933770834844233)
    ·
      refine ⟨7731913351450328126133175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10309217801933770834844233 7731913351450328126133175)
      ·
        refine ⟨11597870027175492189199763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7731913351450328126133175 11597870027175492189199763)
        ·
          refine ⟨17396805040763238283799645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11597870027175492189199763 17396805040763238283799645)
          ·
            refine ⟨6523801890286214356424867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17396805040763238283799645 6523801890286214356424867)
            ·
              refine ⟨9785702835429321534637301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6523801890286214356424867 9785702835429321534637301)
              ·
                refine ⟨917409640821498893872247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9785702835429321534637301 917409640821498893872247)
                ·
                  refine ⟨1376114461232248340808371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 917409640821498893872247 1376114461232248340808371)
                  ·
                    refine ⟨2064171691848372511212557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1376114461232248340808371 2064171691848372511212557)
                    ·
                      refine ⟨774064384443139691704709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2064171691848372511212557 774064384443139691704709)
                      ·
                        rfl

theorem cell23_1507485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_1507485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507485 prefixEnd_1507485 := by exact prefixLift 1507485
  have htrace : WordTrace (prefixWord ++ tailWord_1507485) baseStart_1507485 baseEnd_1507485 := by
    simpa [prefixWord, tailWord_1507485, baseEnd_1507485] using wordTrace_append hprefix tailTrace_1507485
  have hstable : (prefixWord ++ tailWord_1507485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507485).length < 2 ^ (prefixWord ++ tailWord_1507485).sum := by decide
  have hdescent : baseEnd_1507485 < baseStart_1507485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507488 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 1, 5]
def baseStart_1507488 : Nat := 118140960795 + 1507488 * 2 ^ 59
def prefixEnd_1507488 : Nat := 4983230072969 + 3 ^ 40 * 1507488 * 2
def baseEnd_1507488 : Nat := 258021974961701059989065

theorem tailTrace_1507488 : CollatzResearch.WordTrace tailWord_1507488 prefixEnd_1507488 258021974961701059989065 := by
  unfold tailWord_1507488
  simp only [CollatzResearch.WordTrace]
  refine ⟨27491302181317954649097559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36655069575090606198796745 27491302181317954649097559)
  ·
    refine ⟨41236953271976931973646339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27491302181317954649097559 41236953271976931973646339)
    ·
      refine ⟨61855429907965397960469509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41236953271976931973646339 61855429907965397960469509)
      ·
        refine ⟨11597893107743512117588033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61855429907965397960469509 11597893107743512117588033)
        ·
          refine ⟨8698419830807634088191025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11597893107743512117588033 8698419830807634088191025)
          ·
            refine ⟨6523814873105725566143269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8698419830807634088191025 6523814873105725566143269)
            ·
              refine ⟨1223215288707323543651863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6523814873105725566143269 1223215288707323543651863)
              ·
                refine ⟨1834822933060985315477795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223215288707323543651863 1834822933060985315477795)
                ·
                  refine ⟨2752234399591477973216693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834822933060985315477795 2752234399591477973216693)
                  ·
                    refine ⟨258021974961701059989065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2752234399591477973216693 258021974961701059989065)
                    ·
                      rfl

theorem cell23_1507488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 1, 5].length) (baseStart_1507488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507488 prefixEnd_1507488 := by exact prefixLift 1507488
  have htrace : WordTrace (prefixWord ++ tailWord_1507488) baseStart_1507488 baseEnd_1507488 := by
    simpa [prefixWord, tailWord_1507488, baseEnd_1507488] using wordTrace_append hprefix tailTrace_1507488
  have hstable : (prefixWord ++ tailWord_1507488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507488).length < 2 ^ (prefixWord ++ tailWord_1507488).sum := by decide
  have hdescent : baseEnd_1507488 < baseStart_1507488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507511 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_1507511 : Nat := 118140960795 + 1507511 * 2 ^ 59
def prefixEnd_1507511 : Nat := 4983230072969 + 3 ^ 40 * 1507511 * 2
def baseEnd_1507511 : Nat := 774077734940156589979589

theorem tailTrace_1507511 : CollatzResearch.WordTrace tailWord_1507511 prefixEnd_1507511 774077734940156589979589 := by
  unfold tailWord_1507511
  simp only [CollatzResearch.WordTrace]
  refine ⟨54983443241552584226282387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36655628827701722817521591 54983443241552584226282387)
  ·
    refine ⟨82475164862328876339423581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54983443241552584226282387 82475164862328876339423581)
    ·
      refine ⟨30928186823373328627283843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82475164862328876339423581 30928186823373328627283843)
      ·
        refine ⟨46392280235059992940925765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30928186823373328627283843 46392280235059992940925765)
        ·
          refine ⟨8698552544073748676423581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46392280235059992940925765 8698552544073748676423581)
          ·
            refine ⟨3261957204027655753658843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8698552544073748676423581 3261957204027655753658843)
            ·
              refine ⟨4892935806041483630488265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3261957204027655753658843 4892935806041483630488265)
              ·
                refine ⟨3669701854531112722866199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4892935806041483630488265 3669701854531112722866199)
                ·
                  refine ⟨5504552781796669084299299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669701854531112722866199 5504552781796669084299299)
                  ·
                    refine ⟨8256829172695003626448949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5504552781796669084299299 8256829172695003626448949)
                    ·
                      refine ⟨774077734940156589979589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8256829172695003626448949 774077734940156589979589)
                      ·
                        rfl

theorem cell23_1507511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_1507511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507511 prefixEnd_1507511 := by exact prefixLift 1507511
  have htrace : WordTrace (prefixWord ++ tailWord_1507511) baseStart_1507511 baseEnd_1507511 := by
    simpa [prefixWord, tailWord_1507511, baseEnd_1507511] using wordTrace_append hprefix tailTrace_1507511
  have hstable : (prefixWord ++ tailWord_1507511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507511).length < 2 ^ (prefixWord ++ tailWord_1507511).sum := by decide
  have hdescent : baseEnd_1507511 < baseStart_1507511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507522 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1507522 : Nat := 118140960795 + 1507522 * 2 ^ 59
def prefixEnd_1507522 : Nat := 4983230072969 + 3 ^ 40 * 1507522 * 2
def baseEnd_1507522 : Nat := 258027794409118682314013

theorem tailTrace_1507522 : CollatzResearch.WordTrace tailWord_1507522 prefixEnd_1507522 258027794409118682314013 := by
  unfold tailWord_1507522
  simp only [CollatzResearch.WordTrace]
  refine ⟨13745961111128183276233205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36655896296341822069955213 13745961111128183276233205)
  ·
    refine ⟨1288683854168267182146863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13745961111128183276233205 1288683854168267182146863)
    ·
      refine ⟨1933025781252400773220295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1288683854168267182146863 1933025781252400773220295)
      ·
        refine ⟨2899538671878601159830443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1933025781252400773220295 2899538671878601159830443)
        ·
          refine ⟨4349308007817901739745665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2899538671878601159830443 4349308007817901739745665)
          ·
            refine ⟨3261981005863426304809249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4349308007817901739745665 3261981005863426304809249)
            ·
              refine ⟨2446485754397569728606937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3261981005863426304809249 2446485754397569728606937)
              ·
                refine ⟨1834864315798177296455203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2446485754397569728606937 1834864315798177296455203)
                ·
                  refine ⟨2752296473697265944682805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834864315798177296455203 2752296473697265944682805)
                  ·
                    refine ⟨258027794409118682314013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2752296473697265944682805 258027794409118682314013)
                    ·
                      rfl

theorem cell23_1507522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1507522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507522 prefixEnd_1507522 := by exact prefixLift 1507522
  have htrace : WordTrace (prefixWord ++ tailWord_1507522) baseStart_1507522 baseEnd_1507522 := by
    simpa [prefixWord, tailWord_1507522, baseEnd_1507522] using wordTrace_append hprefix tailTrace_1507522
  have hstable : (prefixWord ++ tailWord_1507522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507522).length < 2 ^ (prefixWord ++ tailWord_1507522).sum := by decide
  have hdescent : baseEnd_1507522 < baseStart_1507522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507601 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_1507601 : Nat := 118140960795 + 1507601 * 2 ^ 59
def prefixEnd_1507601 : Nat := 4983230072969 + 3 ^ 40 * 1507601 * 2
def baseEnd_1507601 : Nat := 774123948199061237854175

theorem tailTrace_1507601 : CollatzResearch.WordTrace tailWord_1507601 prefixEnd_1507601 774123948199061237854175 := by
  unfold tailWord_1507601
  simp only [CollatzResearch.WordTrace]
  refine ⟨54986725811226529597058657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36657817207484353064705771 54986725811226529597058657)
  ·
    refine ⟨41240044358419897197793993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54986725811226529597058657 41240044358419897197793993)
    ·
      refine ⟨30930033268814922898345495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41240044358419897197793993 30930033268814922898345495)
      ·
        refine ⟨46395049903222384347518243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30930033268814922898345495 46395049903222384347518243)
        ·
          refine ⟨69592574854833576521277365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46395049903222384347518243 69592574854833576521277365)
          ·
            refine ⟨6524303892640647798869753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69592574854833576521277365 6524303892640647798869753)
            ·
              refine ⟨4893227919480485849152315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6524303892640647798869753 4893227919480485849152315)
              ·
                refine ⟨7339841879220728773728473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893227919480485849152315 7339841879220728773728473)
                ·
                  refine ⟨5504881409415546580296355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7339841879220728773728473 5504881409415546580296355)
                  ·
                    refine ⟨8257322114123319870444533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5504881409415546580296355 8257322114123319870444533)
                    ·
                      refine ⟨774123948199061237854175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8257322114123319870444533 774123948199061237854175)
                      ·
                        rfl

theorem cell23_1507601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_1507601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507601 prefixEnd_1507601 := by exact prefixLift 1507601
  have htrace : WordTrace (prefixWord ++ tailWord_1507601) baseStart_1507601 baseEnd_1507601 := by
    simpa [prefixWord, tailWord_1507601, baseEnd_1507601] using wordTrace_append hprefix tailTrace_1507601
  have hstable : (prefixWord ++ tailWord_1507601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507601).length < 2 ^ (prefixWord ++ tailWord_1507601).sum := by decide
  have hdescent : baseEnd_1507601 < baseStart_1507601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507618 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_1507618 : Nat := 118140960795 + 1507618 * 2 ^ 59
def prefixEnd_1507618 : Nat := 4983230072969 + 3 ^ 40 * 1507618 * 2
def baseEnd_1507618 : Nat := 774132677370187671341597

theorem tailTrace_1507618 : CollatzResearch.WordTrace tailWord_1507618 prefixEnd_1507618 774132677370187671341597 := by
  unfold tailWord_1507618
  simp only [CollatzResearch.WordTrace]
  refine ⟨13746836463041235375106877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36658230568109961000285005 13746836463041235375106877)
  ·
    refine ⟨5155063673640463265665079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13746836463041235375106877 5155063673640463265665079)
    ·
      refine ⟨7732595510460694898497619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5155063673640463265665079 7732595510460694898497619)
      ·
        refine ⟨11598893265691042347746429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7732595510460694898497619 11598893265691042347746429)
        ·
          refine ⟨4349584974634140880404911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11598893265691042347746429 4349584974634140880404911)
          ·
            refine ⟨6524377461951211320607367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349584974634140880404911 6524377461951211320607367)
            ·
              refine ⟨9786566192926816980911051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6524377461951211320607367 9786566192926816980911051)
              ·
                refine ⟨14679849289390225471366577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9786566192926816980911051 14679849289390225471366577)
                ·
                  refine ⟨11009886967042669103524933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14679849289390225471366577 11009886967042669103524933)
                  ·
                    refine ⟨2064353806320500456910925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11009886967042669103524933 2064353806320500456910925)
                    ·
                      refine ⟨774132677370187671341597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2064353806320500456910925 774132677370187671341597)
                      ·
                        rfl

theorem cell23_1507618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_1507618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507618 prefixEnd_1507618 := by exact prefixLift 1507618
  have htrace : WordTrace (prefixWord ++ tailWord_1507618) baseStart_1507618 baseEnd_1507618 := by
    simpa [prefixWord, tailWord_1507618, baseEnd_1507618] using wordTrace_append hprefix tailTrace_1507618
  have hstable : (prefixWord ++ tailWord_1507618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507618).length < 2 ^ (prefixWord ++ tailWord_1507618).sum := by decide
  have hdescent : baseEnd_1507618 < baseStart_1507618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507631 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 3]
def baseStart_1507631 : Nat := 118140960795 + 1507631 * 2 ^ 59
def prefixEnd_1507631 : Nat := 4983230072969 + 3 ^ 40 * 1507631 * 2
def baseEnd_1507631 : Nat := 774139352618696120479037

theorem tailTrace_1507631 : CollatzResearch.WordTrace tailWord_1507631 prefixEnd_1507631 774139352618696120479037 := by
  unfold tailWord_1507631
  simp only [CollatzResearch.WordTrace]
  refine ⟨54987820001117844720650747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36658546667411896480433831 54987820001117844720650747)
  ·
    refine ⟨82481730001676767080976121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54987820001117844720650747 82481730001676767080976121)
    ·
      refine ⟨61861297501257575310732091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82481730001676767080976121 61861297501257575310732091)
      ·
        refine ⟨92791946251886362966098137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61861297501257575310732091 92791946251886362966098137)
        ·
          refine ⟨69593959688914772224573603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92791946251886362966098137 69593959688914772224573603)
          ·
            refine ⟨104390939533372158336860405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69593959688914772224573603 104390939533372158336860405)
            ·
              refine ⟨9786650581253639844080663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104390939533372158336860405 9786650581253639844080663)
              ·
                refine ⟨14679975871880459766120995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9786650581253639844080663 14679975871880459766120995)
                ·
                  refine ⟨22019963807820689649181493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14679975871880459766120995 22019963807820689649181493)
                  ·
                    refine ⟨2064371606983189654610765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22019963807820689649181493 2064371606983189654610765)
                    ·
                      refine ⟨774139352618696120479037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2064371606983189654610765 774139352618696120479037)
                      ·
                        rfl

theorem cell23_1507631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 3].length) (baseStart_1507631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507631 prefixEnd_1507631 := by exact prefixLift 1507631
  have htrace : WordTrace (prefixWord ++ tailWord_1507631) baseStart_1507631 baseEnd_1507631 := by
    simpa [prefixWord, tailWord_1507631, baseEnd_1507631] using wordTrace_append hprefix tailTrace_1507631
  have hstable : (prefixWord ++ tailWord_1507631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507631).length < 2 ^ (prefixWord ++ tailWord_1507631).sum := by decide
  have hdescent : baseEnd_1507631 < baseStart_1507631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507688 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1507688 : Nat := 118140960795 + 1507688 * 2 ^ 59
def prefixEnd_1507688 : Nat := 4983230072969 + 3 ^ 40 * 1507688 * 2
def baseEnd_1507688 : Nat := 774168621016002397466275

theorem tailTrace_1507688 : CollatzResearch.WordTrace tailWord_1507688 prefixEnd_1507688 774168621016002397466275 := by
  unfold tailWord_1507688
  simp only [CollatzResearch.WordTrace]
  refine ⟨27494949480955671727737859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36659932641274228970317145 27494949480955671727737859)
  ·
    refine ⟨41242424221433507591606789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27494949480955671727737859 41242424221433507591606789)
    ·
      refine ⟨7732954541518782673426273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41242424221433507591606789 7732954541518782673426273)
      ·
        refine ⟨5799715906139087005069705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7732954541518782673426273 5799715906139087005069705)
        ·
          refine ⟨4349786929604315253802279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5799715906139087005069705 4349786929604315253802279)
          ·
            refine ⟨6524680394406472880703419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349786929604315253802279 6524680394406472880703419)
            ·
              refine ⟨9787020591609709321055129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6524680394406472880703419 9787020591609709321055129)
              ·
                refine ⟨7340265443707281990791347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9787020591609709321055129 7340265443707281990791347)
                ·
                  refine ⟨11010398165560922986187021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7340265443707281990791347 11010398165560922986187021)
                  ·
                    refine ⟨4128899312085346119820133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11010398165560922986187021 4128899312085346119820133)
                    ·
                      refine ⟨774168621016002397466275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4128899312085346119820133 774168621016002397466275)
                      ·
                        rfl

theorem cell23_1507688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1507688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507688 prefixEnd_1507688 := by exact prefixLift 1507688
  have htrace : WordTrace (prefixWord ++ tailWord_1507688) baseStart_1507688 baseEnd_1507688 := by
    simpa [prefixWord, tailWord_1507688, baseEnd_1507688] using wordTrace_append hprefix tailTrace_1507688
  have hstable : (prefixWord ++ tailWord_1507688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507688).length < 2 ^ (prefixWord ++ tailWord_1507688).sum := by decide
  have hdescent : baseEnd_1507688 < baseStart_1507688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507722 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1507722 : Nat := 118140960795 + 1507722 * 2 ^ 59
def prefixEnd_1507722 : Nat := 4983230072969 + 3 ^ 40 * 1507722 * 2
def baseEnd_1507722 : Nat := 774186079358255264441119

theorem tailTrace_1507722 : CollatzResearch.WordTrace tailWord_1507722 prefixEnd_1507722 774186079358255264441119 := by
  unfold tailWord_1507722
  simp only [CollatzResearch.WordTrace]
  refine ⟨13747784760947041815553355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36660759362525444841475613 13747784760947041815553355)
  ·
    refine ⟨20621677141420562723330033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13747784760947041815553355 20621677141420562723330033)
    ·
      refine ⟨15466257856065422042497525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20621677141420562723330033 15466257856065422042497525)
      ·
        refine ⟨1449961674006133316484143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15466257856065422042497525 1449961674006133316484143)
        ·
          refine ⟨2174942511009199974726215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1449961674006133316484143 2174942511009199974726215)
          ·
            refine ⟨3262413766513799962089323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174942511009199974726215 3262413766513799962089323)
            ·
              refine ⟨4893620649770699943133985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3262413766513799962089323 4893620649770699943133985)
              ·
                refine ⟨3670215487328024957350489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4893620649770699943133985 3670215487328024957350489)
                ·
                  refine ⟨2752661615496018718012867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3670215487328024957350489 2752661615496018718012867)
                  ·
                    refine ⟨4128992423244028077019301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2752661615496018718012867 4128992423244028077019301)
                    ·
                      refine ⟨774186079358255264441119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4128992423244028077019301 774186079358255264441119)
                      ·
                        rfl

theorem cell23_1507722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1507722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507722 prefixEnd_1507722 := by exact prefixLift 1507722
  have htrace : WordTrace (prefixWord ++ tailWord_1507722) baseStart_1507722 baseEnd_1507722 := by
    simpa [prefixWord, tailWord_1507722, baseEnd_1507722] using wordTrace_append hprefix tailTrace_1507722
  have hstable : (prefixWord ++ tailWord_1507722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507722).length < 2 ^ (prefixWord ++ tailWord_1507722).sum := by decide
  have hdescent : baseEnd_1507722 < baseStart_1507722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507805 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1507805 : Nat := 118140960795 + 1507805 * 2 ^ 59
def prefixEnd_1507805 : Nat := 4983230072969 + 3 ^ 40 * 1507805 * 2
def baseEnd_1507805 : Nat := 258076232750859479901079

theorem tailTrace_1507805 : CollatzResearch.WordTrace tailWord_1507805 prefixEnd_1507805 258076232750859479901079 := by
  unfold tailWord_1507805
  simp only [CollatzResearch.WordTrace]
  refine ⟨54994166302487472437484869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36662777534991648291656579 54994166302487472437484869)
  ·
    refine ⟨10311406181716401082028413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54994166302487472437484869 10311406181716401082028413)
    ·
      refine ⟨3866777318143650405760655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10311406181716401082028413 3866777318143650405760655)
      ·
        refine ⟨5800165977215475608640983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866777318143650405760655 5800165977215475608640983)
        ·
          refine ⟨8700248965823213412961475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5800165977215475608640983 8700248965823213412961475)
          ·
            refine ⟨13050373448734820119442213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700248965823213412961475 13050373448734820119442213)
            ·
              refine ⟨2446945021637778772395415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13050373448734820119442213 2446945021637778772395415)
              ·
                refine ⟨3670417532456668158593123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446945021637778772395415 3670417532456668158593123)
                ·
                  refine ⟨5505626298685002237889685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3670417532456668158593123 5505626298685002237889685)
                  ·
                    refine ⟨258076232750859479901079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5505626298685002237889685 258076232750859479901079)
                    ·
                      rfl

theorem cell23_1507805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1507805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507805 prefixEnd_1507805 := by exact prefixLift 1507805
  have htrace : WordTrace (prefixWord ++ tailWord_1507805) baseStart_1507805 baseEnd_1507805 := by
    simpa [prefixWord, tailWord_1507805, baseEnd_1507805] using wordTrace_append hprefix tailTrace_1507805
  have hstable : (prefixWord ++ tailWord_1507805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507805).length < 2 ^ (prefixWord ++ tailWord_1507805).sum := by decide
  have hdescent : baseEnd_1507805 < baseStart_1507805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507815 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1507815 : Nat := 118140960795 + 1507815 * 2 ^ 59
def prefixEnd_1507815 : Nat := 4983230072969 + 3 ^ 40 * 1507815 * 2
def baseEnd_1507815 : Nat := 774233833059123400578191

theorem tailTrace_1507815 : CollatzResearch.WordTrace tailWord_1507815 prefixEnd_1507815 774233833059123400578191 := by
  unfold tailWord_1507815
  simp only [CollatzResearch.WordTrace]
  refine ⟨54994531032451244145348899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36663020688300829430232599 54994531032451244145348899)
  ·
    refine ⟨82491796548676866218023349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54994531032451244145348899 82491796548676866218023349)
    ·
      refine ⟨7733605926438456207939689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82491796548676866218023349 7733605926438456207939689)
      ·
        refine ⟨5800204444828842155954767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7733605926438456207939689 5800204444828842155954767)
        ·
          refine ⟨8700306667243263233932151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5800204444828842155954767 8700306667243263233932151)
          ·
            refine ⟨13050460000864894850898227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700306667243263233932151 13050460000864894850898227)
            ·
              refine ⟨19575690001297342276347341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13050460000864894850898227 19575690001297342276347341)
              ·
                refine ⟨7340883750486503353630253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19575690001297342276347341 7340883750486503353630253)
                ·
                  refine ⟨2752831406432438757611345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7340883750486503353630253 2752831406432438757611345)
                  ·
                    refine ⟨2064623554824329068208509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2752831406432438757611345 2064623554824329068208509)
                    ·
                      refine ⟨774233833059123400578191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2064623554824329068208509 774233833059123400578191)
                      ·
                        rfl

theorem cell23_1507815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1507815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507815 prefixEnd_1507815 := by exact prefixLift 1507815
  have htrace : WordTrace (prefixWord ++ tailWord_1507815) baseStart_1507815 baseEnd_1507815 := by
    simpa [prefixWord, tailWord_1507815, baseEnd_1507815] using wordTrace_append hprefix tailTrace_1507815
  have hstable : (prefixWord ++ tailWord_1507815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507815).length < 2 ^ (prefixWord ++ tailWord_1507815).sum := by decide
  have hdescent : baseEnd_1507815 < baseStart_1507815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507826 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_1507826 : Nat := 118140960795 + 1507826 * 2 ^ 59
def prefixEnd_1507826 : Nat := 4983230072969 + 3 ^ 40 * 1507826 * 2
def baseEnd_1507826 : Nat := 258079827115440952513547

theorem tailTrace_1507826 : CollatzResearch.WordTrace tailWord_1507826 prefixEnd_1507826 258079827115440952513547 := by
  unfold tailWord_1507826
  simp only [CollatzResearch.WordTrace]
  refine ⟨13748733058852848255999833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36663288156940928682666221 13748733058852848255999833)
  ·
    refine ⟨10311549794139636191999875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13748733058852848255999833 10311549794139636191999875)
    ·
      refine ⟨15467324691209454287999813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10311549794139636191999875 15467324691209454287999813)
      ·
        refine ⟨2900123379601772678999965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15467324691209454287999813 2900123379601772678999965)
        ·
          refine ⟨1087546267350664754624987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2900123379601772678999965 1087546267350664754624987)
          ·
            refine ⟨1631319401025997131937481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087546267350664754624987 1631319401025997131937481)
            ·
              refine ⟨1223489550769497848953111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631319401025997131937481 1223489550769497848953111)
              ·
                refine ⟨1835234326154246773429667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223489550769497848953111 1835234326154246773429667)
                ·
                  refine ⟨2752851489231370160144501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1835234326154246773429667 2752851489231370160144501)
                  ·
                    refine ⟨258079827115440952513547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2752851489231370160144501 258079827115440952513547)
                    ·
                      rfl

theorem cell23_1507826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_1507826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507826 prefixEnd_1507826 := by exact prefixLift 1507826
  have htrace : WordTrace (prefixWord ++ tailWord_1507826) baseStart_1507826 baseEnd_1507826 := by
    simpa [prefixWord, tailWord_1507826, baseEnd_1507826] using wordTrace_append hprefix tailTrace_1507826
  have hstable : (prefixWord ++ tailWord_1507826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507826).length < 2 ^ (prefixWord ++ tailWord_1507826).sum := by decide
  have hdescent : baseEnd_1507826 < baseStart_1507826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507829 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1507829 : Nat := 118140960795 + 1507829 * 2 ^ 59
def prefixEnd_1507829 : Nat := 4983230072969 + 3 ^ 40 * 1507829 * 2
def baseEnd_1507829 : Nat := 774241021788286345803127

theorem tailTrace_1507829 : CollatzResearch.WordTrace tailWord_1507829 prefixEnd_1507829 774241021788286345803127 := by
  unfold tailWord_1507829
  simp only [CollatzResearch.WordTrace]
  refine ⟨54995041654400524536358541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36663361102933683024239027 54995041654400524536358541)
  ·
    refine ⟨20623140620400196701134453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54995041654400524536358541 20623140620400196701134453)
    ·
      refine ⟨1933419433162518440731355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20623140620400196701134453 1933419433162518440731355)
      ·
        refine ⟨2900129149743777661097033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1933419433162518440731355 2900129149743777661097033)
        ·
          refine ⟨2175096862307833245822775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2900129149743777661097033 2175096862307833245822775)
          ·
            refine ⟨3262645293461749868734163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175096862307833245822775 3262645293461749868734163)
            ·
              refine ⟨4893967940192624803101245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3262645293461749868734163 4893967940192624803101245)
              ·
                refine ⟨1835237977572234301162967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4893967940192624803101245 1835237977572234301162967)
                ·
                  refine ⟨2752856966358351451744451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1835237977572234301162967 2752856966358351451744451)
                  ·
                    refine ⟨4129285449537527177616677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2752856966358351451744451 4129285449537527177616677)
                    ·
                      refine ⟨774241021788286345803127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4129285449537527177616677 774241021788286345803127)
                      ·
                        rfl

theorem cell23_1507829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1507829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507829 prefixEnd_1507829 := by exact prefixLift 1507829
  have htrace : WordTrace (prefixWord ++ tailWord_1507829) baseStart_1507829 baseEnd_1507829 := by
    simpa [prefixWord, tailWord_1507829, baseEnd_1507829] using wordTrace_append hprefix tailTrace_1507829
  have hstable : (prefixWord ++ tailWord_1507829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507829).length < 2 ^ (prefixWord ++ tailWord_1507829).sum := by decide
  have hdescent : baseEnd_1507829 < baseStart_1507829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507888 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_1507888 : Nat := 118140960795 + 1507888 * 2 ^ 59
def prefixEnd_1507888 : Nat := 4983230072969 + 3 ^ 40 * 1507888 * 2
def baseEnd_1507888 : Nat := 774271317146901614965355

theorem tailTrace_1507888 : CollatzResearch.WordTrace tailWord_1507888 prefixEnd_1507888 774271317146901614965355 := by
  unfold tailWord_1507888
  simp only [CollatzResearch.WordTrace]
  refine ⟨27498596780593388806378159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36664795707457851741837545 27498596780593388806378159)
  ·
    refine ⟨41247895170890083209567239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27498596780593388806378159 41247895170890083209567239)
    ·
      refine ⟨61871842756335124814350859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41247895170890083209567239 61871842756335124814350859)
      ·
        refine ⟨92807764134502687221526289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61871842756335124814350859 92807764134502687221526289)
        ·
          refine ⟨69605823100877015416144717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92807764134502687221526289 69605823100877015416144717)
          ·
            refine ⟨26102183662828880781054269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69605823100877015416144717 26102183662828880781054269)
            ·
              refine ⟨9788318873560830292895351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26102183662828880781054269 9788318873560830292895351)
              ·
                refine ⟨14682478310341245439343027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9788318873560830292895351 14682478310341245439343027)
                ·
                  refine ⟨22023717465511868159014541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14682478310341245439343027 22023717465511868159014541)
                  ·
                    refine ⟨8258894049566950559630453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22023717465511868159014541 8258894049566950559630453)
                    ·
                      refine ⟨774271317146901614965355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8258894049566950559630453 774271317146901614965355)
                      ·
                        rfl

theorem cell23_1507888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_1507888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507888 prefixEnd_1507888 := by exact prefixLift 1507888
  have htrace : WordTrace (prefixWord ++ tailWord_1507888) baseStart_1507888 baseEnd_1507888 := by
    simpa [prefixWord, tailWord_1507888, baseEnd_1507888] using wordTrace_append hprefix tailTrace_1507888
  have hstable : (prefixWord ++ tailWord_1507888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507888).length < 2 ^ (prefixWord ++ tailWord_1507888).sum := by decide
  have hdescent : baseEnd_1507888 < baseStart_1507888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507970 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1507970 : Nat := 118140960795 + 1507970 * 2 ^ 59
def prefixEnd_1507970 : Nat := 4983230072969 + 3 ^ 40 * 1507970 * 2
def baseEnd_1507970 : Nat := 774313422560570294139979

theorem tailTrace_1507970 : CollatzResearch.WordTrace tailWord_1507970 prefixEnd_1507970 774313422560570294139979 := by
  unfold tailWord_1507970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13750046086722426404310341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36666789564593137078160909 13750046086722426404310341)
  ·
    refine ⟨2578133641260454950808189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13750046086722426404310341 2578133641260454950808189)
    ·
      refine ⟨966800115472670606553071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2578133641260454950808189 966800115472670606553071)
      ·
        refine ⟨1450200173209005909829607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966800115472670606553071 1450200173209005909829607)
        ·
          refine ⟨2175300259813508864744411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450200173209005909829607 2175300259813508864744411)
          ·
            refine ⟨3262950389720263297116617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175300259813508864744411 3262950389720263297116617)
            ·
              refine ⟨2447212792290197472837463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3262950389720263297116617 2447212792290197472837463)
              ·
                refine ⟨3670819188435296209256195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447212792290197472837463 3670819188435296209256195)
                ·
                  refine ⟨5506228782652944313884293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3670819188435296209256195 5506228782652944313884293)
                  ·
                    refine ⟨1032417896747427058853305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5506228782652944313884293 1032417896747427058853305)
                    ·
                      refine ⟨774313422560570294139979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1032417896747427058853305 774313422560570294139979)
                      ·
                        rfl

theorem cell23_1507970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1507970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507970 prefixEnd_1507970 := by exact prefixLift 1507970
  have htrace : WordTrace (prefixWord ++ tailWord_1507970) baseStart_1507970 baseEnd_1507970 := by
    simpa [prefixWord, tailWord_1507970, baseEnd_1507970] using wordTrace_append hprefix tailTrace_1507970
  have hstable : (prefixWord ++ tailWord_1507970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507970).length < 2 ^ (prefixWord ++ tailWord_1507970).sum := by decide
  have hdescent : baseEnd_1507970 < baseStart_1507970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507975 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1507975 : Nat := 118140960795 + 1507975 * 2 ^ 59
def prefixEnd_1507975 : Nat := 4983230072969 + 3 ^ 40 * 1507975 * 2
def baseEnd_1507975 : Nat := 774315989963842774577455

theorem tailTrace_1507975 : CollatzResearch.WordTrace tailWord_1507975 prefixEnd_1507975 774315989963842774577455 := by
  unfold tailWord_1507975
  simp only [CollatzResearch.WordTrace]
  refine ⟨55000366711871591471173379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36666911141247727647448919 55000366711871591471173379)
  ·
    refine ⟨82500550067807387206760069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55000366711871591471173379 82500550067807387206760069)
    ·
      refine ⟨15468853137713885101267513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82500550067807387206760069 15468853137713885101267513)
      ·
        refine ⟨11601639853285413825950635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15468853137713885101267513 11601639853285413825950635)
        ·
          refine ⟨17402459779928120738925953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11601639853285413825950635 17402459779928120738925953)
          ·
            refine ⟨13051844834946090554194465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17402459779928120738925953 13051844834946090554194465)
            ·
              refine ⟨9788883626209567915645849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13051844834946090554194465 9788883626209567915645849)
              ·
                refine ⟨7341662719657175936734387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9788883626209567915645849 7341662719657175936734387)
                ·
                  refine ⟨11012494079485763905101581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7341662719657175936734387 11012494079485763905101581)
                  ·
                    refine ⟨4129685279807161464413093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11012494079485763905101581 4129685279807161464413093)
                    ·
                      refine ⟨774315989963842774577455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4129685279807161464413093 774315989963842774577455)
                      ·
                        rfl

theorem cell23_1507975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1507975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507975 prefixEnd_1507975 := by exact prefixLift 1507975
  have htrace : WordTrace (prefixWord ++ tailWord_1507975) baseStart_1507975 baseEnd_1507975 := by
    simpa [prefixWord, tailWord_1507975, baseEnd_1507975] using wordTrace_append hprefix tailTrace_1507975
  have hstable : (prefixWord ++ tailWord_1507975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507975).length < 2 ^ (prefixWord ++ tailWord_1507975).sum := by decide
  have hdescent : baseEnd_1507975 < baseStart_1507975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507992 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 1, 6, 2]
def baseStart_1507992 : Nat := 118140960795 + 1507992 * 2 ^ 59
def prefixEnd_1507992 : Nat := 4983230072969 + 3 ^ 40 * 1507992 * 2
def baseEnd_1507992 : Nat := 774324719134969208064877

theorem tailTrace_1507992 : CollatzResearch.WordTrace tailWord_1507992 prefixEnd_1507992 774324719134969208064877 := by
  unfold tailWord_1507992
  simp only [CollatzResearch.WordTrace]
  refine ⟨27500493376405001687271115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36667324501873335583028153 27500493376405001687271115)
  ·
    refine ⟨41250740064607502530906673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27500493376405001687271115 41250740064607502530906673)
    ·
      refine ⟨30938055048455626898180005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41250740064607502530906673 30938055048455626898180005)
      ·
        refine ⟨5800885321585430043408751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30938055048455626898180005 5800885321585430043408751)
        ·
          refine ⟨8701327982378145065113127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5800885321585430043408751 8701327982378145065113127)
          ·
            refine ⟨13051991973567217597669691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8701327982378145065113127 13051991973567217597669691)
            ·
              refine ⟨19577987960350826396504537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13051991973567217597669691 19577987960350826396504537)
              ·
                refine ⟨14683490970263119797378403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19577987960350826396504537 14683490970263119797378403)
                ·
                  refine ⟨22025236455394679696067605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14683490970263119797378403 22025236455394679696067605)
                  ·
                    refine ⟨1032432958846625610753169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22025236455394679696067605 1032432958846625610753169)
                    ·
                      refine ⟨774324719134969208064877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1032432958846625610753169 774324719134969208064877)
                      ·
                        rfl

theorem cell23_1507992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_1507992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1507992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1507992 prefixEnd_1507992 := by exact prefixLift 1507992
  have htrace : WordTrace (prefixWord ++ tailWord_1507992) baseStart_1507992 baseEnd_1507992 := by
    simpa [prefixWord, tailWord_1507992, baseEnd_1507992] using wordTrace_append hprefix tailTrace_1507992
  have hstable : (prefixWord ++ tailWord_1507992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507992).length < 2 ^ (prefixWord ++ tailWord_1507992).sum := by decide
  have hdescent : baseEnd_1507992 < baseStart_1507992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508015 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 8]
def baseStart_1508015 : Nat := 118140960795 + 1508015 * 2 ^ 59
def prefixEnd_1508015 : Nat := 4983230072969 + 3 ^ 40 * 1508015 * 2
def baseEnd_1508015 : Nat := 86037392132224735341919

theorem tailTrace_1508015 : CollatzResearch.WordTrace tailWord_1508015 prefixEnd_1508015 86037392132224735341919 := by
  unfold tailWord_1508015
  simp only [CollatzResearch.WordTrace]
  refine ⟨55001825631726678302629499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36667883754484452201752999 55001825631726678302629499)
  ·
    refine ⟨82502738447590017453944249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55001825631726678302629499 82502738447590017453944249)
    ·
      refine ⟨61877053835692513090458187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82502738447590017453944249 61877053835692513090458187)
      ·
        refine ⟨92815580753538769635687281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61877053835692513090458187 92815580753538769635687281)
        ·
          refine ⟨69611685565154077226765461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92815580753538769635687281 69611685565154077226765461)
          ·
            refine ⟨3263047760866597370004631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69611685565154077226765461 3263047760866597370004631)
            ·
              refine ⟨4894571641299896055006947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263047760866597370004631 4894571641299896055006947)
              ·
                refine ⟨7341857461949844082510421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4894571641299896055006947 7341857461949844082510421)
                ·
                  refine ⟨86037392132224735341919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7341857461949844082510421 86037392132224735341919)
                  ·
                    rfl

theorem cell23_1508015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 8].length) (baseStart_1508015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508015 prefixEnd_1508015 := by exact prefixLift 1508015
  have htrace : WordTrace (prefixWord ++ tailWord_1508015) baseStart_1508015 baseEnd_1508015 := by
    simpa [prefixWord, tailWord_1508015, baseEnd_1508015] using wordTrace_append hprefix tailTrace_1508015
  have hstable : (prefixWord ++ tailWord_1508015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508015).length < 2 ^ (prefixWord ++ tailWord_1508015).sum := by decide
  have hdescent : baseEnd_1508015 < baseStart_1508015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508019 : List Nat := [1, 1, 1, 2, 3, 4, 2, 4, 1, 4]
def baseStart_1508019 : Nat := 118140960795 + 1508019 * 2 ^ 59
def prefixEnd_1508019 : Nat := 4983230072969 + 3 ^ 40 * 1508019 * 2
def baseEnd_1508019 : Nat := 258112861037546867475751

theorem tailTrace_1508019 : CollatzResearch.WordTrace tailWord_1508019 prefixEnd_1508019 258112861037546867475751 := by
  unfold tailWord_1508019
  simp only [CollatzResearch.WordTrace]
  refine ⟨55001971523712186985775111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36667981015808124657183407 55001971523712186985775111)
  ·
    refine ⟨82502957285568280478662667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55001971523712186985775111 82502957285568280478662667)
    ·
      refine ⟨123754435928352420717994001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82502957285568280478662667 123754435928352420717994001)
      ·
        refine ⟨92815826946264315538495501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123754435928352420717994001 92815826946264315538495501)
        ·
          refine ⟨34805935104849118326935813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92815826946264315538495501 34805935104849118326935813)
          ·
            refine ⟨6526112832159209686300465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34805935104849118326935813 6526112832159209686300465)
            ·
              refine ⟨4894584624119407264725349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6526112832159209686300465 4894584624119407264725349)
              ·
                refine ⟨917734617022388862136003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4894584624119407264725349 917734617022388862136003)
                ·
                  refine ⟨1376601925533583293204005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 917734617022388862136003 1376601925533583293204005)
                  ·
                    refine ⟨258112861037546867475751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1376601925533583293204005 258112861037546867475751)
                    ·
                      rfl

theorem cell23_1508019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 1, 4].length) (baseStart_1508019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508019 prefixEnd_1508019 := by exact prefixLift 1508019
  have htrace : WordTrace (prefixWord ++ tailWord_1508019) baseStart_1508019 baseEnd_1508019 := by
    simpa [prefixWord, tailWord_1508019, baseEnd_1508019] using wordTrace_append hprefix tailTrace_1508019
  have hstable : (prefixWord ++ tailWord_1508019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508019).length < 2 ^ (prefixWord ++ tailWord_1508019).sum := by decide
  have hdescent : baseEnd_1508019 < baseStart_1508019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508069 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 4, 3, 2]
def baseStart_1508069 : Nat := 118140960795 + 1508069 * 2 ^ 59
def prefixEnd_1508069 : Nat := 4983230072969 + 3 ^ 40 * 1508069 * 2
def baseEnd_1508069 : Nat := 774364257145365406802023

theorem tailTrace_1508069 : CollatzResearch.WordTrace tailWord_1508069 prefixEnd_1508069 774364257145365406802023 := by
  unfold tailWord_1508069
  simp only [CollatzResearch.WordTrace]
  refine ⟨55003795173531045525095261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36669196782354030350063507 55003795173531045525095261)
  ·
    refine ⟨20626423190074142071910723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55003795173531045525095261 20626423190074142071910723)
    ·
      refine ⟨30939634785111213107866085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20626423190074142071910723 30939634785111213107866085)
      ·
        refine ⟨5801181522208352457724891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30939634785111213107866085 5801181522208352457724891)
        ·
          refine ⟨8701772283312528686587337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5801181522208352457724891 8701772283312528686587337)
          ·
            refine ⟨6526329212484396514940503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8701772283312528686587337 6526329212484396514940503)
            ·
              refine ⟨9789493818726594772410755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6526329212484396514940503 9789493818726594772410755)
              ·
                refine ⟨14684240728089892158616133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9789493818726594772410755 14684240728089892158616133)
                ·
                  refine ⟨2753295136516854779740525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14684240728089892158616133 2753295136516854779740525)
                  ·
                    refine ⟨1032485676193820542402697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2753295136516854779740525 1032485676193820542402697)
                    ·
                      refine ⟨774364257145365406802023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1032485676193820542402697 774364257145365406802023)
                      ·
                        rfl

theorem cell23_1508069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_1508069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508069 prefixEnd_1508069 := by exact prefixLift 1508069
  have htrace : WordTrace (prefixWord ++ tailWord_1508069) baseStart_1508069 baseEnd_1508069 := by
    simpa [prefixWord, tailWord_1508069, baseEnd_1508069] using wordTrace_append hprefix tailTrace_1508069
  have hstable : (prefixWord ++ tailWord_1508069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508069).length < 2 ^ (prefixWord ++ tailWord_1508069).sum := by decide
  have hdescent : baseEnd_1508069 < baseStart_1508069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508099 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 5, 2, 2]
def baseStart_1508099 : Nat := 118140960795 + 1508099 * 2 ^ 59
def prefixEnd_1508099 : Nat := 4983230072969 + 3 ^ 40 * 1508099 * 2
def baseEnd_1508099 : Nat := 774379661565000289426885

theorem tailTrace_1508099 : CollatzResearch.WordTrace tailWord_1508099 prefixEnd_1508099 774379661565000289426885 := by
  unfold tailWord_1508099
  simp only [CollatzResearch.WordTrace]
  refine ⟨55004889363422360648687351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36669926242281573765791567 55004889363422360648687351)
  ·
    refine ⟨82507334045133540973031027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55004889363422360648687351 82507334045133540973031027)
    ·
      refine ⟨123761001067700311459546541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82507334045133540973031027 123761001067700311459546541)
      ·
        refine ⟨46410375400387616797329953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123761001067700311459546541 46410375400387616797329953)
        ·
          refine ⟨34807781550290712597997465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46410375400387616797329953 34807781550290712597997465)
          ·
            refine ⟨26105836162718034448498099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34807781550290712597997465 26105836162718034448498099)
            ·
              refine ⟨39158754244077051672747149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26105836162718034448498099 39158754244077051672747149)
              ·
                refine ⟨14684532841528894377280181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39158754244077051672747149 14684532841528894377280181)
                ·
                  refine ⟨1376674953893333847870017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14684532841528894377280181 1376674953893333847870017)
                  ·
                    refine ⟨1032506215420000385902513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1376674953893333847870017 1032506215420000385902513)
                    ·
                      refine ⟨774379661565000289426885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1032506215420000385902513 774379661565000289426885)
                      ·
                        rfl

theorem cell23_1508099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 2, 2].length) (baseStart_1508099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508099 prefixEnd_1508099 := by exact prefixLift 1508099
  have htrace : WordTrace (prefixWord ++ tailWord_1508099) baseStart_1508099 baseEnd_1508099 := by
    simpa [prefixWord, tailWord_1508099, baseEnd_1508099] using wordTrace_append hprefix tailTrace_1508099
  have hstable : (prefixWord ++ tailWord_1508099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508099).length < 2 ^ (prefixWord ++ tailWord_1508099).sum := by decide
  have hdescent : baseEnd_1508099 < baseStart_1508099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508105 : List Nat := [1, 2, 1, 1, 3, 2, 4, 9]
def baseStart_1508105 : Nat := 118140960795 + 1508105 * 2 ^ 59
def prefixEnd_1508105 : Nat := 4983230072969 + 3 ^ 40 * 1508105 * 2
def baseEnd_1508105 : Nat := 28680842312923232072291

theorem tailTrace_1508105 : CollatzResearch.WordTrace tailWord_1508105 prefixEnd_1508105 28680842312923232072291 := by
  unfold tailWord_1508105
  simp only [CollatzResearch.WordTrace]
  refine ⟨55005108201400623673405769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36670072134267082448937179 55005108201400623673405769)
  ·
    refine ⟨41253831151050467755054327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55005108201400623673405769 41253831151050467755054327)
    ·
      refine ⟨61880746726575701632581491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41253831151050467755054327 61880746726575701632581491)
      ·
        refine ⟨92821120089863552448872237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61880746726575701632581491 92821120089863552448872237)
        ·
          refine ⟨34807920033698832168327089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92821120089863552448872237 34807920033698832168327089)
          ·
            refine ⟨26105940025274124126245317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34807920033698832168327089 26105940025274124126245317)
            ·
              refine ⟨4894863754738898273670997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26105940025274124126245317 4894863754738898273670997)
              ·
                refine ⟨28680842312923232072291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4894863754738898273670997 28680842312923232072291)
                ·
                  rfl

theorem cell23_1508105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 9].length) (baseStart_1508105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508105 prefixEnd_1508105 := by exact prefixLift 1508105
  have htrace : WordTrace (prefixWord ++ tailWord_1508105) baseStart_1508105 baseEnd_1508105 := by
    simpa [prefixWord, tailWord_1508105, baseEnd_1508105] using wordTrace_append hprefix tailTrace_1508105
  have hstable : (prefixWord ++ tailWord_1508105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508105).length < 2 ^ (prefixWord ++ tailWord_1508105).sum := by decide
  have hdescent : baseEnd_1508105 < baseStart_1508105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508133 : List Nat := [1, 3, 1, 2, 3, 1, 3, 4, 1, 2, 2]
def baseStart_1508133 : Nat := 118140960795 + 1508133 * 2 ^ 59
def prefixEnd_1508133 : Nat := 4983230072969 + 3 ^ 40 * 1508133 * 2
def baseEnd_1508133 : Nat := 774397119907253156401729

theorem tailTrace_1508133 : CollatzResearch.WordTrace tailWord_1508133 prefixEnd_1508133 774397119907253156401729 := by
  unfold tailWord_1508133
  simp only [CollatzResearch.WordTrace]
  refine ⟨55006129445299184455425053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36670752963532789636950035 55006129445299184455425053)
  ·
    refine ⟨20627298541987194170784395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55006129445299184455425053 20627298541987194170784395)
    ·
      refine ⟨30940947812980791256176593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20627298541987194170784395 30940947812980791256176593)
      ·
        refine ⟨23205710859735593442132445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30940947812980791256176593 23205710859735593442132445)
        ·
          refine ⟨8702141572400847540799667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23205710859735593442132445 8702141572400847540799667)
          ·
            refine ⟨13053212358601271311199501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8702141572400847540799667 13053212358601271311199501)
            ·
              refine ⟨4894954634475476741699813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13053212358601271311199501 4894954634475476741699813)
              ·
                refine ⟨917803993964151889068715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4894954634475476741699813 917803993964151889068715)
                ·
                  refine ⟨1376705990946227833603073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 917803993964151889068715 1376705990946227833603073)
                  ·
                    refine ⟨1032529493209670875202305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1376705990946227833603073 1032529493209670875202305)
                    ·
                      refine ⟨774397119907253156401729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1032529493209670875202305 774397119907253156401729)
                      ·
                        rfl

theorem cell23_1508133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_1508133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508133 prefixEnd_1508133 := by exact prefixLift 1508133
  have htrace : WordTrace (prefixWord ++ tailWord_1508133) baseStart_1508133 baseEnd_1508133 := by
    simpa [prefixWord, tailWord_1508133, baseEnd_1508133] using wordTrace_append hprefix tailTrace_1508133
  have hstable : (prefixWord ++ tailWord_1508133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508133).length < 2 ^ (prefixWord ++ tailWord_1508133).sum := by decide
  have hdescent : baseEnd_1508133 < baseStart_1508133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508149 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_1508149 : Nat := 118140960795 + 1508149 * 2 ^ 59
def prefixEnd_1508149 : Nat := 4983230072969 + 3 ^ 40 * 1508149 * 2
def baseEnd_1508149 : Nat := 774405335597725093801655

theorem tailTrace_1508149 : CollatzResearch.WordTrace tailWord_1508149 prefixEnd_1508149 774405335597725093801655 := by
  unfold tailWord_1508149
  simp only [CollatzResearch.WordTrace]
  refine ⟨55006713013241219188007501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36671142008827479458671667 55006713013241219188007501)
  ·
    refine ⟨20627517379965457195502813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55006713013241219188007501 20627517379965457195502813)
    ·
      refine ⟨7735319017487046448313555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20627517379965457195502813 7735319017487046448313555)
      ·
        refine ⟨11602978526230569672470333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7735319017487046448313555 11602978526230569672470333)
        ·
          refine ⟨4351116947336463627176375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11602978526230569672470333 4351116947336463627176375)
          ·
            refine ⟨6526675421004695440764563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351116947336463627176375 6526675421004695440764563)
            ·
              refine ⟨9790013131507043161146845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6526675421004695440764563 9790013131507043161146845)
              ·
                refine ⟨3671254924315141185430067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9790013131507043161146845 3671254924315141185430067)
                ·
                  refine ⟨5506882386472711778145101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671254924315141185430067 5506882386472711778145101)
                  ·
                    refine ⟨2065080894927266916804413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5506882386472711778145101 2065080894927266916804413)
                    ·
                      refine ⟨774405335597725093801655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2065080894927266916804413 774405335597725093801655)
                      ·
                        rfl

theorem cell23_1508149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_1508149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508149 prefixEnd_1508149 := by exact prefixLift 1508149
  have htrace : WordTrace (prefixWord ++ tailWord_1508149) baseStart_1508149 baseEnd_1508149 := by
    simpa [prefixWord, tailWord_1508149, baseEnd_1508149] using wordTrace_append hprefix tailTrace_1508149
  have hstable : (prefixWord ++ tailWord_1508149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508149).length < 2 ^ (prefixWord ++ tailWord_1508149).sum := by decide
  have hdescent : baseEnd_1508149 < baseStart_1508149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508150 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_1508150 : Nat := 118140960795 + 1508150 * 2 ^ 59
def prefixEnd_1508150 : Nat := 4983230072969 + 3 ^ 40 * 1508150 * 2
def baseEnd_1508150 : Nat := 774405849078379589889151

theorem tailTrace_1508150 : CollatzResearch.WordTrace tailWord_1508150 prefixEnd_1508150 774405849078379589889151 := by
  unfold tailWord_1508150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437921842889849772424619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36671166324158397572529269 3437921842889849772424619)
  ·
    refine ⟨5156882764334774658636929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3437921842889849772424619 5156882764334774658636929)
    ·
      refine ⟨3867662073251080993977697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5156882764334774658636929 3867662073251080993977697)
      ·
        refine ⟨2900746554938310745483273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3867662073251080993977697 2900746554938310745483273)
        ·
          refine ⟨2175559916203733059112455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2900746554938310745483273 2175559916203733059112455)
          ·
            refine ⟨3263339874305599588668683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175559916203733059112455 3263339874305599588668683)
            ·
              refine ⟨4895009811458399383003025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263339874305599588668683 4895009811458399383003025)
              ·
                refine ⟨3671257358593799537252269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4895009811458399383003025 3671257358593799537252269)
                ·
                  refine ⟨1376721509472674826469601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3671257358593799537252269 1376721509472674826469601)
                  ·
                    refine ⟨1032541132104506119852201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1376721509472674826469601 1032541132104506119852201)
                    ·
                      refine ⟨774405849078379589889151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1032541132104506119852201 774405849078379589889151)
                      ·
                        rfl

theorem cell23_1508150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_1508150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508150 prefixEnd_1508150 := by exact prefixLift 1508150
  have htrace : WordTrace (prefixWord ++ tailWord_1508150) baseStart_1508150 baseEnd_1508150 := by
    simpa [prefixWord, tailWord_1508150, baseEnd_1508150] using wordTrace_append hprefix tailTrace_1508150
  have hstable : (prefixWord ++ tailWord_1508150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508150).length < 2 ^ (prefixWord ++ tailWord_1508150).sum := by decide
  have hdescent : baseEnd_1508150 < baseStart_1508150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508183 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 2, 1, 3]
def baseStart_1508183 : Nat := 118140960795 + 1508183 * 2 ^ 59
def prefixEnd_1508183 : Nat := 4983230072969 + 3 ^ 40 * 1508183 * 2
def baseEnd_1508183 : Nat := 774422793939977960776499

theorem tailTrace_1508183 : CollatzResearch.WordTrace tailWord_1508183 prefixEnd_1508183 774422793939977960776499 := by
  unfold tailWord_1508183
  simp only [CollatzResearch.WordTrace]
  refine ⟨55007953095118042994745203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36671968730078695329830135 55007953095118042994745203)
  ·
    refine ⟨82511929642677064492117805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55007953095118042994745203 82511929642677064492117805)
    ·
      refine ⟨30941973616003899184544177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82511929642677064492117805 30941973616003899184544177)
      ·
        refine ⟨23206480212002924388408133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30941973616003899184544177 23206480212002924388408133)
        ·
          refine ⟨4351215039750548322826525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23206480212002924388408133 4351215039750548322826525)
          ·
            refine ⟨1631705639906455621059947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4351215039750548322826525 1631705639906455621059947)
            ·
              refine ⟨2447558459859683431589921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631705639906455621059947 2447558459859683431589921)
              ·
                refine ⟨1835668844894762573692441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2447558459859683431589921 1835668844894762573692441)
                ·
                  refine ⟨1376751633671071930269331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1835668844894762573692441 1376751633671071930269331)
                  ·
                    refine ⟨2065127450506607895403997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1376751633671071930269331 2065127450506607895403997)
                    ·
                      refine ⟨774422793939977960776499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2065127450506607895403997 774422793939977960776499)
                      ·
                        rfl

theorem cell23_1508183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_1508183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508183 prefixEnd_1508183 := by exact prefixLift 1508183
  have htrace : WordTrace (prefixWord ++ tailWord_1508183) baseStart_1508183 baseEnd_1508183 := by
    simpa [prefixWord, tailWord_1508183, baseEnd_1508183] using wordTrace_append hprefix tailTrace_1508183
  have hstable : (prefixWord ++ tailWord_1508183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508183).length < 2 ^ (prefixWord ++ tailWord_1508183).sum := by decide
  have hdescent : baseEnd_1508183 < baseStart_1508183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508249 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 2, 5, 2]
def baseStart_1508249 : Nat := 118140960795 + 1508249 * 2 ^ 59
def prefixEnd_1508249 : Nat := 4983230072969 + 3 ^ 40 * 1508249 * 2
def baseEnd_1508249 : Nat := 774456683663174702551195

theorem tailTrace_1508249 : CollatzResearch.WordTrace tailWord_1508249 prefixEnd_1508249 774456683663174702551195 := by
  unfold tailWord_1508249
  simp only [CollatzResearch.WordTrace]
  refine ⟨55010360312878936266647801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36673573541919290844431867 55010360312878936266647801)
  ·
    refine ⟨41257770234659202199985851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55010360312878936266647801 41257770234659202199985851)
    ·
      refine ⟨61886655351988803299978777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41257770234659202199985851 61886655351988803299978777)
      ·
        refine ⟨46414991513991602474984083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61886655351988803299978777 46414991513991602474984083)
        ·
          refine ⟨69622487270987403712476125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46414991513991602474984083 69622487270987403712476125)
          ·
            refine ⟨26108432726620276392178547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69622487270987403712476125 26108432726620276392178547)
            ·
              refine ⟨39162649089930414588267821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26108432726620276392178547 39162649089930414588267821)
              ·
                refine ⟨14685993408723905470600433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39162649089930414588267821 14685993408723905470600433)
                ·
                  refine ⟨11014495056542929102950325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14685993408723905470600433 11014495056542929102950325)
                  ·
                    refine ⟨1032608911550899603401593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11014495056542929102950325 1032608911550899603401593)
                    ·
                      refine ⟨774456683663174702551195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1032608911550899603401593 774456683663174702551195)
                      ·
                        rfl

theorem cell23_1508249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 5, 2].length) (baseStart_1508249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508249 prefixEnd_1508249 := by exact prefixLift 1508249
  have htrace : WordTrace (prefixWord ++ tailWord_1508249) baseStart_1508249 baseEnd_1508249 := by
    simpa [prefixWord, tailWord_1508249, baseEnd_1508249] using wordTrace_append hprefix tailTrace_1508249
  have hstable : (prefixWord ++ tailWord_1508249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508249).length < 2 ^ (prefixWord ++ tailWord_1508249).sum := by decide
  have hdescent : baseEnd_1508249 < baseStart_1508249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508257 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1508257 : Nat := 118140960795 + 1508257 * 2 ^ 59
def prefixEnd_1508257 : Nat := 4983230072969 + 3 ^ 40 * 1508257 * 2
def baseEnd_1508257 : Nat := 774460791508410671251159

theorem tailTrace_1508257 : CollatzResearch.WordTrace tailWord_1508257 prefixEnd_1508257 774460791508410671251159 := by
  unfold tailWord_1508257
  simp only [CollatzResearch.WordTrace]
  refine ⟨55010652096849953632939025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36673768064566635755292683 55010652096849953632939025)
  ·
    refine ⟨41257989072637465224704269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55010652096849953632939025 41257989072637465224704269)
    ·
      refine ⟨15471745902239049459264101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41257989072637465224704269 15471745902239049459264101)
      ·
        refine ⟨2900952356669821773612019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15471745902239049459264101 2900952356669821773612019)
        ·
          refine ⟨4351428535004732660418029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2900952356669821773612019 4351428535004732660418029)
          ·
            refine ⟨1631785700626774747656761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4351428535004732660418029 1631785700626774747656761)
            ·
              refine ⟨1223839275470081060742571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631785700626774747656761 1223839275470081060742571)
              ·
                refine ⟨1835758913205121591113857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223839275470081060742571 1835758913205121591113857)
                ·
                  refine ⟨1376819184903841193335393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1835758913205121591113857 1376819184903841193335393)
                  ·
                    refine ⟨1032614388677880895001545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1376819184903841193335393 1032614388677880895001545)
                    ·
                      refine ⟨774460791508410671251159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1032614388677880895001545 774460791508410671251159)
                      ·
                        rfl

theorem cell23_1508257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1508257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508257 prefixEnd_1508257 := by exact prefixLift 1508257
  have htrace : WordTrace (prefixWord ++ tailWord_1508257) baseStart_1508257 baseEnd_1508257 := by
    simpa [prefixWord, tailWord_1508257, baseEnd_1508257] using wordTrace_append hprefix tailTrace_1508257
  have hstable : (prefixWord ++ tailWord_1508257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508257).length < 2 ^ (prefixWord ++ tailWord_1508257).sum := by decide
  have hdescent : baseEnd_1508257 < baseStart_1508257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508279 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_1508279 : Nat := 118140960795 + 1508279 * 2 ^ 59
def prefixEnd_1508279 : Nat := 4983230072969 + 3 ^ 40 * 1508279 * 2
def baseEnd_1508279 : Nat := 774472088082809585176057

theorem tailTrace_1508279 : CollatzResearch.WordTrace tailWord_1508279 prefixEnd_1508279 774472088082809585176057 := by
  unfold tailWord_1508279
  simp only [CollatzResearch.WordTrace]
  refine ⟨55011454502770251390239891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36674303001846834260159927 55011454502770251390239891)
  ·
    refine ⟨82517181754155377085359837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55011454502770251390239891 82517181754155377085359837)
    ·
      refine ⟨30943943157808266407009939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82517181754155377085359837 30943943157808266407009939)
      ·
        refine ⟨46415914736712399610514909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30943943157808266407009939 46415914736712399610514909)
        ·
          refine ⟨17405968026267149853943091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46415914736712399610514909 17405968026267149853943091)
          ·
            refine ⟨26108952039400724780914637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17405968026267149853943091 26108952039400724780914637)
            ·
              refine ⟨9790857014775271792842989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26108952039400724780914637 9790857014775271792842989)
              ·
                refine ⟨3671571380540726922316121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9790857014775271792842989 3671571380540726922316121)
                ·
                  refine ⟨2753678535405545191737091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3671571380540726922316121 2753678535405545191737091)
                  ·
                    refine ⟨4130517803108317787605637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2753678535405545191737091 4130517803108317787605637)
                    ·
                      refine ⟨774472088082809585176057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4130517803108317787605637 774472088082809585176057)
                      ·
                        rfl

theorem cell23_1508279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_1508279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508279 prefixEnd_1508279 := by exact prefixLift 1508279
  have htrace : WordTrace (prefixWord ++ tailWord_1508279) baseStart_1508279 baseEnd_1508279 := by
    simpa [prefixWord, tailWord_1508279, baseEnd_1508279] using wordTrace_append hprefix tailTrace_1508279
  have hstable : (prefixWord ++ tailWord_1508279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508279).length < 2 ^ (prefixWord ++ tailWord_1508279).sum := by decide
  have hdescent : baseEnd_1508279 < baseStart_1508279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508363 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 3, 1, 3]
def baseStart_1508363 : Nat := 118140960795 + 1508363 * 2 ^ 59
def prefixEnd_1508363 : Nat := 4983230072969 + 3 ^ 40 * 1508363 * 2
def baseEnd_1508363 : Nat := 774515220457787256525671

theorem tailTrace_1508363 : CollatzResearch.WordTrace tailWord_1508363 prefixEnd_1508363 774515220457787256525671 := by
  unfold tailWord_1508363
  simp only [CollatzResearch.WordTrace]
  refine ⟨55014518234465933736297743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36676345489643955824198495 55014518234465933736297743)
  ·
    refine ⟨82521777351698900604446615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55014518234465933736297743 82521777351698900604446615)
    ·
      refine ⟨123782666027548350906669923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82521777351698900604446615 123782666027548350906669923)
      ·
        refine ⟨185673999041322526360004885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123782666027548350906669923 185673999041322526360004885)
        ·
          refine ⟨8703468705061993423125229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185673999041322526360004885 8703468705061993423125229)
          ·
            refine ⟨3263800764398247533671961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8703468705061993423125229 3263800764398247533671961)
            ·
              refine ⟨2447850573298685650253971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3263800764398247533671961 2447850573298685650253971)
              ·
                refine ⟨3671775859948028475380957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447850573298685650253971 3671775859948028475380957)
                ·
                  refine ⟨1376915947480510678267859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3671775859948028475380957 1376915947480510678267859)
                  ·
                    refine ⟨2065373921220766017401789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1376915947480510678267859 2065373921220766017401789)
                    ·
                      refine ⟨774515220457787256525671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2065373921220766017401789 774515220457787256525671)
                      ·
                        rfl

theorem cell23_1508363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 1, 3].length) (baseStart_1508363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508363 prefixEnd_1508363 := by exact prefixLift 1508363
  have htrace : WordTrace (prefixWord ++ tailWord_1508363) baseStart_1508363 baseEnd_1508363 := by
    simpa [prefixWord, tailWord_1508363, baseEnd_1508363] using wordTrace_append hprefix tailTrace_1508363
  have hstable : (prefixWord ++ tailWord_1508363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508363).length < 2 ^ (prefixWord ++ tailWord_1508363).sum := by decide
  have hdescent : baseEnd_1508363 < baseStart_1508363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508369 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_1508369 : Nat := 118140960795 + 1508369 * 2 ^ 59
def prefixEnd_1508369 : Nat := 4983230072969 + 3 ^ 40 * 1508369 * 2
def baseEnd_1508369 : Nat := 774518301341714233050643

theorem tailTrace_1508369 : CollatzResearch.WordTrace tailWord_1508369 prefixEnd_1508369 774518301341714233050643 := by
  unfold tailWord_1508369
  simp only [CollatzResearch.WordTrace]
  refine ⟨55014737072444196761016161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36676491381629464507344107 55014737072444196761016161)
  ·
    refine ⟨41261052804333147570762121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55014737072444196761016161 41261052804333147570762121)
    ·
      refine ⟨30945789603249860678071591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41261052804333147570762121 30945789603249860678071591)
      ·
        refine ⟨46418684404874791017107387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30945789603249860678071591 46418684404874791017107387)
        ·
          refine ⟨69628026607312186525661081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46418684404874791017107387 69628026607312186525661081)
          ·
            refine ⟨52221019955484139894245811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69628026607312186525661081 52221019955484139894245811)
            ·
              refine ⟨78331529933226209841368717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52221019955484139894245811 78331529933226209841368717)
              ·
                refine ⟨29374323724959828690513269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78331529933226209841368717 29374323724959828690513269)
                ·
                  refine ⟨2753842849214983939735619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29374323724959828690513269 2753842849214983939735619)
                  ·
                    refine ⟨4130764273822475909603429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2753842849214983939735619 4130764273822475909603429)
                    ·
                      refine ⟨774518301341714233050643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4130764273822475909603429 774518301341714233050643)
                      ·
                        rfl

theorem cell23_1508369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_1508369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508369 prefixEnd_1508369 := by exact prefixLift 1508369
  have htrace : WordTrace (prefixWord ++ tailWord_1508369) baseStart_1508369 baseEnd_1508369 := by
    simpa [prefixWord, tailWord_1508369, baseEnd_1508369] using wordTrace_append hprefix tailTrace_1508369
  have hstable : (prefixWord ++ tailWord_1508369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508369).length < 2 ^ (prefixWord ++ tailWord_1508369).sum := by decide
  have hdescent : baseEnd_1508369 < baseStart_1508369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508389 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_1508389 : Nat := 118140960795 + 1508389 * 2 ^ 59
def prefixEnd_1508389 : Nat := 4983230072969 + 3 ^ 40 * 1508389 * 2
def baseEnd_1508389 : Nat := 774528570954804154800551

theorem tailTrace_1508389 : CollatzResearch.WordTrace tailWord_1508389 prefixEnd_1508389 774528570954804154800551 := by
  unfold tailWord_1508389
  simp only [CollatzResearch.WordTrace]
  refine ⟨55015466532371740176744221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36676977688247826784496147 55015466532371740176744221)
  ·
    refine ⟨20630799949639402566279083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55015466532371740176744221 20630799949639402566279083)
    ·
      refine ⟨30946199924459103849418625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20630799949639402566279083 30946199924459103849418625)
      ·
        refine ⟨23209649943344327887063969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30946199924459103849418625 23209649943344327887063969)
        ·
          refine ⟨17407237457508245915297977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23209649943344327887063969 17407237457508245915297977)
          ·
            refine ⟨13055428093131184436473483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17407237457508245915297977 13055428093131184436473483)
            ·
              refine ⟨19583142139696776654710225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13055428093131184436473483 19583142139696776654710225)
              ·
                refine ⟨14687356604772582491032669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19583142139696776654710225 14687356604772582491032669)
                ·
                  refine ⟨5507758726789718434137251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14687356604772582491032669 5507758726789718434137251)
                  ·
                    refine ⟨8261638090184577651205877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5507758726789718434137251 8261638090184577651205877)
                    ·
                      refine ⟨774528570954804154800551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8261638090184577651205877 774528570954804154800551)
                      ·
                        rfl

theorem cell23_1508389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_1508389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508389 prefixEnd_1508389 := by exact prefixLift 1508389
  have htrace : WordTrace (prefixWord ++ tailWord_1508389) baseStart_1508389 baseEnd_1508389 := by
    simpa [prefixWord, tailWord_1508389, baseEnd_1508389] using wordTrace_append hprefix tailTrace_1508389
  have hstable : (prefixWord ++ tailWord_1508389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508389).length < 2 ^ (prefixWord ++ tailWord_1508389).sum := by decide
  have hdescent : baseEnd_1508389 < baseStart_1508389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508409 : List Nat := [1, 2, 1, 5, 2, 1, 11]
def baseStart_1508409 : Nat := 118140960795 + 1508409 * 2 ^ 59
def prefixEnd_1508409 : Nat := 4983230072969 + 3 ^ 40 * 1508409 * 2
def baseEnd_1508409 : Nat := 9562207908245605883339

theorem tailTrace_1508409 : CollatzResearch.WordTrace tailWord_1508409 prefixEnd_1508409 9562207908245605883339 := by
  unfold tailWord_1508409
  simp only [CollatzResearch.WordTrace]
  refine ⟨55016195992299283592472281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36677463994866189061648187 55016195992299283592472281)
  ·
    refine ⟨41262146994224462694354211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55016195992299283592472281 41262146994224462694354211)
    ·
      refine ⟨61893220491336694041531317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41262146994224462694354211 61893220491336694041531317)
      ·
        refine ⟨5802489421062815066393561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61893220491336694041531317 5802489421062815066393561)
        ·
          refine ⟨4351867065797111299795171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5802489421062815066393561 4351867065797111299795171)
          ·
            refine ⟨6527800598695666949692757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351867065797111299795171 6527800598695666949692757)
            ·
              refine ⟨9562207908245605883339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6527800598695666949692757 9562207908245605883339)
              ·
                rfl

theorem cell23_1508409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 11].length) (baseStart_1508409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508409 prefixEnd_1508409 := by exact prefixLift 1508409
  have htrace : WordTrace (prefixWord ++ tailWord_1508409) baseStart_1508409 baseEnd_1508409 := by
    simpa [prefixWord, tailWord_1508409, baseEnd_1508409] using wordTrace_append hprefix tailTrace_1508409
  have hstable : (prefixWord ++ tailWord_1508409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508409).length < 2 ^ (prefixWord ++ tailWord_1508409).sum := by decide
  have hdescent : baseEnd_1508409 < baseStart_1508409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508414 : List Nat := [4, 2, 1, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_1508414 : Nat := 118140960795 + 1508414 * 2 ^ 59
def prefixEnd_1508414 : Nat := 4983230072969 + 3 ^ 40 * 1508414 * 2
def baseEnd_1508414 : Nat := 774541407971166556987937

theorem tailTrace_1508414 : CollatzResearch.WordTrace tailWord_1508414 prefixEnd_1508414 774541407971166556987937 := by
  unfold tailWord_1508414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6877047294660146180800537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36677585571520779630936197 6877047294660146180800537)
  ·
    refine ⟨5157785470995109635600403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6877047294660146180800537 5157785470995109635600403)
    ·
      refine ⟨7736678206492664453400605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5157785470995109635600403 7736678206492664453400605)
      ·
        refine ⟨2901254327434749170025227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7736678206492664453400605 2901254327434749170025227)
        ·
          refine ⟨4351881491152123755037841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901254327434749170025227 4351881491152123755037841)
          ·
            refine ⟨3263911118364092816278381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4351881491152123755037841 3263911118364092816278381)
            ·
              refine ⟨1223966669386534806104393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3263911118364092816278381 1223966669386534806104393)
              ·
                refine ⟨917975002039901104578295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223966669386534806104393 917975002039901104578295)
                ·
                  refine ⟨1376962503059851656867443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 917975002039901104578295 1376962503059851656867443)
                  ·
                    refine ⟨2065443754589777485301165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1376962503059851656867443 2065443754589777485301165)
                    ·
                      refine ⟨774541407971166556987937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2065443754589777485301165 774541407971166556987937)
                      ·
                        rfl

theorem cell23_1508414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_1508414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508414 prefixEnd_1508414 := by exact prefixLift 1508414
  have htrace : WordTrace (prefixWord ++ tailWord_1508414) baseStart_1508414 baseEnd_1508414 := by
    simpa [prefixWord, tailWord_1508414, baseEnd_1508414] using wordTrace_append hprefix tailTrace_1508414
  have hstable : (prefixWord ++ tailWord_1508414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508414).length < 2 ^ (prefixWord ++ tailWord_1508414).sum := by decide
  have hdescent : baseEnd_1508414 < baseStart_1508414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508449 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_1508449 : Nat := 118140960795 + 1508449 * 2 ^ 59
def prefixEnd_1508449 : Nat := 4983230072969 + 3 ^ 40 * 1508449 * 2
def baseEnd_1508449 : Nat := 774559379794073920050275

theorem tailTrace_1508449 : CollatzResearch.WordTrace tailWord_1508449 prefixEnd_1508449 774559379794073920050275 := by
  unfold tailWord_1508449
  simp only [CollatzResearch.WordTrace]
  refine ⟨55017654912154370423928401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36678436608102913615952267 55017654912154370423928401)
  ·
    refine ⟨41263241184115777817946301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55017654912154370423928401 41263241184115777817946301)
    ·
      refine ⟨15473715444043416681729863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41263241184115777817946301 15473715444043416681729863)
      ·
        refine ⟨23210573166065125022594795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15473715444043416681729863 23210573166065125022594795)
        ·
          refine ⟨34815859749097687533892193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23210573166065125022594795 34815859749097687533892193)
          ·
            refine ⟨26111894811823265650419145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34815859749097687533892193 26111894811823265650419145)
            ·
              refine ⟨19583921108867449237814359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26111894811823265650419145 19583921108867449237814359)
              ·
                refine ⟨29375881663301173856721539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19583921108867449237814359 29375881663301173856721539)
                ·
                  refine ⟨44063822494951760785082309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29375881663301173856721539 44063822494951760785082309)
                  ·
                    refine ⟨8261966717803455147202933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44063822494951760785082309 8261966717803455147202933)
                    ·
                      refine ⟨774559379794073920050275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8261966717803455147202933 774559379794073920050275)
                      ·
                        rfl

theorem cell23_1508449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_1508449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508449 prefixEnd_1508449 := by exact prefixLift 1508449
  have htrace : WordTrace (prefixWord ++ tailWord_1508449) baseStart_1508449 baseEnd_1508449 := by
    simpa [prefixWord, tailWord_1508449, baseEnd_1508449] using wordTrace_append hprefix tailTrace_1508449
  have hstable : (prefixWord ++ tailWord_1508449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508449).length < 2 ^ (prefixWord ++ tailWord_1508449).sum := by decide
  have hdescent : baseEnd_1508449 < baseStart_1508449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508459 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 4]
def baseStart_1508459 : Nat := 118140960795 + 1508459 * 2 ^ 59
def prefixEnd_1508459 : Nat := 4983230072969 + 3 ^ 40 * 1508459 * 2
def baseEnd_1508459 : Nat := 774564514600618880925229

theorem tailTrace_1508459 : CollatzResearch.WordTrace tailWord_1508459 prefixEnd_1508459 774564514600618880925229 := by
  unfold tailWord_1508459
  simp only [CollatzResearch.WordTrace]
  refine ⟨55018019642118142131792431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36678679761412094754528287 55018019642118142131792431)
  ·
    refine ⟨82527029463177213197688647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55018019642118142131792431 82527029463177213197688647)
    ·
      refine ⟨123790544194765819796532971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82527029463177213197688647 123790544194765819796532971)
      ·
        refine ⟨185685816292148729694799457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123790544194765819796532971 185685816292148729694799457)
        ·
          refine ⟨139264362219111547271099593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185685816292148729694799457 139264362219111547271099593)
          ·
            refine ⟨104448271664333660453324695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139264362219111547271099593 104448271664333660453324695)
            ·
              refine ⟨156672407496500490679987043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104448271664333660453324695 156672407496500490679987043)
              ·
                refine ⟨235008611244750736019980565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156672407496500490679987043 235008611244750736019980565)
                ·
                  refine ⟨11016028652097690750936589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 235008611244750736019980565 11016028652097690750936589)
                  ·
                    refine ⟨4131010744536634031601221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11016028652097690750936589 4131010744536634031601221)
                    ·
                      refine ⟨774564514600618880925229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4131010744536634031601221 774564514600618880925229)
                      ·
                        rfl

theorem cell23_1508459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 4].length) (baseStart_1508459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508459 prefixEnd_1508459 := by exact prefixLift 1508459
  have htrace : WordTrace (prefixWord ++ tailWord_1508459) baseStart_1508459 baseEnd_1508459 := by
    simpa [prefixWord, tailWord_1508459, baseEnd_1508459] using wordTrace_append hprefix tailTrace_1508459
  have hstable : (prefixWord ++ tailWord_1508459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508459).length < 2 ^ (prefixWord ++ tailWord_1508459).sum := by decide
  have hdescent : baseEnd_1508459 < baseStart_1508459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508499 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 9]
def baseStart_1508499 : Nat := 118140960795 + 1508499 * 2 ^ 59
def prefixEnd_1508499 : Nat := 4983230072969 + 3 ^ 40 * 1508499 * 2
def baseEnd_1508499 : Nat := 86065005980755413825005

theorem tailTrace_1508499 : CollatzResearch.WordTrace tailWord_1508499 prefixEnd_1508499 86065005980755413825005 := by
  unfold tailWord_1508499
  simp only [CollatzResearch.WordTrace]
  refine ⟨55019478561973228963248551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36679652374648819308832367 55019478561973228963248551)
  ·
    refine ⟨82529217842959843444872827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55019478561973228963248551 82529217842959843444872827)
    ·
      refine ⟨123793826764439765167309241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82529217842959843444872827 123793826764439765167309241)
      ·
        refine ⟨92845370073329823875481931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123793826764439765167309241 92845370073329823875481931)
        ·
          refine ⟨139268055109994735813222897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92845370073329823875481931 139268055109994735813222897)
          ·
            refine ⟨104451041332496051859917173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139268055109994735813222897 104451041332496051859917173)
            ·
              refine ⟨9792285124921504861867235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104451041332496051859917173 9792285124921504861867235)
              ·
                refine ⟨14688427687382257292800853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9792285124921504861867235 14688427687382257292800853)
                ·
                  refine ⟨86065005980755413825005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14688427687382257292800853 86065005980755413825005)
                  ·
                    rfl

theorem cell23_1508499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 9].length) (baseStart_1508499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508499 prefixEnd_1508499 := by exact prefixLift 1508499
  have htrace : WordTrace (prefixWord ++ tailWord_1508499) baseStart_1508499 baseEnd_1508499 := by
    simpa [prefixWord, tailWord_1508499, baseEnd_1508499] using wordTrace_append hprefix tailTrace_1508499
  have hstable : (prefixWord ++ tailWord_1508499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508499).length < 2 ^ (prefixWord ++ tailWord_1508499).sum := by decide
  have hdescent : baseEnd_1508499 < baseStart_1508499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508544 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 2, 2, 2]
def baseStart_1508544 : Nat := 118140960795 + 1508544 * 2 ^ 59
def prefixEnd_1508544 : Nat := 4983230072969 + 3 ^ 40 * 1508544 * 2
def baseEnd_1508544 : Nat := 774608160456251048362339

theorem tailTrace_1508544 : CollatzResearch.WordTrace tailWord_1508544 prefixEnd_1508544 774608160456251048362339 := by
  unfold tailWord_1508544
  simp only [CollatzResearch.WordTrace]
  refine ⟨27510559923405100824318343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36680746564540134432424457 27510559923405100824318343)
  ·
    refine ⟨41265839885107651236477515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27510559923405100824318343 41265839885107651236477515)
    ·
      refine ⟨61898759827661476854716273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41265839885107651236477515 61898759827661476854716273)
      ·
        refine ⟨46424069870746107641037205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61898759827661476854716273 46424069870746107641037205)
        ·
          refine ⟨2176128275191223795673619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46424069870746107641037205 2176128275191223795673619)
          ·
            refine ⟨3264192412786835693510429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176128275191223795673619 3264192412786835693510429)
            ·
              refine ⟨1224072154795063385066411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3264192412786835693510429 1224072154795063385066411)
              ·
                refine ⟨1836108232192595077599617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224072154795063385066411 1836108232192595077599617)
                ·
                  refine ⟨1377081174144446308199713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1836108232192595077599617 1377081174144446308199713)
                  ·
                    refine ⟨1032810880608334731149785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1377081174144446308199713 1032810880608334731149785)
                    ·
                      refine ⟨774608160456251048362339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1032810880608334731149785 774608160456251048362339)
                      ·
                        rfl

theorem cell23_1508544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 2, 2, 2].length) (baseStart_1508544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508544 prefixEnd_1508544 := by exact prefixLift 1508544
  have htrace : WordTrace (prefixWord ++ tailWord_1508544) baseStart_1508544 baseEnd_1508544 := by
    simpa [prefixWord, tailWord_1508544, baseEnd_1508544] using wordTrace_append hprefix tailTrace_1508544
  have hstable : (prefixWord ++ tailWord_1508544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508544).length < 2 ^ (prefixWord ++ tailWord_1508544).sum := by decide
  have hdescent : baseEnd_1508544 < baseStart_1508544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508620 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 2, 2, 3]
def baseStart_1508620 : Nat := 118140960795 + 1508620 * 2 ^ 59
def prefixEnd_1508620 : Nat := 4983230072969 + 3 ^ 40 * 1508620 * 2
def baseEnd_1508620 : Nat := 774647184985992751011989

theorem tailTrace_1508620 : CollatzResearch.WordTrace tailWord_1508620 prefixEnd_1508620 774647184985992751011989 := by
  unfold tailWord_1508620
  simp only [CollatzResearch.WordTrace]
  refine ⟨27511945897267433314201657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36682594529689911085602209 27511945897267433314201657)
  ·
    refine ⟨20633959422950574985651243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27511945897267433314201657 20633959422950574985651243)
    ·
      refine ⟨30950939134425862478476865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20633959422950574985651243 30950939134425862478476865)
      ·
        refine ⟨23213204350819396858857649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30950939134425862478476865 23213204350819396858857649)
        ·
          refine ⟨17409903263114547644143237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23213204350819396858857649 17409903263114547644143237)
          ·
            refine ⟨3264356861833977683276857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17409903263114547644143237 3264356861833977683276857)
            ·
              refine ⟨2448267646375483262457643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3264356861833977683276857 2448267646375483262457643)
              ·
                refine ⟨3672401469563224893686465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2448267646375483262457643 3672401469563224893686465)
                ·
                  refine ⟨2754301102172418670264849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3672401469563224893686465 2754301102172418670264849)
                  ·
                    refine ⟨2065725826629314002698637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2754301102172418670264849 2065725826629314002698637)
                    ·
                      refine ⟨774647184985992751011989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2065725826629314002698637 774647184985992751011989)
                      ·
                        rfl

theorem cell23_1508620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_1508620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508620 prefixEnd_1508620 := by exact prefixLift 1508620
  have htrace : WordTrace (prefixWord ++ tailWord_1508620) baseStart_1508620 baseEnd_1508620 := by
    simpa [prefixWord, tailWord_1508620, baseEnd_1508620] using wordTrace_append hprefix tailTrace_1508620
  have hstable : (prefixWord ++ tailWord_1508620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508620).length < 2 ^ (prefixWord ++ tailWord_1508620).sum := by decide
  have hdescent : baseEnd_1508620 < baseStart_1508620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508640 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 6]
def baseStart_1508640 : Nat := 118140960795 + 1508640 * 2 ^ 59
def prefixEnd_1508640 : Nat := 4983230072969 + 3 ^ 40 * 1508640 * 2
def baseEnd_1508640 : Nat := 86073050511009185862433

theorem tailTrace_1508640 : CollatzResearch.WordTrace tailWord_1508640 prefixEnd_1508640 86073050511009185862433 := by
  unfold tailWord_1508640
  simp only [CollatzResearch.WordTrace]
  refine ⟨27512310627231205022065687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36683080836308273362754249 27512310627231205022065687)
  ·
    refine ⟨41268465940846807533098531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27512310627231205022065687 41268465940846807533098531)
    ·
      refine ⟨61902698911270211299647797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41268465940846807533098531 61902698911270211299647797)
      ·
        refine ⟨5803378022931582309341981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61902698911270211299647797 5803378022931582309341981)
        ·
          refine ⟨2176266758599343366003243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5803378022931582309341981 2176266758599343366003243)
          ·
            refine ⟨3264400137899015049004865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176266758599343366003243 3264400137899015049004865)
            ·
              refine ⟨2448300103424261286753649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3264400137899015049004865 2448300103424261286753649)
              ·
                refine ⟨1836225077568195965065237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2448300103424261286753649 1836225077568195965065237)
                ·
                  refine ⟨86073050511009185862433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1836225077568195965065237 86073050511009185862433)
                  ·
                    rfl

theorem cell23_1508640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 6].length) (baseStart_1508640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508640 prefixEnd_1508640 := by exact prefixLift 1508640
  have htrace : WordTrace (prefixWord ++ tailWord_1508640) baseStart_1508640 baseEnd_1508640 := by
    simpa [prefixWord, tailWord_1508640, baseEnd_1508640] using wordTrace_append hprefix tailTrace_1508640
  have hstable : (prefixWord ++ tailWord_1508640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508640).length < 2 ^ (prefixWord ++ tailWord_1508640).sum := by decide
  have hdescent : baseEnd_1508640 < baseStart_1508640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508670 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_1508670 : Nat := 118140960795 + 1508670 * 2 ^ 59
def prefixEnd_1508670 : Nat := 4983230072969 + 3 ^ 40 * 1508670 * 2
def baseEnd_1508670 : Nat := 258224286339572518462253

theorem tailTrace_1508670 : CollatzResearch.WordTrace tailWord_1508670 prefixEnd_1508670 258224286339572518462253 := by
  unfold tailWord_1508670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6878214430544215645965433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36683810296235816778482309 6878214430544215645965433)
  ·
    refine ⟨5158660822908161734474075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6878214430544215645965433 5158660822908161734474075)
    ·
      refine ⟨7737991234362242601711113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5158660822908161734474075 7737991234362242601711113)
      ·
        refine ⟨5803493425771681951283335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7737991234362242601711113 5803493425771681951283335)
        ·
          refine ⟨8705240138657522926925003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5803493425771681951283335 8705240138657522926925003)
          ·
            refine ⟨13057860207986284390387505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8705240138657522926925003 13057860207986284390387505)
            ·
              refine ⟨9793395155989713292790629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13057860207986284390387505 9793395155989713292790629)
              ·
                refine ⟨1836261591748071242398243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9793395155989713292790629 1836261591748071242398243)
                ·
                  refine ⟨2754392387622106863597365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836261591748071242398243 2754392387622106863597365)
                  ·
                    refine ⟨258224286339572518462253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2754392387622106863597365 258224286339572518462253)
                    ·
                      rfl

theorem cell23_1508670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_1508670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508670 prefixEnd_1508670 := by exact prefixLift 1508670
  have htrace : WordTrace (prefixWord ++ tailWord_1508670) baseStart_1508670 baseEnd_1508670 := by
    simpa [prefixWord, tailWord_1508670, baseEnd_1508670] using wordTrace_append hprefix tailTrace_1508670
  have hstable : (prefixWord ++ tailWord_1508670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508670).length < 2 ^ (prefixWord ++ tailWord_1508670).sum := by decide
  have hdescent : baseEnd_1508670 < baseStart_1508670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508678 : List Nat := [6, 1, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_1508678 : Nat := 118140960795 + 1508678 * 2 ^ 59
def prefixEnd_1508678 : Nat := 4983230072969 + 3 ^ 40 * 1508678 * 2
def baseEnd_1508678 : Nat := 258225655621317841362241

theorem tailTrace_1508678 : CollatzResearch.WordTrace tailWord_1508678 prefixEnd_1508678 258225655621317841362241 := by
  unfold tailWord_1508678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719562725885148204187959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36684004818883161689343125 1719562725885148204187959)
  ·
    refine ⟨2579344088827722306281939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1719562725885148204187959 2579344088827722306281939)
    ·
      refine ⟨3869016133241583459422909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2579344088827722306281939 3869016133241583459422909)
      ·
        refine ⟨1450881049965593797283591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3869016133241583459422909 1450881049965593797283591)
        ·
          refine ⟨2176321574948390695925387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450881049965593797283591 2176321574948390695925387)
          ·
            refine ⟨3264482362422586043888081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176321574948390695925387 3264482362422586043888081)
            ·
              refine ⟨2448361771816939532916061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3264482362422586043888081 2448361771816939532916061)
              ·
                refine ⟨918135664431352324843523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2448361771816939532916061 918135664431352324843523)
                ·
                  refine ⟨1377203496647028487265285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918135664431352324843523 1377203496647028487265285)
                  ·
                    refine ⟨258225655621317841362241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1377203496647028487265285 258225655621317841362241)
                    ·
                      rfl

theorem cell23_1508678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_1508678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508678 prefixEnd_1508678 := by exact prefixLift 1508678
  have htrace : WordTrace (prefixWord ++ tailWord_1508678) baseStart_1508678 baseEnd_1508678 := by
    simpa [prefixWord, tailWord_1508678, baseEnd_1508678] using wordTrace_append hprefix tailTrace_1508678
  have hstable : (prefixWord ++ tailWord_1508678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508678).length < 2 ^ (prefixWord ++ tailWord_1508678).sum := by decide
  have hdescent : baseEnd_1508678 < baseStart_1508678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508684 : List Nat := [2, 2, 1, 3, 2, 3, 2, 3, 1, 1, 3]
def baseStart_1508684 : Nat := 118140960795 + 1508684 * 2 ^ 59
def prefixEnd_1508684 : Nat := 4983230072969 + 3 ^ 40 * 1508684 * 2
def baseEnd_1508684 : Nat := 774680047747880500611695

theorem tailTrace_1508684 : CollatzResearch.WordTrace tailWord_1508684 prefixEnd_1508684 774680047747880500611695 := by
  unfold tailWord_1508684
  simp only [CollatzResearch.WordTrace]
  refine ⟨27513113033151502779366553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36684150710868670372488737 27513113033151502779366553)
  ·
    refine ⟨20634834774863627084524915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27513113033151502779366553 20634834774863627084524915)
    ·
      refine ⟨30952252162295440626787373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20634834774863627084524915 30952252162295440626787373)
      ·
        refine ⟨11607094560860790235045265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30952252162295440626787373 11607094560860790235045265)
        ·
          refine ⟨8705320920645592676283949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11607094560860790235045265 8705320920645592676283949)
          ·
            refine ⟨3264495345242097253606481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8705320920645592676283949 3264495345242097253606481)
            ·
              refine ⟨2448371508931572940204861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3264495345242097253606481 2448371508931572940204861)
              ·
                refine ⟨918139315849339852576823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2448371508931572940204861 918139315849339852576823)
                ·
                  refine ⟨1377208973774009778865235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918139315849339852576823 1377208973774009778865235)
                  ·
                    refine ⟨2065813460661014668297853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1377208973774009778865235 2065813460661014668297853)
                    ·
                      refine ⟨774680047747880500611695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2065813460661014668297853 774680047747880500611695)
                      ·
                        rfl

theorem cell23_1508684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_1508684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508684 prefixEnd_1508684 := by exact prefixLift 1508684
  have htrace : WordTrace (prefixWord ++ tailWord_1508684) baseStart_1508684 baseEnd_1508684 := by
    simpa [prefixWord, tailWord_1508684, baseEnd_1508684] using wordTrace_append hprefix tailTrace_1508684
  have hstable : (prefixWord ++ tailWord_1508684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508684).length < 2 ^ (prefixWord ++ tailWord_1508684).sum := by decide
  have hdescent : baseEnd_1508684 < baseStart_1508684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508696 : List Nat := [2, 1, 2, 2, 1, 1, 14]
def baseStart_1508696 : Nat := 118140960795 + 1508696 * 2 ^ 59
def prefixEnd_1508696 : Nat := 4983230072969 + 3 ^ 40 * 1508696 * 2
def baseEnd_1508696 : Nat := 9564027277972030292119

theorem tailTrace_1508696 : CollatzResearch.WordTrace tailWord_1508696 prefixEnd_1508696 9564027277972030292119 := by
  unfold tailWord_1508696
  simp only [CollatzResearch.WordTrace]
  refine ⟨27513331871129765804084971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36684442494839687738779961 27513331871129765804084971)
  ·
    refine ⟨41269997806694648706127457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27513331871129765804084971 41269997806694648706127457)
    ·
      refine ⟨30952498355020986529595593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41269997806694648706127457 30952498355020986529595593)
      ·
        refine ⟨23214373766265739897196695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30952498355020986529595593 23214373766265739897196695)
        ·
          refine ⟨34821560649398609845795043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23214373766265739897196695 34821560649398609845795043)
          ·
            refine ⟨52232340974097914768692565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34821560649398609845795043 52232340974097914768692565)
            ·
              refine ⟨9564027277972030292119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 52232340974097914768692565 9564027277972030292119)
              ·
                rfl

theorem cell23_1508696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 14].length) (baseStart_1508696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508696 prefixEnd_1508696 := by exact prefixLift 1508696
  have htrace : WordTrace (prefixWord ++ tailWord_1508696) baseStart_1508696 baseEnd_1508696 := by
    simpa [prefixWord, tailWord_1508696, baseEnd_1508696] using wordTrace_append hprefix tailTrace_1508696
  have hstable : (prefixWord ++ tailWord_1508696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508696).length < 2 ^ (prefixWord ++ tailWord_1508696).sum := by decide
  have hdescent : baseEnd_1508696 < baseStart_1508696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508707 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 3, 2, 2]
def baseStart_1508707 : Nat := 118140960795 + 1508707 * 2 ^ 59
def prefixEnd_1508707 : Nat := 4983230072969 + 3 ^ 40 * 1508707 * 2
def baseEnd_1508707 : Nat := 774691857802933910624089

theorem tailTrace_1508707 : CollatzResearch.WordTrace tailWord_1508707 prefixEnd_1508707 774691857802933910624089 := by
  unfold tailWord_1508707
  simp only [CollatzResearch.WordTrace]
  refine ⟨55027064945219680486820375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36684709963479786991213583 55027064945219680486820375)
  ·
    refine ⟨82540597417829520730230563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55027064945219680486820375 82540597417829520730230563)
    ·
      refine ⟨123810896126744281095345845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82540597417829520730230563 123810896126744281095345845)
      ·
        refine ⟨11607271511882276352688673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123810896126744281095345845 11607271511882276352688673)
        ·
          refine ⟨8705453633911707264516505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11607271511882276352688673 8705453633911707264516505)
          ·
            refine ⟨6529090225433780448387379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8705453633911707264516505 6529090225433780448387379)
            ·
              refine ⟨9793635338150670672581069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6529090225433780448387379 9793635338150670672581069)
              ·
                refine ⟨3672613251806501502217901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9793635338150670672581069 3672613251806501502217901)
                ·
                  refine ⟨1377229969427438063331713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3672613251806501502217901 1377229969427438063331713)
                  ·
                    refine ⟨1032922477070578547498785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1377229969427438063331713 1032922477070578547498785)
                    ·
                      refine ⟨774691857802933910624089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1032922477070578547498785 774691857802933910624089)
                      ·
                        rfl

theorem cell23_1508707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_1508707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508707 prefixEnd_1508707 := by exact prefixLift 1508707
  have htrace : WordTrace (prefixWord ++ tailWord_1508707) baseStart_1508707 baseEnd_1508707 := by
    simpa [prefixWord, tailWord_1508707, baseEnd_1508707] using wordTrace_append hprefix tailTrace_1508707
  have hstable : (prefixWord ++ tailWord_1508707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508707).length < 2 ^ (prefixWord ++ tailWord_1508707).sum := by decide
  have hdescent : baseEnd_1508707 < baseStart_1508707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508797 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 1, 4, 2]
def baseStart_1508797 : Nat := 118140960795 + 1508797 * 2 ^ 59
def prefixEnd_1508797 : Nat := 4983230072969 + 3 ^ 40 * 1508797 * 2
def baseEnd_1508797 : Nat := 774738071061838558498675

theorem tailTrace_1508797 : CollatzResearch.WordTrace tailWord_1508797 prefixEnd_1508797 774738071061838558498675 := by
  unfold tailWord_1508797
  simp only [CollatzResearch.WordTrace]
  refine ⟨55030347514893625857596645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36686898343262417238397763 55030347514893625857596645)
  ·
    refine ⟨10318190159042554848299371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55030347514893625857596645 10318190159042554848299371)
    ·
      refine ⟨15477285238563832272449057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10318190159042554848299371 15477285238563832272449057)
      ·
        refine ⟨11607963928922874204336793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15477285238563832272449057 11607963928922874204336793)
        ·
          refine ⟨8705972946692155653252595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11607963928922874204336793 8705972946692155653252595)
          ·
            refine ⟨13058959420038233479878893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8705972946692155653252595 13058959420038233479878893)
            ·
              refine ⟨4897109782514337554954585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13058959420038233479878893 4897109782514337554954585)
              ·
                refine ⟨3672832336885753166215939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4897109782514337554954585 3672832336885753166215939)
                ·
                  refine ⟨5509248505328629749323909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672832336885753166215939 5509248505328629749323909)
                  ·
                    refine ⟨1032984094749118077998233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5509248505328629749323909 1032984094749118077998233)
                    ·
                      refine ⟨774738071061838558498675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1032984094749118077998233 774738071061838558498675)
                      ·
                        rfl

theorem cell23_1508797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_1508797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508797 prefixEnd_1508797 := by exact prefixLift 1508797
  have htrace : WordTrace (prefixWord ++ tailWord_1508797) baseStart_1508797 baseEnd_1508797 := by
    simpa [prefixWord, tailWord_1508797, baseEnd_1508797] using wordTrace_append hprefix tailTrace_1508797
  have hstable : (prefixWord ++ tailWord_1508797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508797).length < 2 ^ (prefixWord ++ tailWord_1508797).sum := by decide
  have hdescent : baseEnd_1508797 < baseStart_1508797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508814 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2]
def baseStart_1508814 : Nat := 118140960795 + 1508814 * 2 ^ 59
def prefixEnd_1508814 : Nat := 4983230072969 + 3 ^ 40 * 1508814 * 2
def baseEnd_1508814 : Nat := 774746800232964991986097

theorem tailTrace_1508814 : CollatzResearch.WordTrace tailWord_1508814 prefixEnd_1508814 774746800232964991986097 := by
  unfold tailWord_1508814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6878870944479004720120687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36687311703888025173976997 6878870944479004720120687)
  ·
    refine ⟨10318306416718507080181031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6878870944479004720120687 10318306416718507080181031)
    ·
      refine ⟨15477459625077760620271547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10318306416718507080181031 15477459625077760620271547)
      ·
        refine ⟨23216189437616640930407321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15477459625077760620271547 23216189437616640930407321)
        ·
          refine ⟨17412142078212480697805491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23216189437616640930407321 17412142078212480697805491)
          ·
            refine ⟨26118213117318721046708237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17412142078212480697805491 26118213117318721046708237)
            ·
              refine ⟨9794329918994520392515589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26118213117318721046708237 9794329918994520392515589)
              ·
                refine ⟨1836436859811472573596673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9794329918994520392515589 1836436859811472573596673)
                ·
                  refine ⟨1377327644858604430197505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1836436859811472573596673 1377327644858604430197505)
                  ·
                    refine ⟨1032995733643953322648129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1377327644858604430197505 1032995733643953322648129)
                    ·
                      refine ⟨774746800232964991986097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1032995733643953322648129 774746800232964991986097)
                      ·
                        rfl

theorem cell23_1508814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_1508814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508814 prefixEnd_1508814 := by exact prefixLift 1508814
  have htrace : WordTrace (prefixWord ++ tailWord_1508814) baseStart_1508814 baseEnd_1508814 := by
    simpa [prefixWord, tailWord_1508814, baseEnd_1508814] using wordTrace_append hprefix tailTrace_1508814
  have hstable : (prefixWord ++ tailWord_1508814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508814).length < 2 ^ (prefixWord ++ tailWord_1508814).sum := by decide
  have hdescent : baseEnd_1508814 < baseStart_1508814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508843 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 5]
def baseStart_1508843 : Nat := 118140960795 + 1508843 * 2 ^ 59
def prefixEnd_1508843 : Nat := 4983230072969 + 3 ^ 40 * 1508843 * 2
def baseEnd_1508843 : Nat := 774761691171945378523463

theorem tailTrace_1508843 : CollatzResearch.WordTrace tailWord_1508843 prefixEnd_1508843 774761691171945378523463 := by
  unfold tailWord_1508843
  simp only [CollatzResearch.WordTrace]
  refine ⟨55032025272726975713771183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36688016848484650475847455 55032025272726975713771183)
  ·
    refine ⟨82548037909090463570656775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55032025272726975713771183 82548037909090463570656775)
    ·
      refine ⟨123822056863635695355985163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82548037909090463570656775 123822056863635695355985163)
      ·
        refine ⟨185733085295453543033977745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123822056863635695355985163 185733085295453543033977745)
        ·
          refine ⟨139299813971590157275483309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185733085295453543033977745 139299813971590157275483309)
          ·
            refine ⟨52237430239346308978306241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139299813971590157275483309 52237430239346308978306241)
            ·
              refine ⟨39178072679509731733729681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52237430239346308978306241 39178072679509731733729681)
              ·
                refine ⟨29383554509632298800297261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39178072679509731733729681 29383554509632298800297261)
                ·
                  refine ⟨11018832941112112050111473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29383554509632298800297261 11018832941112112050111473)
                  ·
                    refine ⟨8264124705834084037583605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11018832941112112050111473 8264124705834084037583605)
                    ·
                      refine ⟨774761691171945378523463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8264124705834084037583605 774761691171945378523463)
                      ·
                        rfl

theorem cell23_1508843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_1508843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508843 prefixEnd_1508843 := by exact prefixLift 1508843
  have htrace : WordTrace (prefixWord ++ tailWord_1508843) baseStart_1508843 baseEnd_1508843 := by
    simpa [prefixWord, tailWord_1508843, baseEnd_1508843] using wordTrace_append hprefix tailTrace_1508843
  have hstable : (prefixWord ++ tailWord_1508843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508843).length < 2 ^ (prefixWord ++ tailWord_1508843).sum := by decide
  have hdescent : baseEnd_1508843 < baseStart_1508843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508854 : List Nat := [5, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_1508854 : Nat := 118140960795 + 1508854 * 2 ^ 59
def prefixEnd_1508854 : Nat := 4983230072969 + 3 ^ 40 * 1508854 * 2
def baseEnd_1508854 : Nat := 86085259939904981720657

theorem tailTrace_1508854 : CollatzResearch.WordTrace tailWord_1508854 prefixEnd_1508854 86085259939904981720657 := by
  unfold tailWord_1508854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3439526654730445287026351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36688284317124749728281077 3439526654730445287026351)
  ·
    refine ⟨5159289982095667930539527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3439526654730445287026351 5159289982095667930539527)
    ·
      refine ⟨7738934973143501895809291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5159289982095667930539527 7738934973143501895809291)
      ·
        refine ⟨11608402459715252843713937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7738934973143501895809291 11608402459715252843713937)
        ·
          refine ⟨8706301844786439632785453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11608402459715252843713937 8706301844786439632785453)
          ·
            refine ⟨3264863191794914862294545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8706301844786439632785453 3264863191794914862294545)
            ·
              refine ⟨2448647393846186146720909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3264863191794914862294545 2448647393846186146720909)
              ·
                refine ⟨918242772692319805020341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2448647393846186146720909 918242772692319805020341)
                ·
                  refine ⟨86085259939904981720657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 918242772692319805020341 86085259939904981720657)
                  ·
                    rfl

theorem cell23_1508854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_1508854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508854 prefixEnd_1508854 := by exact prefixLift 1508854
  have htrace : WordTrace (prefixWord ++ tailWord_1508854) baseStart_1508854 baseEnd_1508854 := by
    simpa [prefixWord, tailWord_1508854, baseEnd_1508854] using wordTrace_append hprefix tailTrace_1508854
  have hstable : (prefixWord ++ tailWord_1508854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508854).length < 2 ^ (prefixWord ++ tailWord_1508854).sum := by decide
  have hdescent : baseEnd_1508854 < baseStart_1508854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508897 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 3, 4]
def baseStart_1508897 : Nat := 118140960795 + 1508897 * 2 ^ 59
def prefixEnd_1508897 : Nat := 4983230072969 + 3 ^ 40 * 1508897 * 2
def baseEnd_1508897 : Nat := 258263139709096055749405

theorem tailTrace_1508897 : CollatzResearch.WordTrace tailWord_1508897 prefixEnd_1508897 258263139709096055749405 := by
  unfold tailWord_1508897
  simp only [CollatzResearch.WordTrace]
  refine ⟨55033994814531342936236945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36689329876354228624157963 55033994814531342936236945)
  ·
    refine ⟨41275496110898507202177709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55033994814531342936236945 41275496110898507202177709)
    ·
      refine ⟨15478311041586940200816641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41275496110898507202177709 15478311041586940200816641)
      ·
        refine ⟨11608733281190205150612481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15478311041586940200816641 11608733281190205150612481)
        ·
          refine ⟨8706549960892653862959361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11608733281190205150612481 8706549960892653862959361)
          ·
            refine ⟨6529912470669490397219521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8706549960892653862959361 6529912470669490397219521)
            ·
              refine ⟨4897434353002117797914641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6529912470669490397219521 4897434353002117797914641)
              ·
                refine ⟨3673075764751588348435981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4897434353002117797914641 3673075764751588348435981)
                ·
                  refine ⟨1377403411781845630663493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3673075764751588348435981 1377403411781845630663493)
                  ·
                    refine ⟨258263139709096055749405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1377403411781845630663493 258263139709096055749405)
                    ·
                      rfl

theorem cell23_1508897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_1508897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508897 prefixEnd_1508897 := by exact prefixLift 1508897
  have htrace : WordTrace (prefixWord ++ tailWord_1508897) baseStart_1508897 baseEnd_1508897 := by
    simpa [prefixWord, tailWord_1508897, baseEnd_1508897] using wordTrace_append hprefix tailTrace_1508897
  have hstable : (prefixWord ++ tailWord_1508897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508897).length < 2 ^ (prefixWord ++ tailWord_1508897).sum := by decide
  have hdescent : baseEnd_1508897 < baseStart_1508897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508924 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_1508924 : Nat := 118140960795 + 1508924 * 2 ^ 59
def prefixEnd_1508924 : Nat := 4983230072969 + 3 ^ 40 * 1508924 * 2
def baseEnd_1508924 : Nat := 774803283104959561610591

theorem tailTrace_1508924 : CollatzResearch.WordTrace tailWord_1508924 prefixEnd_1508924 774803283104959561610591 := by
  unfold tailWord_1508924
  simp only [CollatzResearch.WordTrace]
  refine ⟨27517489792716763273734913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36689986390289017698313217 27517489792716763273734913)
  ·
    refine ⟨20638117344537572455301185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27517489792716763273734913 20638117344537572455301185)
    ·
      refine ⟨15478588008403179341475889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20638117344537572455301185 15478588008403179341475889)
      ·
        refine ⟨11608941006302384506106917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15478588008403179341475889 11608941006302384506106917)
        ·
          refine ⟨2176676438681697094895047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11608941006302384506106917 2176676438681697094895047)
          ·
            refine ⟨3265014658022545642342571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176676438681697094895047 3265014658022545642342571)
            ·
              refine ⟨4897521987033818463513857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265014658022545642342571 4897521987033818463513857)
              ·
                refine ⟨3673141490275363847635393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4897521987033818463513857 3673141490275363847635393)
                ·
                  refine ⟨2754856117706522885726545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3673141490275363847635393 2754856117706522885726545)
                  ·
                    refine ⟨2066142088279892164294909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2754856117706522885726545 2066142088279892164294909)
                    ·
                      refine ⟨774803283104959561610591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2066142088279892164294909 774803283104959561610591)
                      ·
                        rfl

theorem cell23_1508924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_1508924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508924 prefixEnd_1508924 := by exact prefixLift 1508924
  have htrace : WordTrace (prefixWord ++ tailWord_1508924) baseStart_1508924 baseEnd_1508924 := by
    simpa [prefixWord, tailWord_1508924, baseEnd_1508924] using wordTrace_append hprefix tailTrace_1508924
  have hstable : (prefixWord ++ tailWord_1508924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508924).length < 2 ^ (prefixWord ++ tailWord_1508924).sum := by decide
  have hdescent : baseEnd_1508924 < baseStart_1508924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508964 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 2, 3, 2]
def baseStart_1508964 : Nat := 118140960795 + 1508964 * 2 ^ 59
def prefixEnd_1508964 : Nat := 4983230072969 + 3 ^ 40 * 1508964 * 2
def baseEnd_1508964 : Nat := 774823822331139405110407

theorem tailTrace_1508964 : CollatzResearch.WordTrace tailWord_1508964 prefixEnd_1508964 774823822331139405110407 := by
  unfold tailWord_1508964
  simp only [CollatzResearch.WordTrace]
  refine ⟨27518219252644306689462973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36690959003525742252617297 27518219252644306689462973)
  ·
    refine ⟨10319332219741615008548615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27518219252644306689462973 10319332219741615008548615)
    ·
      refine ⟨15478998329612422512822923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10319332219741615008548615 15478998329612422512822923)
      ·
        refine ⟨23218497494418633769234385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15478998329612422512822923 23218497494418633769234385)
        ·
          refine ⟨17413873120813975326925789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23218497494418633769234385 17413873120813975326925789)
          ·
            refine ⟨6530202420305240747597171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17413873120813975326925789 6530202420305240747597171)
            ·
              refine ⟨9795303630457861121395757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6530202420305240747597171 9795303630457861121395757)
              ·
                refine ⟨3673238861421697920523409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9795303630457861121395757 3673238861421697920523409)
                ·
                  refine ⟨2754929146066273440392557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3673238861421697920523409 2754929146066273440392557)
                  ·
                    refine ⟨1033098429774852540147209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2754929146066273440392557 1033098429774852540147209)
                    ·
                      refine ⟨774823822331139405110407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033098429774852540147209 774823822331139405110407)
                      ·
                        rfl

theorem cell23_1508964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_1508964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508964 prefixEnd_1508964 := by exact prefixLift 1508964
  have htrace : WordTrace (prefixWord ++ tailWord_1508964) baseStart_1508964 baseEnd_1508964 := by
    simpa [prefixWord, tailWord_1508964, baseEnd_1508964] using wordTrace_append hprefix tailTrace_1508964
  have hstable : (prefixWord ++ tailWord_1508964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508964).length < 2 ^ (prefixWord ++ tailWord_1508964).sum := by decide
  have hdescent : baseEnd_1508964 < baseStart_1508964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508977 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 4]
def baseStart_1508977 : Nat := 118140960795 + 1508977 * 2 ^ 59
def prefixEnd_1508977 : Nat := 4983230072969 + 3 ^ 40 * 1508977 * 2
def baseEnd_1508977 : Nat := 774830497579647854247847

theorem tailTrace_1508977 : CollatzResearch.WordTrace tailWord_1508977 prefixEnd_1508977 774830497579647854247847 := by
  unfold tailWord_1508977
  simp only [CollatzResearch.WordTrace]
  refine ⟨55036912654241516599149185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36691275102827677732766123 55036912654241516599149185)
  ·
    refine ⟨41277684490681137449361889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55036912654241516599149185 41277684490681137449361889)
    ·
      refine ⟨30958263368010853087021417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41277684490681137449361889 30958263368010853087021417)
      ·
        refine ⟨23218697526008139815266063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30958263368010853087021417 23218697526008139815266063)
        ·
          refine ⟨34828046289012209722899095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23218697526008139815266063 34828046289012209722899095)
          ·
            refine ⟨52242069433518314584348643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34828046289012209722899095 52242069433518314584348643)
            ·
              refine ⟨78363104150277471876522965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52242069433518314584348643 78363104150277471876522965)
              ·
                refine ⟨1836635253522128247106007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 78363104150277471876522965 1836635253522128247106007)
                ·
                  refine ⟨2754952880283192370659011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836635253522128247106007 2754952880283192370659011)
                  ·
                    refine ⟨4132429320424788555988517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2754952880283192370659011 4132429320424788555988517)
                    ·
                      refine ⟨774830497579647854247847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4132429320424788555988517 774830497579647854247847)
                      ·
                        rfl

theorem cell23_1508977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_1508977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508977 prefixEnd_1508977 := by exact prefixLift 1508977
  have htrace : WordTrace (prefixWord ++ tailWord_1508977) baseStart_1508977 baseEnd_1508977 := by
    simpa [prefixWord, tailWord_1508977, baseEnd_1508977] using wordTrace_append hprefix tailTrace_1508977
  have hstable : (prefixWord ++ tailWord_1508977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508977).length < 2 ^ (prefixWord ++ tailWord_1508977).sum := by decide
  have hdescent : baseEnd_1508977 < baseStart_1508977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508981 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1508981 : Nat := 118140960795 + 1508981 * 2 ^ 59
def prefixEnd_1508981 : Nat := 4983230072969 + 3 ^ 40 * 1508981 * 2
def baseEnd_1508981 : Nat := 774832551502265838597829

theorem tailTrace_1508981 : CollatzResearch.WordTrace tailWord_1508981 prefixEnd_1508981 774832551502265838597829 := by
  unfold tailWord_1508981
  simp only [CollatzResearch.WordTrace]
  refine ⟨55037058546227025282294797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36691372364151350188196531 55037058546227025282294797)
  ·
    refine ⟨20638896954835134480860549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55037058546227025282294797 20638896954835134480860549)
    ·
      refine ⟨3869793179031587715161353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20638896954835134480860549 3869793179031587715161353)
      ·
        refine ⟨2902344884273690786371015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3869793179031587715161353 2902344884273690786371015)
        ·
          refine ⟨4353517326410536179556523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2902344884273690786371015 4353517326410536179556523)
          ·
            refine ⟨6530275989615804269334785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4353517326410536179556523 6530275989615804269334785)
            ·
              refine ⟨4897706992211853202001089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6530275989615804269334785 4897706992211853202001089)
              ·
                refine ⟨3673280244158889901500817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4897706992211853202001089 3673280244158889901500817)
                ·
                  refine ⟨2754960183119167426125613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3673280244158889901500817 2754960183119167426125613)
                  ·
                    refine ⟨1033110068669687784797105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2754960183119167426125613 1033110068669687784797105)
                    ·
                      refine ⟨774832551502265838597829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033110068669687784797105 774832551502265838597829)
                      ·
                        rfl

theorem cell23_1508981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1508981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508981 prefixEnd_1508981 := by exact prefixLift 1508981
  have htrace : WordTrace (prefixWord ++ tailWord_1508981) baseStart_1508981 baseEnd_1508981 := by
    simpa [prefixWord, tailWord_1508981, baseEnd_1508981] using wordTrace_append hprefix tailTrace_1508981
  have hstable : (prefixWord ++ tailWord_1508981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508981).length < 2 ^ (prefixWord ++ tailWord_1508981).sum := by decide
  have hdescent : baseEnd_1508981 < baseStart_1508981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508997 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 5, 2, 3]
def baseStart_1508997 : Nat := 118140960795 + 1508997 * 2 ^ 59
def prefixEnd_1508997 : Nat := 4983230072969 + 3 ^ 40 * 1508997 * 2
def baseEnd_1508997 : Nat := 774840767192737775997755

theorem tailTrace_1508997 : CollatzResearch.WordTrace tailWord_1508997 prefixEnd_1508997 774840767192737775997755 := by
  unfold tailWord_1508997
  simp only [CollatzResearch.WordTrace]
  refine ⟨55037642114169060014877245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36691761409446040009918163 55037642114169060014877245)
  ·
    refine ⟨20639115792813397505578967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55037642114169060014877245 20639115792813397505578967)
    ·
      refine ⟨30958673689220096258368451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20639115792813397505578967 30958673689220096258368451)
      ·
        refine ⟨46438010533830144387552677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30958673689220096258368451 46438010533830144387552677)
        ·
          refine ⟨8707126975093152072666127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46438010533830144387552677 8707126975093152072666127)
          ·
            refine ⟨13060690462639728108999191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8707126975093152072666127 13060690462639728108999191)
            ·
              refine ⟨19591035693959592163498787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13060690462639728108999191 19591035693959592163498787)
              ·
                refine ⟨29386553540939388245248181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19591035693959592163498787 29386553540939388245248181)
                ·
                  refine ⟨2754989394463067647992017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29386553540939388245248181 2754989394463067647992017)
                  ·
                    refine ⟨2066242045847300735994013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2754989394463067647992017 2066242045847300735994013)
                    ·
                      refine ⟨774840767192737775997755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2066242045847300735994013 774840767192737775997755)
                      ·
                        rfl

theorem cell23_1508997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_1508997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1508997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1508997 prefixEnd_1508997 := by exact prefixLift 1508997
  have htrace : WordTrace (prefixWord ++ tailWord_1508997) baseStart_1508997 baseEnd_1508997 := by
    simpa [prefixWord, tailWord_1508997, baseEnd_1508997] using wordTrace_append hprefix tailTrace_1508997
  have hstable : (prefixWord ++ tailWord_1508997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508997).length < 2 ^ (prefixWord ++ tailWord_1508997).sum := by decide
  have hdescent : baseEnd_1508997 < baseStart_1508997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509027 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 3]
def baseStart_1509027 : Nat := 118140960795 + 1509027 * 2 ^ 59
def prefixEnd_1509027 : Nat := 4983230072969 + 3 ^ 40 * 1509027 * 2
def baseEnd_1509027 : Nat := 774856171612372658622617

theorem tailTrace_1509027 : CollatzResearch.WordTrace tailWord_1509027 prefixEnd_1509027 774856171612372658622617 := by
  unfold tailWord_1509027
  simp only [CollatzResearch.WordTrace]
  refine ⟨55038736304060375138469335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36692490869373583425646223 55038736304060375138469335)
  ·
    refine ⟨82558104456090562707704003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55038736304060375138469335 82558104456090562707704003)
    ·
      refine ⟨123837156684135844061556005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82558104456090562707704003 123837156684135844061556005)
      ·
        refine ⟨23219466878275470761541751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123837156684135844061556005 23219466878275470761541751)
        ·
          refine ⟨34829200317413206142312627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23219466878275470761541751 34829200317413206142312627)
          ·
            refine ⟨52243800476119809213468941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34829200317413206142312627 52243800476119809213468941)
            ·
              refine ⟨19591425178544928455050853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52243800476119809213468941 19591425178544928455050853)
              ·
                refine ⟨3673392220977174085322035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19591425178544928455050853 3673392220977174085322035)
                ·
                  refine ⟨5510088331465761127983053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3673392220977174085322035 5510088331465761127983053)
                  ·
                    refine ⟨2066283124299660422993645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5510088331465761127983053 2066283124299660422993645)
                    ·
                      refine ⟨774856171612372658622617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2066283124299660422993645 774856171612372658622617)
                      ·
                        rfl

theorem cell23_1509027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_1509027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509027 prefixEnd_1509027 := by exact prefixLift 1509027
  have htrace : WordTrace (prefixWord ++ tailWord_1509027) baseStart_1509027 baseEnd_1509027 := by
    simpa [prefixWord, tailWord_1509027, baseEnd_1509027] using wordTrace_append hprefix tailTrace_1509027
  have hstable : (prefixWord ++ tailWord_1509027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509027).length < 2 ^ (prefixWord ++ tailWord_1509027).sum := by decide
  have hdescent : baseEnd_1509027 < baseStart_1509027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509028 : List Nat := [2, 3, 1, 2, 2, 2, 1, 5, 1, 2, 2]
def baseStart_1509028 : Nat := 118140960795 + 1509028 * 2 ^ 59
def prefixEnd_1509028 : Nat := 4983230072969 + 3 ^ 40 * 1509028 * 2
def baseEnd_1509028 : Nat := 774856685093027154710113

theorem tailTrace_1509028 : CollatzResearch.WordTrace tailWord_1509028 prefixEnd_1509028 774856685093027154710113 := by
  unfold tailWord_1509028
  simp only [CollatzResearch.WordTrace]
  refine ⟨27519386388528376154627869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36692515184704501539503825 27519386388528376154627869)
  ·
    refine ⟨10319769895698141057985451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27519386388528376154627869 10319769895698141057985451)
    ·
      refine ⟨15479654843547211586978177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10319769895698141057985451 15479654843547211586978177)
      ·
        refine ⟨11609741132660408690233633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15479654843547211586978177 11609741132660408690233633)
        ·
          refine ⟨8707305849495306517675225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11609741132660408690233633 8707305849495306517675225)
          ·
            refine ⟨6530479387121479888256419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8707305849495306517675225 6530479387121479888256419)
            ·
              refine ⟨9795719080682219832384629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6530479387121479888256419 9795719080682219832384629)
              ·
                refine ⟨918348663813958109286059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9795719080682219832384629 918348663813958109286059)
                ·
                  refine ⟨1377522995720937163929089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918348663813958109286059 1377522995720937163929089)
                  ·
                    refine ⟨1033142246790702872946817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1377522995720937163929089 1033142246790702872946817)
                    ·
                      refine ⟨774856685093027154710113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033142246790702872946817 774856685093027154710113)
                      ·
                        rfl

theorem cell23_1509028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_1509028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509028 prefixEnd_1509028 := by exact prefixLift 1509028
  have htrace : WordTrace (prefixWord ++ tailWord_1509028) baseStart_1509028 baseEnd_1509028 := by
    simpa [prefixWord, tailWord_1509028, baseEnd_1509028] using wordTrace_append hprefix tailTrace_1509028
  have hstable : (prefixWord ++ tailWord_1509028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509028).length < 2 ^ (prefixWord ++ tailWord_1509028).sum := by decide
  have hdescent : baseEnd_1509028 < baseStart_1509028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509058 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1509058 : Nat := 118140960795 + 1509058 * 2 ^ 59
def prefixEnd_1509058 : Nat := 4983230072969 + 3 ^ 40 * 1509058 * 2
def baseEnd_1509058 : Nat := 774872089512662037334975

theorem tailTrace_1509058 : CollatzResearch.WordTrace tailWord_1509058 prefixEnd_1509058 774872089512662037334975 := by
  unfold tailWord_1509058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13759966741737016858211957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36693244644632044955231885 13759966741737016858211957)
  ·
    refine ⟨1289996882037845330457371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13759966741737016858211957 1289996882037845330457371)
    ·
      refine ⟨1934995323056767995686057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1289996882037845330457371 1934995323056767995686057)
      ·
        refine ⟨1451246492292575996764543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1934995323056767995686057 1451246492292575996764543)
        ·
          refine ⟨2176869738438863995146815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451246492292575996764543 2176869738438863995146815)
          ·
            refine ⟨3265304607658295992720223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176869738438863995146815 3265304607658295992720223)
            ·
              refine ⟨4897956911487443989080335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265304607658295992720223 4897956911487443989080335)
              ·
                refine ⟨7346935367231165983620503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4897956911487443989080335 7346935367231165983620503)
                ·
                  refine ⟨11020403050846748975430755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7346935367231165983620503 11020403050846748975430755)
                  ·
                    refine ⟨16530604576270123463146133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11020403050846748975430755 16530604576270123463146133)
                    ·
                      refine ⟨774872089512662037334975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16530604576270123463146133 774872089512662037334975)
                      ·
                        rfl

theorem cell23_1509058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1509058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509058 prefixEnd_1509058 := by exact prefixLift 1509058
  have htrace : WordTrace (prefixWord ++ tailWord_1509058) baseStart_1509058 baseEnd_1509058 := by
    simpa [prefixWord, tailWord_1509058, baseEnd_1509058] using wordTrace_append hprefix tailTrace_1509058
  have hstable : (prefixWord ++ tailWord_1509058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509058).length < 2 ^ (prefixWord ++ tailWord_1509058).sum := by decide
  have hdescent : baseEnd_1509058 < baseStart_1509058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509087 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1509087 : Nat := 118140960795 + 1509087 * 2 ^ 59
def prefixEnd_1509087 : Nat := 4983230072969 + 3 ^ 40 * 1509087 * 2
def baseEnd_1509087 : Nat := 774886980451642423872341

theorem tailTrace_1509087 : CollatzResearch.WordTrace tailWord_1509087 prefixEnd_1509087 774886980451642423872341 := by
  unfold tailWord_1509087
  simp only [CollatzResearch.WordTrace]
  refine ⟨55040924683843005385653515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36693949789228670257102343 55040924683843005385653515)
  ·
    refine ⟨82561387025764508078480273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55040924683843005385653515 82561387025764508078480273)
    ·
      refine ⟨61921040269323381058860205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82561387025764508078480273 61921040269323381058860205)
      ·
        refine ⟨23220390100996267897072577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61921040269323381058860205 23220390100996267897072577)
        ·
          refine ⟨17415292575747200922804433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23220390100996267897072577 17415292575747200922804433)
          ·
            refine ⟨13061469431810400692103325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17415292575747200922804433 13061469431810400692103325)
            ·
              refine ⟨4898051036928900259538747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13061469431810400692103325 4898051036928900259538747)
              ·
                refine ⟨7347076555393350389308121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898051036928900259538747 7347076555393350389308121)
                ·
                  refine ⟨5510307416545012791981091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7347076555393350389308121 5510307416545012791981091)
                  ·
                    refine ⟨8265461124817519187971637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5510307416545012791981091 8265461124817519187971637)
                    ·
                      refine ⟨774886980451642423872341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8265461124817519187971637 774886980451642423872341)
                      ·
                        rfl

theorem cell23_1509087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1509087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509087 prefixEnd_1509087 := by exact prefixLift 1509087
  have htrace : WordTrace (prefixWord ++ tailWord_1509087) baseStart_1509087 baseEnd_1509087 := by
    simpa [prefixWord, tailWord_1509087, baseEnd_1509087] using wordTrace_append hprefix tailTrace_1509087
  have hstable : (prefixWord ++ tailWord_1509087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509087).length < 2 ^ (prefixWord ++ tailWord_1509087).sum := by decide
  have hdescent : baseEnd_1509087 < baseStart_1509087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509107 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 7]
def baseStart_1509107 : Nat := 118140960795 + 1509107 * 2 ^ 59
def prefixEnd_1509107 : Nat := 4983230072969 + 3 ^ 40 * 1509107 * 2
def baseEnd_1509107 : Nat := 86099694451636927291361

theorem tailTrace_1509107 : CollatzResearch.WordTrace tailWord_1509107 prefixEnd_1509107 86099694451636927291361 := by
  unfold tailWord_1509107
  simp only [CollatzResearch.WordTrace]
  refine ⟨55041654143770548801381575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36694436095847032534254383 55041654143770548801381575)
  ·
    refine ⟨82562481215655823202072363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55041654143770548801381575 82562481215655823202072363)
    ·
      refine ⟨123843721823483734803108545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82562481215655823202072363 123843721823483734803108545)
      ·
        refine ⟨92882791367612801102331409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123843721823483734803108545 92882791367612801102331409)
        ·
          refine ⟨69662093525709600826748557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92882791367612801102331409 69662093525709600826748557)
          ·
            refine ⟨26123285072141100310030709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69662093525709600826748557 26123285072141100310030709)
            ·
              refine ⟨2449057975513228154065379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26123285072141100310030709 2449057975513228154065379)
              ·
                refine ⟨3673586963269842231098069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449057975513228154065379 3673586963269842231098069)
                ·
                  refine ⟨86099694451636927291361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3673586963269842231098069 86099694451636927291361)
                  ·
                    rfl

theorem cell23_1509107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 7].length) (baseStart_1509107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509107 prefixEnd_1509107 := by exact prefixLift 1509107
  have htrace : WordTrace (prefixWord ++ tailWord_1509107) baseStart_1509107 baseEnd_1509107 := by
    simpa [prefixWord, tailWord_1509107, baseEnd_1509107] using wordTrace_append hprefix tailTrace_1509107
  have hstable : (prefixWord ++ tailWord_1509107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509107).length < 2 ^ (prefixWord ++ tailWord_1509107).sum := by decide
  have hdescent : baseEnd_1509107 < baseStart_1509107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
