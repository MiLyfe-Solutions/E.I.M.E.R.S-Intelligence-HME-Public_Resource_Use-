import V185TrunkScan23Chunk1127

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6681316 : List Nat := [2, 3, 1, 1, 1, 6, 2, 7]
def baseStart_6681316 : Nat := 118140960795 + 6681316 * 2 ^ 59
def prefixEnd_6681316 : Nat := 4983230072969 + 3 ^ 40 * 6681316 * 2
def baseEnd_6681316 : Nat := 127063944910195798300859

theorem tailTrace_6681316 : CollatzResearch.WordTrace tailWord_6681316 prefixEnd_6681316 127063944910195798300859 := by
  unfold tailWord_6681316
  simp only [CollatzResearch.WordTrace]
  refine ⟨121843807131370342386027901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162458409508493789848037201 121843807131370342386027901)
  ·
    refine ⟨45691427674263878394760463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121843807131370342386027901 45691427674263878394760463)
    ·
      refine ⟨68537141511395817592140695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45691427674263878394760463 68537141511395817592140695)
      ·
        refine ⟨102805712267093726388211043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68537141511395817592140695 102805712267093726388211043)
        ·
          refine ⟨154208568400640589582316565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102805712267093726388211043 154208568400640589582316565)
          ·
            refine ⟨7228526643780027636671089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154208568400640589582316565 7228526643780027636671089)
            ·
              refine ⟨5421394982835020727503317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7228526643780027636671089 5421394982835020727503317)
              ·
                refine ⟨127063944910195798300859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5421394982835020727503317 127063944910195798300859)
                ·
                  rfl

theorem cell23_6681316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 7].length) (baseStart_6681316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681316 prefixEnd_6681316 := by exact prefixLift 6681316
  have htrace : WordTrace (prefixWord ++ tailWord_6681316) baseStart_6681316 baseEnd_6681316 := by
    simpa [prefixWord, tailWord_6681316, baseEnd_6681316] using wordTrace_append hprefix tailTrace_6681316
  have hstable : (prefixWord ++ tailWord_6681316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681316).length < 2 ^ (prefixWord ++ tailWord_6681316).sum := by decide
  have hdescent : baseEnd_6681316 < baseStart_6681316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681327 : List Nat := [1, 1, 2, 1, 5, 4, 1, 3, 1, 2, 2]
def baseStart_6681327 : Nat := 118140960795 + 6681327 * 2 ^ 59
def prefixEnd_6681327 : Nat := 4983230072969 + 3 ^ 40 * 6681327 * 2
def baseEnd_6681327 : Nat := 3430732160862486011085643

theorem tailTrace_6681327 : CollatzResearch.WordTrace tailWord_6681327 prefixEnd_6681327 3430732160862486011085643 := by
  unfold tailWord_6681327
  simp only [CollatzResearch.WordTrace]
  refine ⟨243688015465700833650706235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162458676977133889100470823 243688015465700833650706235)
  ·
    refine ⟨365532023198551250476059353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243688015465700833650706235 365532023198551250476059353)
    ·
      refine ⟨274149017398913437857044515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365532023198551250476059353 274149017398913437857044515)
      ·
        refine ⟨411223526098370156785566773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274149017398913437857044515 411223526098370156785566773)
        ·
          refine ⟨38552205571722202198646885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 411223526098370156785566773 38552205571722202198646885)
          ·
            refine ⟨7228538544697912912246291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38552205571722202198646885 7228538544697912912246291)
            ·
              refine ⟨10842807817046869368369437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7228538544697912912246291 10842807817046869368369437)
              ·
                refine ⟨4066052931392576013138539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10842807817046869368369437 4066052931392576013138539)
                ·
                  refine ⟨6099079397088864019707809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4066052931392576013138539 6099079397088864019707809)
                  ·
                    refine ⟨4574309547816648014780857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6099079397088864019707809 4574309547816648014780857)
                    ·
                      refine ⟨3430732160862486011085643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574309547816648014780857 3430732160862486011085643)
                      ·
                        rfl

theorem cell23_6681327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 1, 2, 2].length) (baseStart_6681327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681327 prefixEnd_6681327 := by exact prefixLift 6681327
  have htrace : WordTrace (prefixWord ++ tailWord_6681327) baseStart_6681327 baseEnd_6681327 := by
    simpa [prefixWord, tailWord_6681327, baseEnd_6681327] using wordTrace_append hprefix tailTrace_6681327
  have hstable : (prefixWord ++ tailWord_6681327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681327).length < 2 ^ (prefixWord ++ tailWord_6681327).sum := by decide
  have hdescent : baseEnd_6681327 < baseStart_6681327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681369 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 4, 4, 3]
def baseStart_6681369 : Nat := 118140960795 + 6681369 * 2 ^ 59
def prefixEnd_6681369 : Nat := 4983230072969 + 3 ^ 40 * 6681369 * 2
def baseEnd_6681369 : Nat := 3430753727049974846760449

theorem tailTrace_6681369 : CollatzResearch.WordTrace tailWord_6681369 prefixEnd_6681369 3430753727049974846760449 := by
  unfold tailWord_6681369
  simp only [CollatzResearch.WordTrace]
  refine ⟨243689547331548674823735161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162459698221032449882490107 243689547331548674823735161)
  ·
    refine ⟨182767160498661506117801371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243689547331548674823735161 182767160498661506117801371)
    ·
      refine ⟨274150740747992259176702057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182767160498661506117801371 274150740747992259176702057)
      ·
        refine ⟨205613055560994194382526543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274150740747992259176702057 205613055560994194382526543)
        ·
          refine ⟨308419583341491291573789815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205613055560994194382526543 308419583341491291573789815)
          ·
            refine ⟨462629375012236937360684723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308419583341491291573789815 462629375012236937360684723)
            ·
              refine ⟨693944062518355406041027085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462629375012236937360684723 693944062518355406041027085)
              ·
                refine ⟨260229023444383277265385157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 693944062518355406041027085 260229023444383277265385157)
                ·
                  refine ⟨48792941895821864487259717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260229023444383277265385157 48792941895821864487259717)
                  ·
                    refine ⟨9148676605466599591361197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48792941895821864487259717 9148676605466599591361197)
                    ·
                      refine ⟨3430753727049974846760449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9148676605466599591361197 3430753727049974846760449)
                      ·
                        rfl

theorem cell23_6681369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_6681369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681369 prefixEnd_6681369 := by exact prefixLift 6681369
  have htrace : WordTrace (prefixWord ++ tailWord_6681369) baseStart_6681369 baseEnd_6681369 := by
    simpa [prefixWord, tailWord_6681369, baseEnd_6681369] using wordTrace_append hprefix tailTrace_6681369
  have hstable : (prefixWord ++ tailWord_6681369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681369).length < 2 ^ (prefixWord ++ tailWord_6681369).sum := by decide
  have hdescent : baseEnd_6681369 < baseStart_6681369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681379 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 4]
def baseStart_6681379 : Nat := 118140960795 + 6681379 * 2 ^ 59
def prefixEnd_6681379 : Nat := 4983230072969 + 3 ^ 40 * 6681379 * 2
def baseEnd_6681379 : Nat := 3430758861856519807635403

theorem tailTrace_6681379 : CollatzResearch.WordTrace tailWord_6681379 prefixEnd_6681379 3430758861856519807635403 := by
  unfold tailWord_6681379
  simp only [CollatzResearch.WordTrace]
  refine ⟨243689912061512446531599191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162459941374341631021066127 243689912061512446531599191)
  ·
    refine ⟨365534868092268669797398787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243689912061512446531599191 365534868092268669797398787)
    ·
      refine ⟨548302302138403004696098181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365534868092268669797398787 548302302138403004696098181)
      ·
        refine ⟨102806681650950563380518409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 548302302138403004696098181 102806681650950563380518409)
        ·
          refine ⟨77105011238212922535388807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102806681650950563380518409 77105011238212922535388807)
          ·
            refine ⟨115657516857319383803083211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77105011238212922535388807 115657516857319383803083211)
            ·
              refine ⟨173486275285979075704624817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115657516857319383803083211 173486275285979075704624817)
              ·
                refine ⟨130114706464484306778468613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173486275285979075704624817 130114706464484306778468613)
                ·
                  refine ⟨24396507462090807520962865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130114706464484306778468613 24396507462090807520962865)
                  ·
                    refine ⟨18297380596568105640722149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24396507462090807520962865 18297380596568105640722149)
                    ·
                      refine ⟨3430758861856519807635403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18297380596568105640722149 3430758861856519807635403)
                      ·
                        rfl

theorem cell23_6681379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_6681379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681379 prefixEnd_6681379 := by exact prefixLift 6681379
  have htrace : WordTrace (prefixWord ++ tailWord_6681379) baseStart_6681379 baseEnd_6681379 := by
    simpa [prefixWord, tailWord_6681379, baseEnd_6681379] using wordTrace_append hprefix tailTrace_6681379
  have hstable : (prefixWord ++ tailWord_6681379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681379).length < 2 ^ (prefixWord ++ tailWord_6681379).sum := by decide
  have hdescent : baseEnd_6681379 < baseStart_6681379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681400 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 2, 2, 2]
def baseStart_6681400 : Nat := 118140960795 + 6681400 * 2 ^ 59
def prefixEnd_6681400 : Nat := 4983230072969 + 3 ^ 40 * 6681400 * 2
def baseEnd_6681400 : Nat := 3430769644950264225472807

theorem tailTrace_6681400 : CollatzResearch.WordTrace tailWord_6681400 prefixEnd_6681400 3430769644950264225472807 := by
  unfold tailWord_6681400
  simp only [CollatzResearch.WordTrace]
  refine ⟨121845338997218183559056827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162460451996290911412075769 121845338997218183559056827)
  ·
    refine ⟨182768008495827275338585241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121845338997218183559056827 182768008495827275338585241)
    ·
      refine ⟨137076006371870456503938931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182768008495827275338585241 137076006371870456503938931)
      ·
        refine ⟨205614009557805684755908397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137076006371870456503938931 205614009557805684755908397)
        ·
          refine ⟨77105253584177131783465649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205614009557805684755908397 77105253584177131783465649)
          ·
            refine ⟨57828940188132848837599237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77105253584177131783465649 57828940188132848837599237)
            ·
              refine ⟨10842926285274909157049857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57828940188132848837599237 10842926285274909157049857)
              ·
                refine ⟨8132194713956181867787393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10842926285274909157049857 8132194713956181867787393)
                ·
                  refine ⟨6099146035467136400840545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8132194713956181867787393 6099146035467136400840545)
                  ·
                    refine ⟨4574359526600352300630409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6099146035467136400840545 4574359526600352300630409)
                    ·
                      refine ⟨3430769644950264225472807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574359526600352300630409 3430769644950264225472807)
                      ·
                        rfl

theorem cell23_6681400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2, 2, 2].length) (baseStart_6681400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681400 prefixEnd_6681400 := by exact prefixLift 6681400
  have htrace : WordTrace (prefixWord ++ tailWord_6681400) baseStart_6681400 baseEnd_6681400 := by
    simpa [prefixWord, tailWord_6681400, baseEnd_6681400] using wordTrace_append hprefix tailTrace_6681400
  have hstable : (prefixWord ++ tailWord_6681400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681400).length < 2 ^ (prefixWord ++ tailWord_6681400).sum := by decide
  have hdescent : baseEnd_6681400 < baseStart_6681400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681416 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_6681416 : Nat := 118140960795 + 6681416 * 2 ^ 59
def prefixEnd_6681416 : Nat := 4983230072969 + 3 ^ 40 * 6681416 * 2
def baseEnd_6681416 : Nat := 3430777860640736162872733

theorem tailTrace_6681416 : CollatzResearch.WordTrace tailWord_6681416 prefixEnd_6681416 3430777860640736162872733 := by
  unfold tailWord_6681416
  simp only [CollatzResearch.WordTrace]
  refine ⟨121845630781189200925348051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162460841041585601233797401 121845630781189200925348051)
  ·
    refine ⟨182768446171783801388022077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121845630781189200925348051 182768446171783801388022077)
    ·
      refine ⟨68538167314418925520508279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182768446171783801388022077 68538167314418925520508279)
      ·
        refine ⟨102807250971628388280762419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68538167314418925520508279 102807250971628388280762419)
        ·
          refine ⟨154210876457442582421143629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102807250971628388280762419 154210876457442582421143629)
          ·
            refine ⟨57829078671540968407928861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154210876457442582421143629 57829078671540968407928861)
            ·
              refine ⟨21685904501827863152973323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57829078671540968407928861 21685904501827863152973323)
              ·
                refine ⟨32528856752741794729459985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21685904501827863152973323 32528856752741794729459985)
                ·
                  refine ⟨24396642564556346047094989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32528856752741794729459985 24396642564556346047094989)
                  ·
                    refine ⟨9148740961708629767660621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24396642564556346047094989 9148740961708629767660621)
                    ·
                      refine ⟨3430777860640736162872733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9148740961708629767660621 3430777860640736162872733)
                      ·
                        rfl

theorem cell23_6681416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_6681416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681416 prefixEnd_6681416 := by exact prefixLift 6681416
  have htrace : WordTrace (prefixWord ++ tailWord_6681416) baseStart_6681416 baseEnd_6681416 := by
    simpa [prefixWord, tailWord_6681416, baseEnd_6681416] using wordTrace_append hprefix tailTrace_6681416
  have hstable : (prefixWord ++ tailWord_6681416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681416).length < 2 ^ (prefixWord ++ tailWord_6681416).sum := by decide
  have hdescent : baseEnd_6681416 < baseStart_6681416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681456 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 4]
def baseStart_6681456 : Nat := 118140960795 + 6681456 * 2 ^ 59
def prefixEnd_6681456 : Nat := 4983230072969 + 3 ^ 40 * 6681456 * 2
def baseEnd_6681456 : Nat := 3430798399866916006372549

theorem tailTrace_6681456 : CollatzResearch.WordTrace tailWord_6681456 prefixEnd_6681456 3430798399866916006372549 := by
  unfold tailWord_6681456
  simp only [CollatzResearch.WordTrace]
  refine ⟨121846360241116744341076111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162461813654822325788101481 121846360241116744341076111)
  ·
    refine ⟨182769540361675116511614167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121846360241116744341076111 182769540361675116511614167)
    ·
      refine ⟨274154310542512674767421251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182769540361675116511614167 274154310542512674767421251)
      ·
        refine ⟨411231465813769012151131877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274154310542512674767421251 411231465813769012151131877)
        ·
          refine ⟨77105899840081689778337227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 411231465813769012151131877 77105899840081689778337227)
          ·
            refine ⟨115658849760122534667505841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77105899840081689778337227 115658849760122534667505841)
            ·
              refine ⟨86744137320091901000629381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115658849760122534667505841 86744137320091901000629381)
              ·
                refine ⟨16264525747517231437618009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86744137320091901000629381 16264525747517231437618009)
                ·
                  refine ⟨12198394310637923578213507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16264525747517231437618009 12198394310637923578213507)
                  ·
                    refine ⟨18297591465956885367320261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12198394310637923578213507 18297591465956885367320261)
                    ·
                      refine ⟨3430798399866916006372549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18297591465956885367320261 3430798399866916006372549)
                      ·
                        rfl

theorem cell23_6681456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_6681456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681456 prefixEnd_6681456 := by exact prefixLift 6681456
  have htrace : WordTrace (prefixWord ++ tailWord_6681456) baseStart_6681456 baseEnd_6681456 := by
    simpa [prefixWord, tailWord_6681456, baseEnd_6681456] using wordTrace_append hprefix tailTrace_6681456
  have hstable : (prefixWord ++ tailWord_6681456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681456).length < 2 ^ (prefixWord ++ tailWord_6681456).sum := by decide
  have hdescent : baseEnd_6681456 < baseStart_6681456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681459 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 5]
def baseStart_6681459 : Nat := 118140960795 + 6681459 * 2 ^ 59
def prefixEnd_6681459 : Nat := 4983230072969 + 3 ^ 40 * 6681459 * 2
def baseEnd_6681459 : Nat := 3430799940308879494635035

theorem tailTrace_6681459 : CollatzResearch.WordTrace tailWord_6681459 prefixEnd_6681459 3430799940308879494635035 := by
  unfold tailWord_6681459
  simp only [CollatzResearch.WordTrace]
  refine ⟨243692829901222620194511431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162461886600815080129674287 243692829901222620194511431)
  ·
    refine ⟨365539244851833930291767147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243692829901222620194511431 365539244851833930291767147)
    ·
      refine ⟨548308867277750895437650721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365539244851833930291767147 548308867277750895437650721)
      ·
        refine ⟨411231650458313171578238041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548308867277750895437650721 411231650458313171578238041)
        ·
          refine ⟨308423737843734878683678531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411231650458313171578238041 308423737843734878683678531)
          ·
            refine ⟨462635606765602318025517797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308423737843734878683678531 462635606765602318025517797)
            ·
              refine ⟨86744176268550434629784587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 462635606765602318025517797 86744176268550434629784587)
              ·
                refine ⟨130116264402825651944676881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86744176268550434629784587 130116264402825651944676881)
                ·
                  refine ⟨97587198302119238958507661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130116264402825651944676881 97587198302119238958507661)
                  ·
                    refine ⟨36595199363294714609440373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97587198302119238958507661 36595199363294714609440373)
                    ·
                      refine ⟨3430799940308879494635035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36595199363294714609440373 3430799940308879494635035)
                      ·
                        rfl

theorem cell23_6681459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_6681459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681459 prefixEnd_6681459 := by exact prefixLift 6681459
  have htrace : WordTrace (prefixWord ++ tailWord_6681459) baseStart_6681459 baseEnd_6681459 := by
    simpa [prefixWord, tailWord_6681459, baseEnd_6681459] using wordTrace_append hprefix tailTrace_6681459
  have hstable : (prefixWord ++ tailWord_6681459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681459).length < 2 ^ (prefixWord ++ tailWord_6681459).sum := by decide
  have hdescent : baseEnd_6681459 < baseStart_6681459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681523 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 3, 1, 3]
def baseStart_6681523 : Nat := 118140960795 + 6681523 * 2 ^ 59
def prefixEnd_6681523 : Nat := 4983230072969 + 3 ^ 40 * 6681523 * 2
def baseEnd_6681523 : Nat := 3430832803070767244234741

theorem tailTrace_6681523 : CollatzResearch.WordTrace tailWord_6681523 prefixEnd_6681523 3430832803070767244234741 := by
  unfold tailWord_6681523
  simp only [CollatzResearch.WordTrace]
  refine ⟨243695164172990759124841223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162463442781993839416560815 243695164172990759124841223)
  ·
    refine ⟨365542746259486138687261835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243695164172990759124841223 365542746259486138687261835)
    ·
      refine ⟨548314119389229208030892753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365542746259486138687261835 548314119389229208030892753)
      ·
        refine ⟨411235589541921906023169565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548314119389229208030892753 411235589541921906023169565)
        ·
          refine ⟨154213346078220714758688587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411235589541921906023169565 154213346078220714758688587)
          ·
            refine ⟨231320019117331072138032881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154213346078220714758688587 231320019117331072138032881)
            ·
              refine ⟨173490014337998304103524661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231320019117331072138032881 173490014337998304103524661)
              ·
                refine ⟨16264688844187341009705437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173490014337998304103524661 16264688844187341009705437)
                ·
                  refine ⟨6099258316570252878639539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16264688844187341009705437 6099258316570252878639539)
                  ·
                    refine ⟨9148887474855379317959309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6099258316570252878639539 9148887474855379317959309)
                    ·
                      refine ⟨3430832803070767244234741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9148887474855379317959309 3430832803070767244234741)
                      ·
                        rfl

theorem cell23_6681523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 1, 3].length) (baseStart_6681523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681523 prefixEnd_6681523 := by exact prefixLift 6681523
  have htrace : WordTrace (prefixWord ++ tailWord_6681523) baseStart_6681523 baseEnd_6681523 := by
    simpa [prefixWord, tailWord_6681523, baseEnd_6681523] using wordTrace_append hprefix tailTrace_6681523
  have hstable : (prefixWord ++ tailWord_6681523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681523).length < 2 ^ (prefixWord ++ tailWord_6681523).sum := by decide
  have hdescent : baseEnd_6681523 < baseStart_6681523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681543 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 1, 5]
def baseStart_6681543 : Nat := 118140960795 + 6681543 * 2 ^ 59
def prefixEnd_6681543 : Nat := 4983230072969 + 3 ^ 40 * 6681543 * 2
def baseEnd_6681543 : Nat := 1143614357561285721994883

theorem tailTrace_6681543 : CollatzResearch.WordTrace tailWord_6681543 prefixEnd_6681543 1143614357561285721994883 := by
  unfold tailWord_6681543
  simp only [CollatzResearch.WordTrace]
  refine ⟨243695893632918302540569283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162463929088612201693712855 243695893632918302540569283)
  ·
    refine ⟨365543840449377453810853925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243695893632918302540569283 365543840449377453810853925)
    ·
      refine ⟨68539470084258272589535111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365543840449377453810853925 68539470084258272589535111)
      ·
        refine ⟨102809205126387408884302667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68539470084258272589535111 102809205126387408884302667)
        ·
          refine ⟨154213807689581113326454001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102809205126387408884302667 154213807689581113326454001)
          ·
            refine ⟨115660355767185834994840501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154213807689581113326454001 115660355767185834994840501)
            ·
              refine ⟨10843158353173672030766297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115660355767185834994840501 10843158353173672030766297)
              ·
                refine ⟨8132368764880254023074723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10843158353173672030766297 8132368764880254023074723)
                ·
                  refine ⟨12198553147320381034612085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8132368764880254023074723 12198553147320381034612085)
                  ·
                    refine ⟨1143614357561285721994883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12198553147320381034612085 1143614357561285721994883)
                    ·
                      rfl

theorem cell23_6681543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_6681543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681543 prefixEnd_6681543 := by exact prefixLift 6681543
  have htrace : WordTrace (prefixWord ++ tailWord_6681543) baseStart_6681543 baseEnd_6681543 := by
    simpa [prefixWord, tailWord_6681543, baseEnd_6681543] using wordTrace_append hprefix tailTrace_6681543
  have hstable : (prefixWord ++ tailWord_6681543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681543).length < 2 ^ (prefixWord ++ tailWord_6681543).sum := by decide
  have hdescent : baseEnd_6681543 < baseStart_6681543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681550 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2]
def baseStart_6681550 : Nat := 118140960795 + 6681550 * 2 ^ 59
def prefixEnd_6681550 : Nat := 4983230072969 + 3 ^ 40 * 6681550 * 2
def baseEnd_6681550 : Nat := 3430846667048438638597117

theorem tailTrace_6681550 : CollatzResearch.WordTrace tailWord_6681550 prefixEnd_6681550 3430846667048438638597117 := by
  unfold tailWord_6681550
  simp only [CollatzResearch.WordTrace]
  refine ⟨30462018617986617842009263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162464099295928628490716069 30462018617986617842009263)
  ·
    refine ⟨45693027926979926763013895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30462018617986617842009263 45693027926979926763013895)
    ·
      refine ⟨68539541890469890144520843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45693027926979926763013895 68539541890469890144520843)
      ·
        refine ⟨102809312835704835216781265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68539541890469890144520843 102809312835704835216781265)
        ·
          refine ⟨77106984626778626412585949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102809312835704835216781265 77106984626778626412585949)
          ·
            refine ⟨28915119235041984904719731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77106984626778626412585949 28915119235041984904719731)
            ·
              refine ⟨43372678852562977357079597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28915119235041984904719731 43372678852562977357079597)
              ·
                refine ⟨16264754569711116508904849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43372678852562977357079597 16264754569711116508904849)
                ·
                  refine ⟨12198565927283337381678637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16264754569711116508904849 12198565927283337381678637)
                  ·
                    refine ⟨4574462222731251518129489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12198565927283337381678637 4574462222731251518129489)
                    ·
                      refine ⟨3430846667048438638597117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574462222731251518129489 3430846667048438638597117)
                      ·
                        rfl

theorem cell23_6681550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_6681550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681550 prefixEnd_6681550 := by exact prefixLift 6681550
  have htrace : WordTrace (prefixWord ++ tailWord_6681550) baseStart_6681550 baseEnd_6681550 := by
    simpa [prefixWord, tailWord_6681550, baseEnd_6681550] using wordTrace_append hprefix tailTrace_6681550
  have hstable : (prefixWord ++ tailWord_6681550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681550).length < 2 ^ (prefixWord ++ tailWord_6681550).sum := by decide
  have hdescent : baseEnd_6681550 < baseStart_6681550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681560 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 1, 5]
def baseStart_6681560 : Nat := 118140960795 + 6681560 * 2 ^ 59
def prefixEnd_6681560 : Nat := 4983230072969 + 3 ^ 40 * 6681560 * 2
def baseEnd_6681560 : Nat := 1143617267284994533157357

theorem tailTrace_6681560 : CollatzResearch.WordTrace tailWord_6681560 prefixEnd_6681560 1143617267284994533157357 := by
  unfold tailWord_6681560
  simp only [CollatzResearch.WordTrace]
  refine ⟨121848256836928357221969067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162464342449237809629292089 121848256836928357221969067)
  ·
    refine ⟨182772385255392535832953601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121848256836928357221969067 182772385255392535832953601)
    ·
      refine ⟨137079288941544401874715201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182772385255392535832953601 137079288941544401874715201)
      ·
        refine ⟨102809466706158301406036401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137079288941544401874715201 102809466706158301406036401)
        ·
          refine ⟨77107100029618726054527301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102809466706158301406036401 77107100029618726054527301)
          ·
            refine ⟨14457581255553511135223869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77107100029618726054527301 14457581255553511135223869)
            ·
              refine ⟨5421592970832566675708951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14457581255553511135223869 5421592970832566675708951)
              ·
                refine ⟨8132389456248850013563427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5421592970832566675708951 8132389456248850013563427)
                ·
                  refine ⟨12198584184373275020345141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8132389456248850013563427 12198584184373275020345141)
                  ·
                    refine ⟨1143617267284994533157357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12198584184373275020345141 1143617267284994533157357)
                    ·
                      rfl

theorem cell23_6681560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_6681560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681560 prefixEnd_6681560 := by exact prefixLift 6681560
  have htrace : WordTrace (prefixWord ++ tailWord_6681560) baseStart_6681560 baseEnd_6681560 := by
    simpa [prefixWord, tailWord_6681560, baseEnd_6681560] using wordTrace_append hprefix tailTrace_6681560
  have hstable : (prefixWord ++ tailWord_6681560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681560).length < 2 ^ (prefixWord ++ tailWord_6681560).sum := by decide
  have hdescent : baseEnd_6681560 < baseStart_6681560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681576 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6681576 : Nat := 118140960795 + 6681576 * 2 ^ 59
def prefixEnd_6681576 : Nat := 4983230072969 + 3 ^ 40 * 6681576 * 2
def baseEnd_6681576 : Nat := 3430860017545455536871997

theorem tailTrace_6681576 : CollatzResearch.WordTrace tailWord_6681576 prefixEnd_6681576 3430860017545455536871997 := by
  unfold tailWord_6681576
  simp only [CollatzResearch.WordTrace]
  refine ⟨121848548620899374588260291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162464731494532499451013721 121848548620899374588260291)
  ·
    refine ⟨182772822931349061882390437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121848548620899374588260291 182772822931349061882390437)
    ·
      refine ⟨34269904299627949102948207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182772822931349061882390437 34269904299627949102948207)
      ·
        refine ⟨51404856449441923654422311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34269904299627949102948207 51404856449441923654422311)
        ·
          refine ⟨77107284674162885481633467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51404856449441923654422311 77107284674162885481633467)
          ·
            refine ⟨115660927011244328222450201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77107284674162885481633467 115660927011244328222450201)
            ·
              refine ⟨86745695258433246166837651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115660927011244328222450201 86745695258433246166837651)
              ·
                refine ⟨130118542887649869250256477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86745695258433246166837651 130118542887649869250256477)
                ·
                  refine ⟨48794453582868700968846179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130118542887649869250256477 48794453582868700968846179)
                  ·
                    refine ⟨73191680374303051453269269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48794453582868700968846179 73191680374303051453269269)
                    ·
                      refine ⟨3430860017545455536871997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73191680374303051453269269 3430860017545455536871997)
                      ·
                        rfl

theorem cell23_6681576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6681576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681576 prefixEnd_6681576 := by exact prefixLift 6681576
  have htrace : WordTrace (prefixWord ++ tailWord_6681576) baseStart_6681576 baseEnd_6681576 := by
    simpa [prefixWord, tailWord_6681576, baseEnd_6681576] using wordTrace_append hprefix tailTrace_6681576
  have hstable : (prefixWord ++ tailWord_6681576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681576).length < 2 ^ (prefixWord ++ tailWord_6681576).sum := by decide
  have hdescent : baseEnd_6681576 < baseStart_6681576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681583 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 3]
def baseStart_6681583 : Nat := 118140960795 + 6681583 * 2 ^ 59
def prefixEnd_6681583 : Nat := 4983230072969 + 3 ^ 40 * 6681583 * 2
def baseEnd_6681583 : Nat := 3430863611910037009484465

theorem tailTrace_6681583 : CollatzResearch.WordTrace tailWord_6681583 prefixEnd_6681583 3430863611910037009484465 := by
  unfold tailWord_6681583
  simp only [CollatzResearch.WordTrace]
  refine ⟨243697352552773389372025403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162464901701848926248016935 243697352552773389372025403)
  ·
    refine ⟨365546028829160084058038105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243697352552773389372025403 365546028829160084058038105)
    ·
      refine ⟨274159521621870063043528579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365546028829160084058038105 274159521621870063043528579)
      ·
        refine ⟨411239282432805094565292869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274159521621870063043528579 411239282432805094565292869)
        ·
          refine ⟨77107365456150955230992413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 411239282432805094565292869 77107365456150955230992413)
          ·
            refine ⟨28915262046056608211622155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77107365456150955230992413 28915262046056608211622155)
            ·
              refine ⟨43372893069084912317433233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28915262046056608211622155 43372893069084912317433233)
              ·
                refine ⟨32529669801813684238074925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43372893069084912317433233 32529669801813684238074925)
                ·
                  refine ⟨12198626175680131589278097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32529669801813684238074925 12198626175680131589278097)
                  ·
                    refine ⟨9148969631760098691958573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12198626175680131589278097 9148969631760098691958573)
                    ·
                      refine ⟨3430863611910037009484465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9148969631760098691958573 3430863611910037009484465)
                      ·
                        rfl

theorem cell23_6681583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 3].length) (baseStart_6681583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681583 prefixEnd_6681583 := by exact prefixLift 6681583
  have htrace : WordTrace (prefixWord ++ tailWord_6681583) baseStart_6681583 baseEnd_6681583 := by
    simpa [prefixWord, tailWord_6681583, baseEnd_6681583] using wordTrace_append hprefix tailTrace_6681583
  have hstable : (prefixWord ++ tailWord_6681583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681583).length < 2 ^ (prefixWord ++ tailWord_6681583).sum := by decide
  have hdescent : baseEnd_6681583 < baseStart_6681583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681590 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_6681590 : Nat := 118140960795 + 6681590 * 2 ^ 59
def prefixEnd_6681590 : Nat := 4983230072969 + 3 ^ 40 * 6681590 * 2
def baseEnd_6681590 : Nat := 1143622402091539494032311

theorem tailTrace_6681590 : CollatzResearch.WordTrace tailWord_6681590 prefixEnd_6681590 1143622402091539494032311 := by
  unfold tailWord_6681590
  simp only [CollatzResearch.WordTrace]
  refine ⟨15231100491484251847970639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162465071909165353045020149 15231100491484251847970639)
  ·
    refine ⟨22846650737226377771955959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15231100491484251847970639 22846650737226377771955959)
    ·
      refine ⟨34269976105839566657933939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22846650737226377771955959 34269976105839566657933939)
      ·
        refine ⟨51404964158759349986900909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34269976105839566657933939 51404964158759349986900909)
        ·
          refine ⟨19276861559534756245087841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51404964158759349986900909 19276861559534756245087841)
          ·
            refine ⟨14457646169651067183815881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19276861559534756245087841 14457646169651067183815881)
            ·
              refine ⟨10843234627238300387861911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14457646169651067183815881 10843234627238300387861911)
              ·
                refine ⟨16264851940857450581792867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10843234627238300387861911 16264851940857450581792867)
                ·
                  refine ⟨24397277911286175872689301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16264851940857450581792867 24397277911286175872689301)
                  ·
                    refine ⟨1143622402091539494032311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24397277911286175872689301 1143622402091539494032311)
                    ·
                      rfl

theorem cell23_6681590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_6681590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681590 prefixEnd_6681590 := by exact prefixLift 6681590
  have htrace : WordTrace (prefixWord ++ tailWord_6681590) baseStart_6681590 baseEnd_6681590 := by
    simpa [prefixWord, tailWord_6681590, baseEnd_6681590] using wordTrace_append hprefix tailTrace_6681590
  have hstable : (prefixWord ++ tailWord_6681590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681590).length < 2 ^ (prefixWord ++ tailWord_6681590).sum := by decide
  have hdescent : baseEnd_6681590 < baseStart_6681590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681593 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 4]
def baseStart_6681593 : Nat := 118140960795 + 6681593 * 2 ^ 59
def prefixEnd_6681593 : Nat := 4983230072969 + 3 ^ 40 * 6681593 * 2
def baseEnd_6681593 : Nat := 3430868746716581970359419

theorem tailTrace_6681593 : CollatzResearch.WordTrace tailWord_6681593 prefixEnd_6681593 3430868746716581970359419 := by
  unfold tailWord_6681593
  simp only [CollatzResearch.WordTrace]
  refine ⟨243697717282737161079889433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162465144855158107386592955 243697717282737161079889433)
  ·
    refine ⟨182773287962052870809917075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243697717282737161079889433 182773287962052870809917075)
    ·
      refine ⟨274159931943079306214875613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182773287962052870809917075 274159931943079306214875613)
      ·
        refine ⟨102809974478654739830578355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274159931943079306214875613 102809974478654739830578355)
        ·
          refine ⟨154214961717982109745867533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102809974478654739830578355 154214961717982109745867533)
          ·
            refine ⟨57830610644243291154700325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154214961717982109745867533 57830610644243291154700325)
            ·
              refine ⟨10843239495795617091506311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57830610644243291154700325 10843239495795617091506311)
              ·
                refine ⟨16264859243693425637259467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10843239495795617091506311 16264859243693425637259467)
                ·
                  refine ⟨24397288865540138455889201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16264859243693425637259467 24397288865540138455889201)
                  ·
                    refine ⟨18297966649155103841916901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24397288865540138455889201 18297966649155103841916901)
                    ·
                      refine ⟨3430868746716581970359419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18297966649155103841916901 3430868746716581970359419)
                      ·
                        rfl

theorem cell23_6681593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_6681593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681593 prefixEnd_6681593 := by exact prefixLift 6681593
  have htrace : WordTrace (prefixWord ++ tailWord_6681593) baseStart_6681593 baseEnd_6681593 := by
    simpa [prefixWord, tailWord_6681593, baseEnd_6681593] using wordTrace_append hprefix tailTrace_6681593
  have hstable : (prefixWord ++ tailWord_6681593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681593).length < 2 ^ (prefixWord ++ tailWord_6681593).sum := by decide
  have hdescent : baseEnd_6681593 < baseStart_6681593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681614 : List Nat := [4, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2]
def baseStart_6681614 : Nat := 118140960795 + 6681614 * 2 ^ 59
def prefixEnd_6681614 : Nat := 4983230072969 + 3 ^ 40 * 6681614 * 2
def baseEnd_6681614 : Nat := 3430879529810326388196823

theorem tailTrace_6681614 : CollatzResearch.WordTrace tailWord_6681614 prefixEnd_6681614 3430879529810326388196823 := by
  unfold tailWord_6681614
  simp only [CollatzResearch.WordTrace]
  refine ⟨30462310401957635208300487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162465655477107387777602597 30462310401957635208300487)
  ·
    refine ⟨45693465602936452812450731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30462310401957635208300487 45693465602936452812450731)
    ·
      refine ⟨68540198404404679218676097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45693465602936452812450731 68540198404404679218676097)
      ·
        refine ⟨51405148803303509414007073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68540198404404679218676097 51405148803303509414007073)
        ·
          refine ⟨38553861602477632060505305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51405148803303509414007073 38553861602477632060505305)
          ·
            refine ⟨28915396201858224045378979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38553861602477632060505305 28915396201858224045378979)
            ·
              refine ⟨43373094302787336068068469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28915396201858224045378979 43373094302787336068068469)
              ·
                refine ⟨4066227590886312756381419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43373094302787336068068469 4066227590886312756381419)
                ·
                  refine ⟨6099341386329469134572129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4066227590886312756381419 6099341386329469134572129)
                  ·
                    refine ⟨4574506039747101850929097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6099341386329469134572129 4574506039747101850929097)
                    ·
                      refine ⟨3430879529810326388196823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574506039747101850929097 3430879529810326388196823)
                      ·
                        rfl

theorem cell23_6681614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_6681614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681614 prefixEnd_6681614 := by exact prefixLift 6681614
  have htrace : WordTrace (prefixWord ++ tailWord_6681614) baseStart_6681614 baseEnd_6681614 := by
    simpa [prefixWord, tailWord_6681614, baseEnd_6681614] using wordTrace_append hprefix tailTrace_6681614
  have hstable : (prefixWord ++ tailWord_6681614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681614).length < 2 ^ (prefixWord ++ tailWord_6681614).sum := by decide
  have hdescent : baseEnd_6681614 < baseStart_6681614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681657 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 1, 3, 2]
def baseStart_6681657 : Nat := 118140960795 + 6681657 * 2 ^ 59
def prefixEnd_6681657 : Nat := 4983230072969 + 3 ^ 40 * 6681657 * 2
def baseEnd_6681657 : Nat := 3430901609478469719959125

theorem tailTrace_6681657 : CollatzResearch.WordTrace tailWord_6681657 prefixEnd_6681657 3430901609478469719959125 := by
  unfold tailWord_6681657
  simp only [CollatzResearch.WordTrace]
  refine ⟨243700051554505300010219225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162466701036336866673479483 243700051554505300010219225)
  ·
    refine ⟨182775038665878975007664419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243700051554505300010219225 182775038665878975007664419)
    ·
      refine ⟨274162557998818462511496629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182775038665878975007664419 274162557998818462511496629)
      ·
        refine ⟨25702739812389230860452809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 274162557998818462511496629 25702739812389230860452809)
        ·
          refine ⟨19277054859291923145339607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25702739812389230860452809 19277054859291923145339607)
          ·
            refine ⟨28915582288937884718009411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19277054859291923145339607 28915582288937884718009411)
            ·
              refine ⟨43373373433406827077014117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28915582288937884718009411 43373373433406827077014117)
              ·
                refine ⟨8132507518763780076940147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43373373433406827077014117 8132507518763780076940147)
                ·
                  refine ⟨12198761278145670115410221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8132507518763780076940147 12198761278145670115410221)
                  ·
                    refine ⟨4574535479304626293278833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12198761278145670115410221 4574535479304626293278833)
                    ·
                      refine ⟨3430901609478469719959125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574535479304626293278833 3430901609478469719959125)
                      ·
                        rfl

theorem cell23_6681657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_6681657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681657 prefixEnd_6681657 := by exact prefixLift 6681657
  have htrace : WordTrace (prefixWord ++ tailWord_6681657) baseStart_6681657 baseEnd_6681657 := by
    simpa [prefixWord, tailWord_6681657, baseEnd_6681657] using wordTrace_append hprefix tailTrace_6681657
  have hstable : (prefixWord ++ tailWord_6681657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681657).length < 2 ^ (prefixWord ++ tailWord_6681657).sum := by decide
  have hdescent : baseEnd_6681657 < baseStart_6681657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681687 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 2, 2, 2]
def baseStart_6681687 : Nat := 118140960795 + 6681687 * 2 ^ 59
def prefixEnd_6681687 : Nat := 4983230072969 + 3 ^ 40 * 6681687 * 2
def baseEnd_6681687 : Nat := 3430917013898104602583987

theorem tailTrace_6681687 : CollatzResearch.WordTrace tailWord_6681687 prefixEnd_6681687 3430917013898104602583987 := by
  unfold tailWord_6681687
  simp only [CollatzResearch.WordTrace]
  refine ⟨243701145744396615133811315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162467430496264410089207543 243701145744396615133811315)
  ·
    refine ⟨365551718616594922700716973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243701145744396615133811315 365551718616594922700716973)
    ·
      refine ⟨137081894481223096012768865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365551718616594922700716973 137081894481223096012768865)
      ·
        refine ⟨102811420860917322009576649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137081894481223096012768865 102811420860917322009576649)
        ·
          refine ⟨77108565645687991507182487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102811420860917322009576649 77108565645687991507182487)
          ·
            refine ⟨115662848468531987260773731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77108565645687991507182487 115662848468531987260773731)
            ·
              refine ⟨173494272702797980891160597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115662848468531987260773731 173494272702797980891160597)
              ·
                refine ⟨8132544032943655354273153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173494272702797980891160597 8132544032943655354273153)
                ·
                  refine ⟨6099408024707741515704865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8132544032943655354273153 6099408024707741515704865)
                  ·
                    refine ⟨4574556018530806136778649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6099408024707741515704865 4574556018530806136778649)
                    ·
                      refine ⟨3430917013898104602583987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574556018530806136778649 3430917013898104602583987)
                      ·
                        rfl

theorem cell23_6681687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_6681687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681687 prefixEnd_6681687 := by exact prefixLift 6681687
  have htrace : WordTrace (prefixWord ++ tailWord_6681687) baseStart_6681687 baseEnd_6681687 := by
    simpa [prefixWord, tailWord_6681687, baseEnd_6681687] using wordTrace_append hprefix tailTrace_6681687
  have hstable : (prefixWord ++ tailWord_6681687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681687).length < 2 ^ (prefixWord ++ tailWord_6681687).sum := by decide
  have hdescent : baseEnd_6681687 < baseStart_6681687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681743 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 4]
def baseStart_6681743 : Nat := 118140960795 + 6681743 * 2 ^ 59
def prefixEnd_6681743 : Nat := 4983230072969 + 3 ^ 40 * 6681743 * 2
def baseEnd_6681743 : Nat := 3430945768814756383483729

theorem tailTrace_6681743 : CollatzResearch.WordTrace tailWord_6681743 prefixEnd_6681743 3430945768814756383483729 := by
  unfold tailWord_6681743
  simp only [CollatzResearch.WordTrace]
  refine ⟨243703188232193736697849883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162468792154795824465233255 243703188232193736697849883)
  ·
    refine ⟨365554782348290605046774825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243703188232193736697849883 365554782348290605046774825)
    ·
      refine ⟨274166086761217953785081119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365554782348290605046774825 274166086761217953785081119)
      ·
        refine ⟨411249130141826930677621679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274166086761217953785081119 411249130141826930677621679)
        ·
          refine ⟨616873695212740396016432519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411249130141826930677621679 616873695212740396016432519)
          ·
            refine ⟨925310542819110594024648779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616873695212740396016432519 925310542819110594024648779)
            ·
              refine ⟨1387965814228665891036973169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925310542819110594024648779 1387965814228665891036973169)
              ·
                refine ⟨1040974360671499418277729877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387965814228665891036973169 1040974360671499418277729877)
                ·
                  refine ⟨12198918289119133807942147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1040974360671499418277729877 12198918289119133807942147)
                  ·
                    refine ⟨18298377433678700711913221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12198918289119133807942147 18298377433678700711913221)
                    ·
                      refine ⟨3430945768814756383483729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18298377433678700711913221 3430945768814756383483729)
                      ·
                        rfl

theorem cell23_6681743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_6681743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681743 prefixEnd_6681743 := by exact prefixLift 6681743
  have htrace : WordTrace (prefixWord ++ tailWord_6681743) baseStart_6681743 baseEnd_6681743 := by
    simpa [prefixWord, tailWord_6681743, baseEnd_6681743] using wordTrace_append hprefix tailTrace_6681743
  have hstable : (prefixWord ++ tailWord_6681743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681743).length < 2 ^ (prefixWord ++ tailWord_6681743).sum := by decide
  have hdescent : baseEnd_6681743 < baseStart_6681743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681777 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 4]
def baseStart_6681777 : Nat := 118140960795 + 6681777 * 2 ^ 59
def prefixEnd_6681777 : Nat := 4983230072969 + 3 ^ 40 * 6681777 * 2
def baseEnd_6681777 : Nat := 3430963227157009250458573

theorem tailTrace_6681777 : CollatzResearch.WordTrace tailWord_6681777 prefixEnd_6681777 3430963227157009250458573 := by
  unfold tailWord_6681777
  simp only [CollatzResearch.WordTrace]
  refine ⟨243704428314070560504587585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162469618876047040336391723 243704428314070560504587585)
  ·
    refine ⟨182778321235552920378440689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243704428314070560504587585 182778321235552920378440689)
    ·
      refine ⟨137083740926664690283830517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182778321235552920378440689 137083740926664690283830517)
      ·
        refine ⟨12851600711874814714109111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137083740926664690283830517 12851600711874814714109111)
        ·
          refine ⟨19277401067812222071163667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12851600711874814714109111 19277401067812222071163667)
          ·
            refine ⟨28916101601718333106745501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19277401067812222071163667 28916101601718333106745501)
            ·
              refine ⟨10843538100644374915029563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28916101601718333106745501 10843538100644374915029563)
              ·
                refine ⟨16265307150966562372544345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10843538100644374915029563 16265307150966562372544345)
                ·
                  refine ⟨12198980363224921779408259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16265307150966562372544345 12198980363224921779408259)
                  ·
                    refine ⟨18298470544837382669112389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12198980363224921779408259 18298470544837382669112389)
                    ·
                      refine ⟨3430963227157009250458573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18298470544837382669112389 3430963227157009250458573)
                      ·
                        rfl

theorem cell23_6681777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_6681777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681777 prefixEnd_6681777 := by exact prefixLift 6681777
  have htrace : WordTrace (prefixWord ++ tailWord_6681777) baseStart_6681777 baseEnd_6681777 := by
    simpa [prefixWord, tailWord_6681777, baseEnd_6681777] using wordTrace_append hprefix tailTrace_6681777
  have hstable : (prefixWord ++ tailWord_6681777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681777).length < 2 ^ (prefixWord ++ tailWord_6681777).sum := by decide
  have hdescent : baseEnd_6681777 < baseStart_6681777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681783 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 8]
def baseStart_6681783 : Nat := 118140960795 + 6681783 * 2 ^ 59
def prefixEnd_6681783 : Nat := 4983230072969 + 3 ^ 40 * 6681783 * 2
def baseEnd_6681783 : Nat := 381218478671215136331505

theorem tailTrace_6681783 : CollatzResearch.WordTrace tailWord_6681783 prefixEnd_6681783 381218478671215136331505 := by
  unfold tailWord_6681783
  simp only [CollatzResearch.WordTrace]
  refine ⟨243704647152048823529306003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162469764768032549019537335 243704647152048823529306003)
  ·
    refine ⟨365556970728073235293959005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243704647152048823529306003 365556970728073235293959005)
    ·
      refine ⟨137083864023027463235234627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365556970728073235293959005 137083864023027463235234627)
      ·
        refine ⟨205625796034541194852851941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137083864023027463235234627 205625796034541194852851941)
        ·
          refine ⟨38554836756476474034909739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205625796034541194852851941 38554836756476474034909739)
          ·
            refine ⟨57832255134714711052364609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38554836756476474034909739 57832255134714711052364609)
            ·
              refine ⟨43374191351036033289273457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57832255134714711052364609 43374191351036033289273457)
              ·
                refine ⟨32530643513277024966955093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43374191351036033289273457 32530643513277024966955093)
                ·
                  refine ⟨381218478671215136331505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32530643513277024966955093 381218478671215136331505)
                  ·
                    rfl

theorem cell23_6681783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 8].length) (baseStart_6681783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681783 prefixEnd_6681783 := by exact prefixLift 6681783
  have htrace : WordTrace (prefixWord ++ tailWord_6681783) baseStart_6681783 baseEnd_6681783 := by
    simpa [prefixWord, tailWord_6681783, baseEnd_6681783] using wordTrace_append hprefix tailTrace_6681783
  have hstable : (prefixWord ++ tailWord_6681783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681783).length < 2 ^ (prefixWord ++ tailWord_6681783).sum := by decide
  have hdescent : baseEnd_6681783 < baseStart_6681783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681790 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_6681790 : Nat := 118140960795 + 6681790 * 2 ^ 59
def prefixEnd_6681790 : Nat := 4983230072969 + 3 ^ 40 * 6681790 * 2
def baseEnd_6681790 : Nat := 3430969902405517699596013

theorem tailTrace_6681790 : CollatzResearch.WordTrace tailWord_6681790 prefixEnd_6681790 3430969902405517699596013 := by
  unfold tailWord_6681790
  simp only [CollatzResearch.WordTrace]
  refine ⟨30463112807877932965601353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162469934975348975816540549 30463112807877932965601353)
  ·
    refine ⟨22847334605908449724201015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30463112807877932965601353 22847334605908449724201015)
    ·
      refine ⟨34271001908862674586301523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22847334605908449724201015 34271001908862674586301523)
      ·
        refine ⟨51406502863294011879452285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34271001908862674586301523 51406502863294011879452285)
        ·
          refine ⟨19277438573735254454794607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51406502863294011879452285 19277438573735254454794607)
          ·
            refine ⟨28916157860602881682191911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19277438573735254454794607 28916157860602881682191911)
            ·
              refine ⟨43374236790904322523287867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28916157860602881682191911 43374236790904322523287867)
              ·
                refine ⟨65061355186356483784931801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43374236790904322523287867 65061355186356483784931801)
                ·
                  refine ⟨48796016389767362838698851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65061355186356483784931801 48796016389767362838698851)
                  ·
                    refine ⟨73194024584651044258048277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48796016389767362838698851 73194024584651044258048277)
                    ·
                      refine ⟨3430969902405517699596013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73194024584651044258048277 3430969902405517699596013)
                      ·
                        rfl

theorem cell23_6681790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_6681790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681790 prefixEnd_6681790 := by exact prefixLift 6681790
  have htrace : WordTrace (prefixWord ++ tailWord_6681790) baseStart_6681790 baseEnd_6681790 := by
    simpa [prefixWord, tailWord_6681790, baseEnd_6681790] using wordTrace_append hprefix tailTrace_6681790
  have hstable : (prefixWord ++ tailWord_6681790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681790).length < 2 ^ (prefixWord ++ tailWord_6681790).sum := by decide
  have hdescent : baseEnd_6681790 < baseStart_6681790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681800 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 6]
def baseStart_6681800 : Nat := 118140960795 + 6681800 * 2 ^ 59
def prefixEnd_6681800 : Nat := 4983230072969 + 3 ^ 40 * 6681800 * 2
def baseEnd_6681800 : Nat := 381219448579118073385663

theorem tailTrace_6681800 : CollatzResearch.WordTrace tailWord_6681800 prefixEnd_6681800 381219448579118073385663 := by
  unfold tailWord_6681800
  simp only [CollatzResearch.WordTrace]
  refine ⟨121852633596493617716337427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162470178128658156955116569 121852633596493617716337427)
  ·
    refine ⟨182778950394740426574506141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121852633596493617716337427 182778950394740426574506141)
    ·
      refine ⟨68542106398027659965439803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182778950394740426574506141 68542106398027659965439803)
      ·
        refine ⟨102813159597041489948159705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68542106398027659965439803 102813159597041489948159705)
        ·
          refine ⟨77109869697781117461119779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102813159597041489948159705 77109869697781117461119779)
          ·
            refine ⟨115664804546671676191679669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77109869697781117461119779 115664804546671676191679669)
            ·
              refine ⟨10843575426250469642969969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115664804546671676191679669 10843575426250469642969969)
              ·
                refine ⟨8132681569687852232227477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10843575426250469642969969 8132681569687852232227477)
                ·
                  refine ⟨381219448579118073385663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8132681569687852232227477 381219448579118073385663)
                  ·
                    rfl

theorem cell23_6681800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 6].length) (baseStart_6681800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681800 prefixEnd_6681800 := by exact prefixLift 6681800
  have htrace : WordTrace (prefixWord ++ tailWord_6681800) baseStart_6681800 baseEnd_6681800 := by
    simpa [prefixWord, tailWord_6681800, baseEnd_6681800] using wordTrace_append hprefix tailTrace_6681800
  have hstable : (prefixWord ++ tailWord_6681800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681800).length < 2 ^ (prefixWord ++ tailWord_6681800).sum := by decide
  have hdescent : baseEnd_6681800 < baseStart_6681800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681823 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_6681823 : Nat := 118140960795 + 6681823 * 2 ^ 59
def prefixEnd_6681823 : Nat := 4983230072969 + 3 ^ 40 * 6681823 * 2
def baseEnd_6681823 : Nat := 3430986847267116070483361

theorem tailTrace_6681823 : CollatzResearch.WordTrace tailWord_6681823 prefixEnd_6681823 3430986847267116070483361 := by
  unfold tailWord_6681823
  simp only [CollatzResearch.WordTrace]
  refine ⟨243706106071903910360762123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162470737381269273573841415 243706106071903910360762123)
  ·
    refine ⟨365559159107855865541143185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243706106071903910360762123 365559159107855865541143185)
    ·
      refine ⟨274169369330891899155857389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365559159107855865541143185 274169369330891899155857389)
      ·
        refine ⟨102813513499084462183446521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274169369330891899155857389 102813513499084462183446521)
        ·
          refine ⟨77110135124313346637584891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102813513499084462183446521 77110135124313346637584891)
          ·
            refine ⟨115665202686470019956377337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77110135124313346637584891 115665202686470019956377337)
            ·
              refine ⟨86748902014852514967283003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115665202686470019956377337 86748902014852514967283003)
              ·
                refine ⟨130123353022278772450924505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86748902014852514967283003 130123353022278772450924505)
                ·
                  refine ⟨97592514766709079338193379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130123353022278772450924505 97592514766709079338193379)
                  ·
                    refine ⟨146388772150063619007290069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97592514766709079338193379 146388772150063619007290069)
                    ·
                      refine ⟨3430986847267116070483361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146388772150063619007290069 3430986847267116070483361)
                      ·
                        rfl

theorem cell23_6681823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_6681823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681823 prefixEnd_6681823 := by exact prefixLift 6681823
  have htrace : WordTrace (prefixWord ++ tailWord_6681823) baseStart_6681823 baseEnd_6681823 := by
    simpa [prefixWord, tailWord_6681823, baseEnd_6681823] using wordTrace_append hprefix tailTrace_6681823
  have hstable : (prefixWord ++ tailWord_6681823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681823).length < 2 ^ (prefixWord ++ tailWord_6681823).sum := by decide
  have hdescent : baseEnd_6681823 < baseStart_6681823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681854 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_6681854 : Nat := 118140960795 + 6681854 * 2 ^ 59
def prefixEnd_6681854 : Nat := 4983230072969 + 3 ^ 40 * 6681854 * 2
def baseEnd_6681854 : Nat := 3431002765167405449195719

theorem tailTrace_6681854 : CollatzResearch.WordTrace tailWord_6681854 prefixEnd_6681854 3431002765167405449195719 := by
  unfold tailWord_6681854
  simp only [CollatzResearch.WordTrace]
  refine ⟨30463404591848950331892577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162471491156527735103427077 30463404591848950331892577)
  ·
    refine ⟨22847553443886712748919433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30463404591848950331892577 22847553443886712748919433)
    ·
      refine ⟨17135665082915034561689575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22847553443886712748919433 17135665082915034561689575)
      ·
        refine ⟨25703497624372551842534363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17135665082915034561689575 25703497624372551842534363)
        ·
          refine ⟨38555246436558827763801545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25703497624372551842534363 38555246436558827763801545)
          ·
            refine ⟨28916434827419120822851159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38555246436558827763801545 28916434827419120822851159)
            ·
              refine ⟨43374652241128681234276739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28916434827419120822851159 43374652241128681234276739)
              ·
                refine ⟨65061978361693021851415109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43374652241128681234276739 65061978361693021851415109)
                ·
                  refine ⟨12199120942817441597140333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65061978361693021851415109 12199120942817441597140333)
                  ·
                    refine ⟨4574670353556540598927625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12199120942817441597140333 4574670353556540598927625)
                    ·
                      refine ⟨3431002765167405449195719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574670353556540598927625 3431002765167405449195719)
                      ·
                        rfl

theorem cell23_6681854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_6681854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681854 prefixEnd_6681854 := by exact prefixLift 6681854
  have htrace : WordTrace (prefixWord ++ tailWord_6681854) baseStart_6681854 baseEnd_6681854 := by
    simpa [prefixWord, tailWord_6681854, baseEnd_6681854] using wordTrace_append hprefix tailTrace_6681854
  have hstable : (prefixWord ++ tailWord_6681854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681854).length < 2 ^ (prefixWord ++ tailWord_6681854).sum := by decide
  have hdescent : baseEnd_6681854 < baseStart_6681854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681861 : List Nat := [1, 3, 1, 1, 2, 1, 7, 2, 1, 1, 3]
def baseStart_6681861 : Nat := 118140960795 + 6681861 * 2 ^ 59
def prefixEnd_6681861 : Nat := 4983230072969 + 3 ^ 40 * 6681861 * 2
def baseEnd_6681861 : Nat := 3431006359531986921808187

theorem tailTrace_6681861 : CollatzResearch.WordTrace tailWord_6681861 prefixEnd_6681861 3431006359531986921808187 := by
  unfold tailWord_6681861
  simp only [CollatzResearch.WordTrace]
  refine ⟨243707492045766242850645437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162471661363844161900430291 243707492045766242850645437)
  ·
    refine ⟨91390309517162341068992039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243707492045766242850645437 91390309517162341068992039)
    ·
      refine ⟨137085464275743511603488059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91390309517162341068992039 137085464275743511603488059)
      ·
        refine ⟨205628196413615267405232089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137085464275743511603488059 205628196413615267405232089)
        ·
          refine ⟨154221147310211450553924067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205628196413615267405232089 154221147310211450553924067)
          ·
            refine ⟨231331720965317175830886101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154221147310211450553924067 231331720965317175830886101)
            ·
              refine ⟨5421837210124621308536393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 231331720965317175830886101 5421837210124621308536393)
              ·
                refine ⟨4066377907593465981402295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5421837210124621308536393 4066377907593465981402295)
                ·
                  refine ⟨6099566861390198972103443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4066377907593465981402295 6099566861390198972103443)
                  ·
                    refine ⟨9149350292085298458155165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6099566861390198972103443 9149350292085298458155165)
                    ·
                      refine ⟨3431006359531986921808187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9149350292085298458155165 3431006359531986921808187)
                      ·
                        rfl

theorem cell23_6681861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 1, 1, 3].length) (baseStart_6681861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681861 prefixEnd_6681861 := by exact prefixLift 6681861
  have htrace : WordTrace (prefixWord ++ tailWord_6681861) baseStart_6681861 baseEnd_6681861 := by
    simpa [prefixWord, tailWord_6681861, baseEnd_6681861] using wordTrace_append hprefix tailTrace_6681861
  have hstable : (prefixWord ++ tailWord_6681861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681861).length < 2 ^ (prefixWord ++ tailWord_6681861).sum := by decide
  have hdescent : baseEnd_6681861 < baseStart_6681861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681880 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_6681880 : Nat := 118140960795 + 6681880 * 2 ^ 59
def prefixEnd_6681880 : Nat := 4983230072969 + 3 ^ 40 * 6681880 * 2
def baseEnd_6681880 : Nat := 3431016115664422347470599

theorem tailTrace_6681880 : CollatzResearch.WordTrace tailWord_6681880 prefixEnd_6681880 3431016115664422347470599 := by
  unfold tailWord_6681880
  simp only [CollatzResearch.WordTrace]
  refine ⟨121854092516348704547793547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162472123355131606063724729 121854092516348704547793547)
  ·
    refine ⟨182781138774523056821690321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121854092516348704547793547 182781138774523056821690321)
    ·
      refine ⟨137085854080892292616267741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182781138774523056821690321 137085854080892292616267741)
      ·
        refine ⟨51407195280334609731100403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137085854080892292616267741 51407195280334609731100403)
        ·
          refine ⟨77110792920501914596650605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51407195280334609731100403 77110792920501914596650605)
          ·
            refine ⟨28916547345188217973743977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77110792920501914596650605 28916547345188217973743977)
            ·
              refine ⟨21687410508891163480307983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28916547345188217973743977 21687410508891163480307983)
              ·
                refine ⟨32531115763336745220461975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21687410508891163480307983 32531115763336745220461975)
                ·
                  refine ⟨48796673645005117830692963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32531115763336745220461975 48796673645005117830692963)
                  ·
                    refine ⟨73195010467507676746039445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48796673645005117830692963 73195010467507676746039445)
                    ·
                      refine ⟨3431016115664422347470599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73195010467507676746039445 3431016115664422347470599)
                      ·
                        rfl

theorem cell23_6681880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_6681880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681880 prefixEnd_6681880 := by exact prefixLift 6681880
  have htrace : WordTrace (prefixWord ++ tailWord_6681880) baseStart_6681880 baseEnd_6681880 := by
    simpa [prefixWord, tailWord_6681880, baseEnd_6681880] using wordTrace_append hprefix tailTrace_6681880
  have hstable : (prefixWord ++ tailWord_6681880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681880).length < 2 ^ (prefixWord ++ tailWord_6681880).sum := by decide
  have hdescent : baseEnd_6681880 < baseStart_6681880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681884 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_6681884 : Nat := 118140960795 + 6681884 * 2 ^ 59
def prefixEnd_6681884 : Nat := 4983230072969 + 3 ^ 40 * 6681884 * 2
def baseEnd_6681884 : Nat := 3431018169587040331820581

theorem tailTrace_6681884 : CollatzResearch.WordTrace tailWord_6681884 prefixEnd_6681884 3431018169587040331820581 := by
  unfold tailWord_6681884
  simp only [CollatzResearch.WordTrace]
  refine ⟨121854165462341458889366353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162472220616455278519155137 121854165462341458889366353)
  ·
    refine ⟨91390624096756094167024765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121854165462341458889366353 91390624096756094167024765)
    ·
      refine ⟨34271484036283535312634287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91390624096756094167024765 34271484036283535312634287)
      ·
        refine ⟨51407226054425302968951431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34271484036283535312634287 51407226054425302968951431)
        ·
          refine ⟨77110839081637954453427147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51407226054425302968951431 77110839081637954453427147)
          ·
            refine ⟨115666258622456931680140721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77110839081637954453427147 115666258622456931680140721)
            ·
              refine ⟨86749693966842698760105541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115666258622456931680140721 86749693966842698760105541)
              ·
                refine ⟨16265567618783006017519789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86749693966842698760105541 16265567618783006017519789)
                ·
                  refine ⟨6099587857043627256569921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16265567618783006017519789 6099587857043627256569921)
                  ·
                    refine ⟨4574690892782720442427441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6099587857043627256569921 4574690892782720442427441)
                    ·
                      refine ⟨3431018169587040331820581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574690892782720442427441 3431018169587040331820581)
                      ·
                        rfl

theorem cell23_6681884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_6681884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681884 prefixEnd_6681884 := by exact prefixLift 6681884
  have htrace : WordTrace (prefixWord ++ tailWord_6681884) baseStart_6681884 baseEnd_6681884 := by
    simpa [prefixWord, tailWord_6681884, baseEnd_6681884] using wordTrace_append hprefix tailTrace_6681884
  have hstable : (prefixWord ++ tailWord_6681884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681884).length < 2 ^ (prefixWord ++ tailWord_6681884).sum := by decide
  have hdescent : baseEnd_6681884 < baseStart_6681884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681904 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 1, 2, 3]
def baseStart_6681904 : Nat := 118140960795 + 6681904 * 2 ^ 59
def prefixEnd_6681904 : Nat := 4983230072969 + 3 ^ 40 * 6681904 * 2
def baseEnd_6681904 : Nat := 3431028439200130253570489

theorem tailTrace_6681904 : CollatzResearch.WordTrace tailWord_6681904 prefixEnd_6681904 3431028439200130253570489 := by
  unfold tailWord_6681904
  simp only [CollatzResearch.WordTrace]
  refine ⟨121854530192305230597230383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162472706923073640796307177 121854530192305230597230383)
  ·
    refine ⟨182781795288457845895845575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121854530192305230597230383 182781795288457845895845575)
    ·
      refine ⟨274172692932686768843768363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182781795288457845895845575 274172692932686768843768363)
      ·
        refine ⟨411259039399030153265652545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274172692932686768843768363 411259039399030153265652545)
        ·
          refine ⟨308444279549272614949239409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411259039399030153265652545 308444279549272614949239409)
          ·
            refine ⟨231333209661954461211929557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308444279549272614949239409 231333209661954461211929557)
            ·
              refine ⟨5421872101452057684654599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 231333209661954461211929557 5421872101452057684654599)
              ·
                refine ⟨8132808152178086526981899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5421872101452057684654599 8132808152178086526981899)
                ·
                  refine ⟨12199212228267129790472849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8132808152178086526981899 12199212228267129790472849)
                  ·
                    refine ⟨9149409171200347342854637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12199212228267129790472849 9149409171200347342854637)
                    ·
                      refine ⟨3431028439200130253570489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9149409171200347342854637 3431028439200130253570489)
                      ·
                        rfl

theorem cell23_6681904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 2, 3].length) (baseStart_6681904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681904 prefixEnd_6681904 := by exact prefixLift 6681904
  have htrace : WordTrace (prefixWord ++ tailWord_6681904) baseStart_6681904 baseEnd_6681904 := by
    simpa [prefixWord, tailWord_6681904, baseEnd_6681904] using wordTrace_append hprefix tailTrace_6681904
  have hstable : (prefixWord ++ tailWord_6681904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681904).length < 2 ^ (prefixWord ++ tailWord_6681904).sum := by decide
  have hdescent : baseEnd_6681904 < baseStart_6681904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681918 : List Nat := [4, 2, 1, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_6681918 : Nat := 118140960795 + 6681918 * 2 ^ 59
def prefixEnd_6681918 : Nat := 4983230072969 + 3 ^ 40 * 6681918 * 2
def baseEnd_6681918 : Nat := 3431035627929293198795425

theorem tailTrace_6681918 : CollatzResearch.WordTrace tailWord_6681918 prefixEnd_6681918 3431035627929293198795425 := by
  unfold tailWord_6681918
  simp only [CollatzResearch.WordTrace]
  refine ⟨30463696375819967698183801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162473047337706494390313605 30463696375819967698183801)
  ·
    refine ⟨22847772281864975773637851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30463696375819967698183801 22847772281864975773637851)
    ·
      refine ⟨34271658422797463660456777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22847772281864975773637851 34271658422797463660456777)
      ·
        refine ⟨25703743817098097745342583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34271658422797463660456777 25703743817098097745342583)
        ·
          refine ⟨38555615725647146618013875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25703743817098097745342583 38555615725647146618013875)
          ·
            refine ⟨57833423588470719927020813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38555615725647146618013875 57833423588470719927020813)
            ·
              refine ⟨21687533845676519972632805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57833423588470719927020813 21687533845676519972632805)
              ·
                refine ⟨4066412596064347494868651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21687533845676519972632805 4066412596064347494868651)
                ·
                  refine ⟨6099618894096521242302977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4066412596064347494868651 6099618894096521242302977)
                  ·
                    refine ⟨4574714170572390931727233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6099618894096521242302977 4574714170572390931727233)
                    ·
                      refine ⟨3431035627929293198795425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574714170572390931727233 3431035627929293198795425)
                      ·
                        rfl

theorem cell23_6681918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_6681918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681918 prefixEnd_6681918 := by exact prefixLift 6681918
  have htrace : WordTrace (prefixWord ++ tailWord_6681918) baseStart_6681918 baseEnd_6681918 := by
    simpa [prefixWord, tailWord_6681918, baseEnd_6681918] using wordTrace_append hprefix tailTrace_6681918
  have hstable : (prefixWord ++ tailWord_6681918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681918).length < 2 ^ (prefixWord ++ tailWord_6681918).sum := by decide
  have hdescent : baseEnd_6681918 < baseStart_6681918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681924 : List Nat := [2, 3, 4, 1, 1, 3, 1, 8]
def baseStart_6681924 : Nat := 118140960795 + 6681924 * 2 ^ 59
def prefixEnd_6681924 : Nat := 4983230072969 + 3 ^ 40 * 6681924 * 2
def baseEnd_6681924 : Nat := 127075507733822969456311

theorem tailTrace_6681924 : CollatzResearch.WordTrace tailWord_6681924 prefixEnd_6681924 127075507733822969456311 := by
  unfold tailWord_6681924
  simp only [CollatzResearch.WordTrace]
  refine ⟨121854894922269002305094413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162473193229692003073459217 121854894922269002305094413)
  ·
    refine ⟨45695585595850875864410405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121854894922269002305094413 45695585595850875864410405)
    ·
      refine ⟨8567922299222039224576951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45695585595850875864410405 8567922299222039224576951)
      ·
        refine ⟨12851883448833058836865427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8567922299222039224576951 12851883448833058836865427)
        ·
          refine ⟨19277825173249588255298141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12851883448833058836865427 19277825173249588255298141)
          ·
            refine ⟨7229184439968595595736803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19277825173249588255298141 7229184439968595595736803)
            ·
              refine ⟨10843776659952893393605205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7229184439968595595736803 10843776659952893393605205)
              ·
                refine ⟨127075507733822969456311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10843776659952893393605205 127075507733822969456311)
                ·
                  rfl

theorem cell23_6681924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 8].length) (baseStart_6681924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681924 prefixEnd_6681924 := by exact prefixLift 6681924
  have htrace : WordTrace (prefixWord ++ tailWord_6681924) baseStart_6681924 baseEnd_6681924 := by
    simpa [prefixWord, tailWord_6681924, baseEnd_6681924] using wordTrace_append hprefix tailTrace_6681924
  have hstable : (prefixWord ++ tailWord_6681924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681924).length < 2 ^ (prefixWord ++ tailWord_6681924).sum := by decide
  have hdescent : baseEnd_6681924 < baseStart_6681924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681934 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_6681934 : Nat := 118140960795 + 6681934 * 2 ^ 59
def prefixEnd_6681934 : Nat := 4983230072969 + 3 ^ 40 * 6681934 * 2
def baseEnd_6681934 : Nat := 3431043843619765136195351

theorem tailTrace_6681934 : CollatzResearch.WordTrace tailWord_6681934 prefixEnd_6681934 3431043843619765136195351 := by
  unfold tailWord_6681934
  simp only [CollatzResearch.WordTrace]
  refine ⟨30463769321812722039756607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162473436383001184212035237 30463769321812722039756607)
  ·
    refine ⟨45695653982719083059634911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30463769321812722039756607 45695653982719083059634911)
    ·
      refine ⟨68543480974078624589452367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45695653982719083059634911 68543480974078624589452367)
      ·
        refine ⟨102815221461117936884178551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68543480974078624589452367 102815221461117936884178551)
        ·
          refine ⟨154222832191676905326267827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102815221461117936884178551 154222832191676905326267827)
          ·
            refine ⟨231334248287515357989401741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154222832191676905326267827 231334248287515357989401741)
            ·
              refine ⟨86750343107818259246025653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231334248287515357989401741 86750343107818259246025653)
              ·
                refine ⟨8132844666357961804314905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86750343107818259246025653 8132844666357961804314905)
                ·
                  refine ⟨6099633499768471353236179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8132844666357961804314905 6099633499768471353236179)
                  ·
                    refine ⟨9149450249652707029854269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6099633499768471353236179 9149450249652707029854269)
                    ·
                      refine ⟨3431043843619765136195351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9149450249652707029854269 3431043843619765136195351)
                      ·
                        rfl

theorem cell23_6681934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_6681934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681934 prefixEnd_6681934 := by exact prefixLift 6681934
  have htrace : WordTrace (prefixWord ++ tailWord_6681934) baseStart_6681934 baseEnd_6681934 := by
    simpa [prefixWord, tailWord_6681934, baseEnd_6681934] using wordTrace_append hprefix tailTrace_6681934
  have hstable : (prefixWord ++ tailWord_6681934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681934).length < 2 ^ (prefixWord ++ tailWord_6681934).sum := by decide
  have hdescent : baseEnd_6681934 < baseStart_6681934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681944 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 1, 3, 2]
def baseStart_6681944 : Nat := 118140960795 + 6681944 * 2 ^ 59
def prefixEnd_6681944 : Nat := 4983230072969 + 3 ^ 40 * 6681944 * 2
def baseEnd_6681944 : Nat := 3431048978426310097070305

theorem tailTrace_6681944 : CollatzResearch.WordTrace tailWord_6681944 prefixEnd_6681944 3431048978426310097070305 := by
  unfold tailWord_6681944
  simp only [CollatzResearch.WordTrace]
  refine ⟨121855259652232774012958443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162473679536310365350611257 121855259652232774012958443)
  ·
    refine ⟨182782889478349161019437665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121855259652232774012958443 182782889478349161019437665)
    ·
      refine ⟨137087167108761870764578249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182782889478349161019437665 137087167108761870764578249)
      ·
        refine ⟨102815375331571403073433687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137087167108761870764578249 102815375331571403073433687)
        ·
          refine ⟨154223062997357104610150531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102815375331571403073433687 154223062997357104610150531)
          ·
            refine ⟨231334594496035656915225797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154223062997357104610150531 231334594496035656915225797)
            ·
              refine ⟨43375236468006685671604837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231334594496035656915225797 43375236468006685671604837)
              ·
                refine ⟨8132856837751253563425907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43375236468006685671604837 8132856837751253563425907)
                ·
                  refine ⟨12199285256626880345138861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8132856837751253563425907 12199285256626880345138861)
                  ·
                    refine ⟨4574731971235080129427073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12199285256626880345138861 4574731971235080129427073)
                    ·
                      refine ⟨3431048978426310097070305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574731971235080129427073 3431048978426310097070305)
                      ·
                        rfl

theorem cell23_6681944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_6681944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681944 prefixEnd_6681944 := by exact prefixLift 6681944
  have htrace : WordTrace (prefixWord ++ tailWord_6681944) baseStart_6681944 baseEnd_6681944 := by
    simpa [prefixWord, tailWord_6681944, baseEnd_6681944] using wordTrace_append hprefix tailTrace_6681944
  have hstable : (prefixWord ++ tailWord_6681944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681944).length < 2 ^ (prefixWord ++ tailWord_6681944).sum := by decide
  have hdescent : baseEnd_6681944 < baseStart_6681944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681987 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 4]
def baseStart_6681987 : Nat := 118140960795 + 6681987 * 2 ^ 59
def prefixEnd_6681987 : Nat := 4983230072969 + 3 ^ 40 * 6681987 * 2
def baseEnd_6681987 : Nat := 3431071058094453428832607

theorem tailTrace_6681987 : CollatzResearch.WordTrace tailWord_6681987 prefixEnd_6681987 3431071058094453428832607 := by
  unfold tailWord_6681987
  simp only [CollatzResearch.WordTrace]
  refine ⟨243712087643309766369732215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162474725095539844246488143 243712087643309766369732215)
  ·
    refine ⟨365568131464964649554598323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243712087643309766369732215 365568131464964649554598323)
    ·
      refine ⟨548352197197446974331897485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365568131464964649554598323 548352197197446974331897485)
      ·
        refine ⟨205632073949042615374461557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548352197197446974331897485 205632073949042615374461557)
        ·
          refine ⟨19278006932722745191355771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205632073949042615374461557 19278006932722745191355771)
          ·
            refine ⟨28917010399084117787033657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19278006932722745191355771 28917010399084117787033657)
            ·
              refine ⟨21687757799313088340275243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28917010399084117787033657 21687757799313088340275243)
              ·
                refine ⟨32531636698969632510412865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21687757799313088340275243 32531636698969632510412865)
                ·
                  refine ⟨24398727524227224382809649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32531636698969632510412865 24398727524227224382809649)
                  ·
                    refine ⟨18299045643170418287107237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24398727524227224382809649 18299045643170418287107237)
                    ·
                      refine ⟨3431071058094453428832607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18299045643170418287107237 3431071058094453428832607)
                      ·
                        rfl

theorem cell23_6681987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_6681987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681987 prefixEnd_6681987 := by exact prefixLift 6681987
  have htrace : WordTrace (prefixWord ++ tailWord_6681987) baseStart_6681987 baseEnd_6681987 := by
    simpa [prefixWord, tailWord_6681987, baseEnd_6681987] using wordTrace_append hprefix tailTrace_6681987
  have hstable : (prefixWord ++ tailWord_6681987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681987).length < 2 ^ (prefixWord ++ tailWord_6681987).sum := by decide
  have hdescent : baseEnd_6681987 < baseStart_6681987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681991 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 1, 4, 2]
def baseStart_6681991 : Nat := 118140960795 + 6681991 * 2 ^ 59
def prefixEnd_6681991 : Nat := 4983230072969 + 3 ^ 40 * 6681991 * 2
def baseEnd_6681991 : Nat := 3431073112017071413182589

theorem tailTrace_6681991 : CollatzResearch.WordTrace tailWord_6681991 prefixEnd_6681991 3431073112017071413182589 := by
  unfold tailWord_6681991
  simp only [CollatzResearch.WordTrace]
  refine ⟨243712233535295275052877827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162474822356863516701918551 243712233535295275052877827)
  ·
    refine ⟨365568350302942912579316741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243712233535295275052877827 365568350302942912579316741)
    ·
      refine ⟨68544065681801796108621889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365568350302942912579316741 68544065681801796108621889)
      ·
        refine ⟨51408049261351347081466417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68544065681801796108621889 51408049261351347081466417)
        ·
          refine ⟨38556036946013510311099813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51408049261351347081466417 38556036946013510311099813)
          ·
            refine ⟨7229256927377533183331215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38556036946013510311099813 7229256927377533183331215)
            ·
              refine ⟨10843885391066299774996823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7229256927377533183331215 10843885391066299774996823)
              ·
                refine ⟨16265828086599449662495235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10843885391066299774996823 16265828086599449662495235)
                ·
                  refine ⟨24398742129899174493742853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16265828086599449662495235 24398742129899174493742853)
                  ·
                    refine ⟨4574764149356095217576785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24398742129899174493742853 4574764149356095217576785)
                    ·
                      refine ⟨3431073112017071413182589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574764149356095217576785 3431073112017071413182589)
                      ·
                        rfl

theorem cell23_6681991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_6681991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681991 prefixEnd_6681991 := by exact prefixLift 6681991
  have htrace : WordTrace (prefixWord ++ tailWord_6681991) baseStart_6681991 baseEnd_6681991 := by
    simpa [prefixWord, tailWord_6681991, baseEnd_6681991] using wordTrace_append hprefix tailTrace_6681991
  have hstable : (prefixWord ++ tailWord_6681991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681991).length < 2 ^ (prefixWord ++ tailWord_6681991).sum := by decide
  have hdescent : baseEnd_6681991 < baseStart_6681991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682037 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_6682037 : Nat := 118140960795 + 6682037 * 2 ^ 59
def prefixEnd_6682037 : Nat := 4983230072969 + 3 ^ 40 * 6682037 * 2
def baseEnd_6682037 : Nat := 3431096732127178233207377

theorem tailTrace_6682037 : CollatzResearch.WordTrace tailWord_6682037 prefixEnd_6682037 3431096732127178233207377 := by
  unfold tailWord_6682037
  simp only [CollatzResearch.WordTrace]
  refine ⟨243713911293128624909052365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162475940862085749939368243 243713911293128624909052365)
  ·
    refine ⟨91392716734923234340894637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243713911293128624909052365 91392716734923234340894637)
    ·
      refine ⟨34272268775596212877835489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91392716734923234340894637 34272268775596212877835489)
      ·
        refine ⟨25704201581697159658376617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34272268775596212877835489 25704201581697159658376617)
        ·
          refine ⟨19278151186272869743782463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25704201581697159658376617 19278151186272869743782463)
          ·
            refine ⟨28917226779409304615673695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19278151186272869743782463 28917226779409304615673695)
            ·
              refine ⟨43375840169113956923510543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28917226779409304615673695 43375840169113956923510543)
              ·
                refine ⟨65063760253670935385265815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43375840169113956923510543 65063760253670935385265815)
                ·
                  refine ⟨97595640380506403077898723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65063760253670935385265815 97595640380506403077898723)
                  ·
                    refine ⟨146393460570759604616848085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97595640380506403077898723 146393460570759604616848085)
                    ·
                      refine ⟨3431096732127178233207377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146393460570759604616848085 3431096732127178233207377)
                      ·
                        rfl

theorem cell23_6682037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_6682037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682037 prefixEnd_6682037 := by exact prefixLift 6682037
  have htrace : WordTrace (prefixWord ++ tailWord_6682037) baseStart_6682037 baseEnd_6682037 := by
    simpa [prefixWord, tailWord_6682037, baseEnd_6682037] using wordTrace_append hprefix tailTrace_6682037
  have hstable : (prefixWord ++ tailWord_6682037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682037).length < 2 ^ (prefixWord ++ tailWord_6682037).sum := by decide
  have hdescent : baseEnd_6682037 < baseStart_6682037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682057 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 5, 4]
def baseStart_6682057 : Nat := 118140960795 + 6682057 * 2 ^ 59
def prefixEnd_6682057 : Nat := 4983230072969 + 3 ^ 40 * 6682057 * 2
def baseEnd_6682057 : Nat := 1143702333913422718319095

theorem tailTrace_6682057 : CollatzResearch.WordTrace tailWord_6682057 prefixEnd_6682057 1143702333913422718319095 := by
  unfold tailWord_6682057
  simp only [CollatzResearch.WordTrace]
  refine ⟨243714640753056168324780425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162476427168704112216520283 243714640753056168324780425)
  ·
    refine ⟨182785980564792126243585319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243714640753056168324780425 182785980564792126243585319)
    ·
      refine ⟨274178970847188189365377979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182785980564792126243585319 274178970847188189365377979)
      ·
        refine ⟨411268456270782284048066969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274178970847188189365377979 411268456270782284048066969)
        ·
          refine ⟨308451342203086713036050227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411268456270782284048066969 308451342203086713036050227)
          ·
            refine ⟨462677013304630069554075341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308451342203086713036050227 462677013304630069554075341)
            ·
              refine ⟨173503879989236276082778253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462677013304630069554075341 173503879989236276082778253)
              ·
                refine ⟨65063954995963603531041845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173503879989236276082778253 65063954995963603531041845)
                ·
                  refine ⟨6099745780871587831035173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65063954995963603531041845 6099745780871587831035173)
                  ·
                    refine ⟨1143702333913422718319095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6099745780871587831035173 1143702333913422718319095)
                    ·
                      rfl

theorem cell23_6682057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 4].length) (baseStart_6682057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682057 prefixEnd_6682057 := by exact prefixLift 6682057
  have htrace : WordTrace (prefixWord ++ tailWord_6682057) baseStart_6682057 baseEnd_6682057 := by
    simpa [prefixWord, tailWord_6682057, baseEnd_6682057] using wordTrace_append hprefix tailTrace_6682057
  have hstable : (prefixWord ++ tailWord_6682057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682057).length < 2 ^ (prefixWord ++ tailWord_6682057).sum := by decide
  have hdescent : baseEnd_6682057 < baseStart_6682057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682141 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_6682141 : Nat := 118140960795 + 6682141 * 2 ^ 59
def prefixEnd_6682141 : Nat := 4983230072969 + 3 ^ 40 * 6682141 * 2
def baseEnd_6682141 : Nat := 3431150134115245826306899

theorem tailTrace_6682141 : CollatzResearch.WordTrace tailWord_6682141 prefixEnd_6682141 3431150134115245826306899 := by
  unfold tailWord_6682141
  simp only [CollatzResearch.WordTrace]
  refine ⟨243717704484751850670838277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162478469656501233780558851 243717704484751850670838277)
  ·
    refine ⟨45697069590890972000782177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243717704484751850670838277 45697069590890972000782177)
    ·
      refine ⟨34272802193168229000586633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45697069590890972000782177 34272802193168229000586633)
      ·
        refine ⟨25704601644876171750439975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34272802193168229000586633 25704601644876171750439975)
        ·
          refine ⟨38556902467314257625659963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25704601644876171750439975 38556902467314257625659963)
          ·
            refine ⟨57835353700971386438489945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38556902467314257625659963 57835353700971386438489945)
            ·
              refine ⟨43376515275728539828867459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57835353700971386438489945 43376515275728539828867459)
              ·
                refine ⟨65064772913592809743301189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43376515275728539828867459 65064772913592809743301189)
                ·
                  refine ⟨12199644921298651826868973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65064772913592809743301189 12199644921298651826868973)
                  ·
                    refine ⟨4574866845486994435075865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12199644921298651826868973 4574866845486994435075865)
                    ·
                      refine ⟨3431150134115245826306899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574866845486994435075865 3431150134115245826306899)
                      ·
                        rfl

theorem cell23_6682141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_6682141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682141 prefixEnd_6682141 := by exact prefixLift 6682141
  have htrace : WordTrace (prefixWord ++ tailWord_6682141) baseStart_6682141 baseEnd_6682141 := by
    simpa [prefixWord, tailWord_6682141, baseEnd_6682141] using wordTrace_append hprefix tailTrace_6682141
  have hstable : (prefixWord ++ tailWord_6682141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682141).length < 2 ^ (prefixWord ++ tailWord_6682141).sum := by decide
  have hdescent : baseEnd_6682141 < baseStart_6682141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682142 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6682142 : Nat := 118140960795 + 6682142 * 2 ^ 59
def prefixEnd_6682142 : Nat := 4983230072969 + 3 ^ 40 * 6682142 * 2
def baseEnd_6682142 : Nat := 1143716882531966774131465

theorem tailTrace_6682142 : CollatzResearch.WordTrace tailWord_6682142 prefixEnd_6682142 1143716882531966774131465 := by
  unfold tailWord_6682142
  simp only [CollatzResearch.WordTrace]
  refine ⟨30464717619718528480203085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162478493971832151894416453 30464717619718528480203085)
  ·
    refine ⟨11424269107394448180076157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30464717619718528480203085 11424269107394448180076157)
    ·
      refine ⟨4284100915272918067528559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11424269107394448180076157 4284100915272918067528559)
      ·
        refine ⟨6426151372909377101292839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4284100915272918067528559 6426151372909377101292839)
        ·
          refine ⟨9639227059364065651939259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6426151372909377101292839 9639227059364065651939259)
          ·
            refine ⟨14458840589046098477908889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9639227059364065651939259 14458840589046098477908889)
            ·
              refine ⟨10844130441784573858431667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14458840589046098477908889 10844130441784573858431667)
              ·
                refine ⟨16266195662676860787647501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10844130441784573858431667 16266195662676860787647501)
                ·
                  refine ⟨6099823373503822795367813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16266195662676860787647501 6099823373503822795367813)
                  ·
                    refine ⟨1143716882531966774131465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6099823373503822795367813 1143716882531966774131465)
                    ·
                      rfl

theorem cell23_6682142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6682142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682142 prefixEnd_6682142 := by exact prefixLift 6682142
  have htrace : WordTrace (prefixWord ++ tailWord_6682142) baseStart_6682142 baseEnd_6682142 := by
    simpa [prefixWord, tailWord_6682142, baseEnd_6682142] using wordTrace_append hprefix tailTrace_6682142
  have hstable : (prefixWord ++ tailWord_6682142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682142).length < 2 ^ (prefixWord ++ tailWord_6682142).sum := by decide
  have hdescent : baseEnd_6682142 < baseStart_6682142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682194 : List Nat := [3, 2, 2, 1, 2, 4, 9]
def baseStart_6682194 : Nat := 118140960795 + 6682194 * 2 ^ 59
def prefixEnd_6682194 : Nat := 4983230072969 + 3 ^ 40 * 6682194 * 2
def baseEnd_6682194 : Nat := 42360214180122643443755

theorem tailTrace_6682194 : CollatzResearch.WordTrace tailWord_6682194 prefixEnd_6682194 42360214180122643443755 := by
  unfold tailWord_6682194
  simp only [CollatzResearch.WordTrace]
  refine ⟨60929909388389960180629409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162479758369039893815011757 60929909388389960180629409)
  ·
    refine ⟨45697432041292470135472057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60929909388389960180629409 45697432041292470135472057)
    ·
      refine ⟨34273074030969352601604043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45697432041292470135472057 34273074030969352601604043)
      ·
        refine ⟨51409611046454028902406065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34273074030969352601604043 51409611046454028902406065)
        ·
          refine ⟨38557208284840521676804549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51409611046454028902406065 38557208284840521676804549)
          ·
            refine ⟨7229476553407597814400853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38557208284840521676804549 7229476553407597814400853)
            ·
              refine ⟨42360214180122643443755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7229476553407597814400853 42360214180122643443755)
              ·
                rfl

theorem cell23_6682194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 9].length) (baseStart_6682194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682194 prefixEnd_6682194 := by exact prefixLift 6682194
  have htrace : WordTrace (prefixWord ++ tailWord_6682194) baseStart_6682194 baseEnd_6682194 := by
    simpa [prefixWord, tailWord_6682194, baseEnd_6682194] using wordTrace_append hprefix tailTrace_6682194
  have hstable : (prefixWord ++ tailWord_6682194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682194).length < 2 ^ (prefixWord ++ tailWord_6682194).sum := by decide
  have hdescent : baseEnd_6682194 < baseStart_6682194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682306 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_6682306 : Nat := 118140960795 + 6682306 * 2 ^ 59
def prefixEnd_6682306 : Nat := 4983230072969 + 3 ^ 40 * 6682306 * 2
def baseEnd_6682306 : Nat := 3431234858423237680743641

theorem tailTrace_6682306 : CollatzResearch.WordTrace tailWord_6682306 prefixEnd_6682306 3431234858423237680743641 := by
  unfold tailWord_6682306
  simp only [CollatzResearch.WordTrace]
  refine ⟨60930930632288520962648693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162482481686102722567063181 60930930632288520962648693)
  ·
    refine ⟨5712274746777048840248315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60930930632288520962648693 5712274746777048840248315)
    ·
      refine ⟨8568412120165573260372473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5712274746777048840248315 8568412120165573260372473)
      ·
        refine ⟨6426309090124179945279355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8568412120165573260372473 6426309090124179945279355)
        ·
          refine ⟨9639463635186269917919033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6426309090124179945279355 9639463635186269917919033)
          ·
            refine ⟨7229597726389702438439275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9639463635186269917919033 7229597726389702438439275)
            ·
              refine ⟨10844396589584553657658913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7229597726389702438439275 10844396589584553657658913)
              ·
                refine ⟨8133297442188415243244185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10844396589584553657658913 8133297442188415243244185)
                ·
                  refine ⟨6099973081641311432433139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8133297442188415243244185 6099973081641311432433139)
                  ·
                    refine ⟨9149959622461967148649709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6099973081641311432433139 9149959622461967148649709)
                    ·
                      refine ⟨3431234858423237680743641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9149959622461967148649709 3431234858423237680743641)
                      ·
                        rfl

theorem cell23_6682306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_6682306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682306 prefixEnd_6682306 := by exact prefixLift 6682306
  have htrace : WordTrace (prefixWord ++ tailWord_6682306) baseStart_6682306 baseEnd_6682306 := by
    simpa [prefixWord, tailWord_6682306, baseEnd_6682306] using wordTrace_append hprefix tailTrace_6682306
  have hstable : (prefixWord ++ tailWord_6682306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682306).length < 2 ^ (prefixWord ++ tailWord_6682306).sum := by decide
  have hdescent : baseEnd_6682306 < baseStart_6682306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682351 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 4]
def baseStart_6682351 : Nat := 118140960795 + 6682351 * 2 ^ 59
def prefixEnd_6682351 : Nat := 4983230072969 + 3 ^ 40 * 6682351 * 2
def baseEnd_6682351 : Nat := 3431257965052690004680933

theorem tailTrace_6682351 : CollatzResearch.WordTrace tailWord_6682351 prefixEnd_6682351 3431257965052690004680933 := by
  unfold tailWord_6682351
  simp only [CollatzResearch.WordTrace]
  refine ⟨243725363813991056535982907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162483575875994037690655271 243725363813991056535982907)
  ·
    refine ⟨365588045720986584803974361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243725363813991056535982907 365588045720986584803974361)
    ·
      refine ⟨274191034290739938602980771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365588045720986584803974361 274191034290739938602980771)
      ·
        refine ⟨411286551436109907904471157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274191034290739938602980771 411286551436109907904471157)
        ·
          refine ⟨38558114197135303866044171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 411286551436109907904471157 38558114197135303866044171)
          ·
            refine ⟨57837171295702955799066257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38558114197135303866044171 57837171295702955799066257)
            ·
              refine ⟨43377878471777216849299693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57837171295702955799066257 43377878471777216849299693)
              ·
                refine ⟨16266704426916456318487385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43377878471777216849299693 16266704426916456318487385)
                ·
                  refine ⟨12200028320187342238865539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16266704426916456318487385 12200028320187342238865539)
                  ·
                    refine ⟨18300042480281013358298309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12200028320187342238865539 18300042480281013358298309)
                    ·
                      refine ⟨3431257965052690004680933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18300042480281013358298309 3431257965052690004680933)
                      ·
                        rfl

theorem cell23_6682351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_6682351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682351 prefixEnd_6682351 := by exact prefixLift 6682351
  have htrace : WordTrace (prefixWord ++ tailWord_6682351) baseStart_6682351 baseEnd_6682351 := by
    simpa [prefixWord, tailWord_6682351, baseEnd_6682351] using wordTrace_append hprefix tailTrace_6682351
  have hstable : (prefixWord ++ tailWord_6682351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682351).length < 2 ^ (prefixWord ++ tailWord_6682351).sum := by decide
  have hdescent : baseEnd_6682351 < baseStart_6682351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682371 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 3]
def baseStart_6682371 : Nat := 118140960795 + 6682371 * 2 ^ 59
def prefixEnd_6682371 : Nat := 4983230072969 + 3 ^ 40 * 6682371 * 2
def baseEnd_6682371 : Nat := 3431268234665779926430841

theorem tailTrace_6682371 : CollatzResearch.WordTrace tailWord_6682371 prefixEnd_6682371 3431268234665779926430841 := by
  unfold tailWord_6682371
  simp only [CollatzResearch.WordTrace]
  refine ⟨243726093273918599951710967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162484062182612399967807311 243726093273918599951710967)
  ·
    refine ⟨365589139910877899927566451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243726093273918599951710967 365589139910877899927566451)
    ·
      refine ⟨548383709866316849891349677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365589139910877899927566451 548383709866316849891349677)
      ·
        refine ⟨205643891199868818709256129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548383709866316849891349677 205643891199868818709256129)
        ·
          refine ⟨154232918399901614031942097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205643891199868818709256129 154232918399901614031942097)
          ·
            refine ⟨115674688799926210523956573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154232918399901614031942097 115674688799926210523956573)
            ·
              refine ⟨43378008299972328946483715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115674688799926210523956573 43378008299972328946483715)
              ·
                refine ⟨65067012449958493419725573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43378008299972328946483715 65067012449958493419725573)
                ·
                  refine ⟨12200064834367217516198545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65067012449958493419725573 12200064834367217516198545)
                  ·
                    refine ⟨9150048625775413137148909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12200064834367217516198545 9150048625775413137148909)
                    ·
                      refine ⟨3431268234665779926430841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9150048625775413137148909 3431268234665779926430841)
                      ·
                        rfl

theorem cell23_6682371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_6682371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682371 prefixEnd_6682371 := by exact prefixLift 6682371
  have htrace : WordTrace (prefixWord ++ tailWord_6682371) baseStart_6682371 baseEnd_6682371 := by
    simpa [prefixWord, tailWord_6682371, baseEnd_6682371] using wordTrace_append hprefix tailTrace_6682371
  have hstable : (prefixWord ++ tailWord_6682371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682371).length < 2 ^ (prefixWord ++ tailWord_6682371).sum := by decide
  have hdescent : baseEnd_6682371 < baseStart_6682371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682378 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 3, 4]
def baseStart_6682378 : Nat := 118140960795 + 6682378 * 2 ^ 59
def prefixEnd_6682378 : Nat := 4983230072969 + 3 ^ 40 * 6682378 * 2
def baseEnd_6682378 : Nat := 1143757276343453799681103

theorem tailTrace_6682378 : CollatzResearch.WordTrace tailWord_6682378 prefixEnd_6682378 1143757276343453799681103 := by
  unfold tailWord_6682378
  simp only [CollatzResearch.WordTrace]
  refine ⟨60931587146223310036803947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162484232389928826764810525 60931587146223310036803947)
  ·
    refine ⟨91397380719334965055205921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60931587146223310036803947 91397380719334965055205921)
    ·
      refine ⟨68548035539501223791404441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91397380719334965055205921 68548035539501223791404441)
      ·
        refine ⟨51411026654625917843553331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68548035539501223791404441 51411026654625917843553331)
        ·
          refine ⟨77116539981938876765329997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51411026654625917843553331 77116539981938876765329997)
          ·
            refine ⟨28918702493227078786998749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77116539981938876765329997 28918702493227078786998749)
            ·
              refine ⟨10844513434960154545124531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28918702493227078786998749 10844513434960154545124531)
              ·
                refine ⟨16266770152440231817686797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10844513434960154545124531 16266770152440231817686797)
                ·
                  refine ⟨6100038807165086931632549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16266770152440231817686797 6100038807165086931632549)
                  ·
                    refine ⟨1143757276343453799681103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6100038807165086931632549 1143757276343453799681103)
                    ·
                      rfl

theorem cell23_6682378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_6682378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682378 prefixEnd_6682378 := by exact prefixLift 6682378
  have htrace : WordTrace (prefixWord ++ tailWord_6682378) baseStart_6682378 baseEnd_6682378 := by
    simpa [prefixWord, tailWord_6682378, baseEnd_6682378] using wordTrace_append hprefix tailTrace_6682378
  have hstable : (prefixWord ++ tailWord_6682378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682378).length < 2 ^ (prefixWord ++ tailWord_6682378).sum := by decide
  have hdescent : baseEnd_6682378 < baseStart_6682378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682425 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 6]
def baseStart_6682425 : Nat := 118140960795 + 6682425 * 2 ^ 59
def prefixEnd_6682425 : Nat := 4983230072969 + 3 ^ 40 * 6682425 * 2
def baseEnd_6682425 : Nat := 381255106957902523906177

theorem tailTrace_6682425 : CollatzResearch.WordTrace tailWord_6682425 prefixEnd_6682425 381255106957902523906177 := by
  unfold tailWord_6682425
  simp only [CollatzResearch.WordTrace]
  refine ⟨243728062815722967174176729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162485375210481978116117819 243728062815722967174176729)
  ·
    refine ⟨182796047111792225380632547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243728062815722967174176729 182796047111792225380632547)
    ·
      refine ⟨274194070667688338070948821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182796047111792225380632547 274194070667688338070948821)
      ·
        refine ⟨6426423531273945423537863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 274194070667688338070948821 6426423531273945423537863)
        ·
          refine ⟨9639635296910918135306795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6426423531273945423537863 9639635296910918135306795)
          ·
            refine ⟨14459452945366377202960193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9639635296910918135306795 14459452945366377202960193)
            ·
              refine ⟨10844589709024782902220145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14459452945366377202960193 10844589709024782902220145)
              ·
                refine ⟨8133442281768587176665109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10844589709024782902220145 8133442281768587176665109)
                ·
                  refine ⟨381255106957902523906177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8133442281768587176665109 381255106957902523906177)
                  ·
                    rfl

theorem cell23_6682425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 6].length) (baseStart_6682425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682425 prefixEnd_6682425 := by exact prefixLift 6682425
  have htrace : WordTrace (prefixWord ++ tailWord_6682425) baseStart_6682425 baseEnd_6682425 := by
    simpa [prefixWord, tailWord_6682425, baseEnd_6682425] using wordTrace_append hprefix tailTrace_6682425
  have hstable : (prefixWord ++ tailWord_6682425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682425).length < 2 ^ (prefixWord ++ tailWord_6682425).sum := by decide
  have hdescent : baseEnd_6682425 < baseStart_6682425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682429 : List Nat := [1, 4, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_6682429 : Nat := 118140960795 + 6682429 * 2 ^ 59
def prefixEnd_6682429 : Nat := 4983230072969 + 3 ^ 40 * 6682429 * 2
def baseEnd_6682429 : Nat := 1143766005514580233168525

theorem tailTrace_6682429 : CollatzResearch.WordTrace tailWord_6682429 prefixEnd_6682429 1143766005514580233168525 := by
  unfold tailWord_6682429
  simp only [CollatzResearch.WordTrace]
  refine ⟨243728208707708475857322341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162485472471805650571548227 243728208707708475857322341)
  ·
    refine ⟨45699039132695339223247939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243728208707708475857322341 45699039132695339223247939)
    ·
      refine ⟨68548558699043008834871909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45699039132695339223247939 68548558699043008834871909)
      ·
        refine ⟨12852854756070564156538483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68548558699043008834871909 12852854756070564156538483)
        ·
          refine ⟨19279282134105846234807725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12852854756070564156538483 19279282134105846234807725)
          ·
            refine ⟨7229730800289692338052897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19279282134105846234807725 7229730800289692338052897)
            ·
              refine ⟨5422298100217269253539673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7229730800289692338052897 5422298100217269253539673)
              ·
                refine ⟨4066723575162951940154755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5422298100217269253539673 4066723575162951940154755)
                ·
                  refine ⟨6100085362744427910232133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4066723575162951940154755 6100085362744427910232133)
                  ·
                    refine ⟨1143766005514580233168525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6100085362744427910232133 1143766005514580233168525)
                    ·
                      rfl

theorem cell23_6682429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_6682429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682429 prefixEnd_6682429 := by exact prefixLift 6682429
  have htrace : WordTrace (prefixWord ++ tailWord_6682429) baseStart_6682429 baseEnd_6682429 := by
    simpa [prefixWord, tailWord_6682429, baseEnd_6682429] using wordTrace_append hprefix tailTrace_6682429
  have hstable : (prefixWord ++ tailWord_6682429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682429).length < 2 ^ (prefixWord ++ tailWord_6682429).sum := by decide
  have hdescent : baseEnd_6682429 < baseStart_6682429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682441 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 4]
def baseStart_6682441 : Nat := 118140960795 + 6682441 * 2 ^ 59
def prefixEnd_6682441 : Nat := 4983230072969 + 3 ^ 40 * 6682441 * 2
def baseEnd_6682441 : Nat := 3431304178311594652555519

theorem tailTrace_6682441 : CollatzResearch.WordTrace tailWord_6682441 prefixEnd_6682441 3431304178311594652555519 := by
  unfold tailWord_6682441
  simp only [CollatzResearch.WordTrace]
  refine ⟨243728646383665001906759177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162485764255776667937839451 243728646383665001906759177)
  ·
    refine ⟨182796484787748751430069383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243728646383665001906759177 182796484787748751430069383)
    ·
      refine ⟨274194727181623127145104075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182796484787748751430069383 274194727181623127145104075)
      ·
        refine ⟨411292090772434690717656113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274194727181623127145104075 411292090772434690717656113)
        ·
          refine ⟨308469068079326018038242085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411292090772434690717656113 308469068079326018038242085)
          ·
            refine ⟨57837950264873628382170391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308469068079326018038242085 57837950264873628382170391)
            ·
              refine ⟨86756925397310442573255587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57837950264873628382170391 86756925397310442573255587)
              ·
                refine ⟨130135388095965663859883381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86756925397310442573255587 130135388095965663859883381)
                ·
                  refine ⟨12200192633996780986864067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130135388095965663859883381 12200192633996780986864067)
                  ·
                    refine ⟨18300288950995171480296101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12200192633996780986864067 18300288950995171480296101)
                    ·
                      refine ⟨3431304178311594652555519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18300288950995171480296101 3431304178311594652555519)
                      ·
                        rfl

theorem cell23_6682441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_6682441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682441 prefixEnd_6682441 := by exact prefixLift 6682441
  have htrace : WordTrace (prefixWord ++ tailWord_6682441) baseStart_6682441 baseEnd_6682441 := by
    simpa [prefixWord, tailWord_6682441, baseEnd_6682441] using wordTrace_append hprefix tailTrace_6682441
  have hstable : (prefixWord ++ tailWord_6682441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682441).length < 2 ^ (prefixWord ++ tailWord_6682441).sum := by decide
  have hdescent : baseEnd_6682441 < baseStart_6682441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682451 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 8, 4]
def baseStart_6682451 : Nat := 118140960795 + 6682451 * 2 ^ 59
def prefixEnd_6682451 : Nat := 4983230072969 + 3 ^ 40 * 6682451 * 2
def baseEnd_6682451 : Nat := 1143769771039379871143491

theorem tailTrace_6682451 : CollatzResearch.WordTrace tailWord_6682451 prefixEnd_6682451 1143769771039379871143491 := by
  unfold tailWord_6682451
  simp only [CollatzResearch.WordTrace]
  refine ⟨243729011113628773614623207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162486007409085849076415471 243729011113628773614623207)
  ·
    refine ⟨365593516670443160421934811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243729011113628773614623207 365593516670443160421934811)
    ·
      refine ⟨548390275005664740632902217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365593516670443160421934811 548390275005664740632902217)
      ·
        refine ⟨411292706254248555474676663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548390275005664740632902217 411292706254248555474676663)
        ·
          refine ⟨616939059381372833212014995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411292706254248555474676663 616939059381372833212014995)
          ·
            refine ⟨925408589072059249818022493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616939059381372833212014995 925408589072059249818022493)
            ·
              refine ⟨347028220902022218681758435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925408589072059249818022493 347028220902022218681758435)
              ·
                refine ⟨520542331353033328022637653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347028220902022218681758435 520542331353033328022637653)
                ·
                  refine ⟨6100105445543359312765285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 520542331353033328022637653 6100105445543359312765285)
                  ·
                    refine ⟨1143769771039379871143491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6100105445543359312765285 1143769771039379871143491)
                    ·
                      rfl

theorem cell23_6682451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 4].length) (baseStart_6682451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682451 prefixEnd_6682451 := by exact prefixLift 6682451
  have htrace : WordTrace (prefixWord ++ tailWord_6682451) baseStart_6682451 baseEnd_6682451 := by
    simpa [prefixWord, tailWord_6682451, baseEnd_6682451] using wordTrace_append hprefix tailTrace_6682451
  have hstable : (prefixWord ++ tailWord_6682451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682451).length < 2 ^ (prefixWord ++ tailWord_6682451).sum := by decide
  have hdescent : baseEnd_6682451 < baseStart_6682451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682458 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4]
def baseStart_6682458 : Nat := 118140960795 + 6682458 * 2 ^ 59
def prefixEnd_6682458 : Nat := 4983230072969 + 3 ^ 40 * 6682458 * 2
def baseEnd_6682458 : Nat := 3431312907482721086042941

theorem tailTrace_6682458 : CollatzResearch.WordTrace tailWord_6682458 prefixEnd_6682458 3431312907482721086042941 := by
  unfold tailWord_6682458
  simp only [CollatzResearch.WordTrace]
  refine ⟨60932316606150853452532007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162486177616402275873418685 60932316606150853452532007)
  ·
    refine ⟨91398474909226280178798011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60932316606150853452532007 91398474909226280178798011)
    ·
      refine ⟨137097712363839420268197017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91398474909226280178798011 137097712363839420268197017)
      ·
        refine ⟨102823284272879565201147763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137097712363839420268197017 102823284272879565201147763)
        ·
          refine ⟨154234926409319347801721645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102823284272879565201147763 154234926409319347801721645)
          ·
            refine ⟨57838097403494755425645617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154234926409319347801721645 57838097403494755425645617)
            ·
              refine ⟨43378573052621066569234213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57838097403494755425645617 43378573052621066569234213)
              ·
                refine ⟨8133482447366449981731415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43378573052621066569234213 8133482447366449981731415)
                ·
                  refine ⟨12200223671049674972597123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8133482447366449981731415 12200223671049674972597123)
                  ·
                    refine ⟨18300335506574512458895685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12200223671049674972597123 18300335506574512458895685)
                    ·
                      refine ⟨3431312907482721086042941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18300335506574512458895685 3431312907482721086042941)
                      ·
                        rfl

theorem cell23_6682458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_6682458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682458 prefixEnd_6682458 := by exact prefixLift 6682458
  have htrace : WordTrace (prefixWord ++ tailWord_6682458) baseStart_6682458 baseEnd_6682458 := by
    simpa [prefixWord, tailWord_6682458, baseEnd_6682458] using wordTrace_append hprefix tailTrace_6682458
  have hstable : (prefixWord ++ tailWord_6682458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682458).length < 2 ^ (prefixWord ++ tailWord_6682458).sum := by decide
  have hdescent : baseEnd_6682458 < baseStart_6682458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682521 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_6682521 : Nat := 118140960795 + 6682521 * 2 ^ 59
def prefixEnd_6682521 : Nat := 4983230072969 + 3 ^ 40 * 6682521 * 2
def baseEnd_6682521 : Nat := 3431345256763954339555151

theorem tailTrace_6682521 : CollatzResearch.WordTrace tailWord_6682521 prefixEnd_6682521 3431345256763954339555151 := by
  unfold tailWord_6682521
  simp only [CollatzResearch.WordTrace]
  refine ⟨243731564223375175569671417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162487709482250117046447611 243731564223375175569671417)
  ·
    refine ⟨182798673167531381677253563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243731564223375175569671417 182798673167531381677253563)
    ·
      refine ⟨274198009751297072515880345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182798673167531381677253563 274198009751297072515880345)
      ·
        refine ⟨205648507313472804386910259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274198009751297072515880345 205648507313472804386910259)
        ·
          refine ⟨308472760970209206580365389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205648507313472804386910259 308472760970209206580365389)
          ·
            refine ⟨115677285363828452467637021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308472760970209206580365389 115677285363828452467637021)
            ·
              refine ⟨43378982011435669675363883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115677285363828452467637021 43378982011435669675363883)
              ·
                refine ⟨65068473017153504513045825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43378982011435669675363883 65068473017153504513045825)
                ·
                  refine ⟨48801354762865128384784369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65068473017153504513045825 48801354762865128384784369)
                  ·
                    refine ⟨36601016072148846288588277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48801354762865128384784369 36601016072148846288588277)
                    ·
                      refine ⟨3431345256763954339555151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36601016072148846288588277 3431345256763954339555151)
                      ·
                        rfl

theorem cell23_6682521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_6682521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682521 prefixEnd_6682521 := by exact prefixLift 6682521
  have htrace : WordTrace (prefixWord ++ tailWord_6682521) baseStart_6682521 baseEnd_6682521 := by
    simpa [prefixWord, tailWord_6682521, baseEnd_6682521] using wordTrace_append hprefix tailTrace_6682521
  have hstable : (prefixWord ++ tailWord_6682521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682521).length < 2 ^ (prefixWord ++ tailWord_6682521).sum := by decide
  have hdescent : baseEnd_6682521 < baseStart_6682521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682525 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_6682525 : Nat := 118140960795 + 6682525 * 2 ^ 59
def prefixEnd_6682525 : Nat := 4983230072969 + 3 ^ 40 * 6682525 * 2
def baseEnd_6682525 : Nat := 3431347310686572323905133

theorem tailTrace_6682525 : CollatzResearch.WordTrace tailWord_6682525 prefixEnd_6682525 3431347310686572323905133 := by
  unfold tailWord_6682525
  simp only [CollatzResearch.WordTrace]
  refine ⟨243731710115360684252817029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162487806743573789501878019 243731710115360684252817029)
  ·
    refine ⟨45699695646630128297403193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243731710115360684252817029 45699695646630128297403193)
    ·
      refine ⟨34274771734972596223052395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45699695646630128297403193 34274771734972596223052395)
      ·
        refine ⟨51412157602458894334578593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34274771734972596223052395 51412157602458894334578593)
        ·
          refine ⟨38559118201844170750933945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51412157602458894334578593 38559118201844170750933945)
          ·
            refine ⟨28919338651383128063200459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38559118201844170750933945 28919338651383128063200459)
            ·
              refine ⟨43379007977074692094800689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28919338651383128063200459 43379007977074692094800689)
              ·
                refine ⟨32534255982806019071100517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43379007977074692094800689 32534255982806019071100517)
                ·
                  refine ⟨6100172996776128575831347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32534255982806019071100517 6100172996776128575831347)
                  ·
                    refine ⟨9150259495164192863747021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6100172996776128575831347 9150259495164192863747021)
                    ·
                      refine ⟨3431347310686572323905133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9150259495164192863747021 3431347310686572323905133)
                      ·
                        rfl

theorem cell23_6682525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_6682525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682525 prefixEnd_6682525 := by exact prefixLift 6682525
  have htrace : WordTrace (prefixWord ++ tailWord_6682525) baseStart_6682525 baseEnd_6682525 := by
    simpa [prefixWord, tailWord_6682525, baseEnd_6682525] using wordTrace_append hprefix tailTrace_6682525
  have hstable : (prefixWord ++ tailWord_6682525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682525).length < 2 ^ (prefixWord ++ tailWord_6682525).sum := by decide
  have hdescent : baseEnd_6682525 < baseStart_6682525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682531 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 4]
def baseStart_6682531 : Nat := 118140960795 + 6682531 * 2 ^ 59
def prefixEnd_6682531 : Nat := 4983230072969 + 3 ^ 40 * 6682531 * 2
def baseEnd_6682531 : Nat := 3431350391570499300430105

theorem tailTrace_6682531 : CollatzResearch.WordTrace tailWord_6682531 prefixEnd_6682531 3431350391570499300430105 := by
  unfold tailWord_6682531
  simp only [CollatzResearch.WordTrace]
  refine ⟨243731928953338947277535447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162487952635559298185023631 243731928953338947277535447)
  ·
    refine ⟨365597893430008420916303171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243731928953338947277535447 365597893430008420916303171)
    ·
      refine ⟨548396840145012631374454757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365597893430008420916303171 548396840145012631374454757)
      ·
        refine ⟨102824407527189868382710267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 548396840145012631374454757 102824407527189868382710267)
        ·
          refine ⟨154236611290784802574065401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102824407527189868382710267 154236611290784802574065401)
          ·
            refine ⟨115677458468088601930549051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154236611290784802574065401 115677458468088601930549051)
            ·
              refine ⟨173516187702132902895823577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115677458468088601930549051 173516187702132902895823577)
              ·
                refine ⟨130137140776599677171867683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173516187702132902895823577 130137140776599677171867683)
                ·
                  refine ⟨195205711164899515757801525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130137140776599677171867683 195205711164899515757801525)
                  ·
                    refine ⟨18300535421709329602293893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 195205711164899515757801525 18300535421709329602293893)
                    ·
                      refine ⟨3431350391570499300430105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18300535421709329602293893 3431350391570499300430105)
                      ·
                        rfl

theorem cell23_6682531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_6682531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682531 prefixEnd_6682531 := by exact prefixLift 6682531
  have htrace : WordTrace (prefixWord ++ tailWord_6682531) baseStart_6682531 baseEnd_6682531 := by
    simpa [prefixWord, tailWord_6682531, baseEnd_6682531] using wordTrace_append hprefix tailTrace_6682531
  have hstable : (prefixWord ++ tailWord_6682531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682531).length < 2 ^ (prefixWord ++ tailWord_6682531).sum := by decide
  have hdescent : baseEnd_6682531 < baseStart_6682531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682551 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_6682551 : Nat := 118140960795 + 6682551 * 2 ^ 59
def prefixEnd_6682551 : Nat := 4983230072969 + 3 ^ 40 * 6682551 * 2
def baseEnd_6682551 : Nat := 3431360661183589222180013

theorem tailTrace_6682551 : CollatzResearch.WordTrace tailWord_6682551 prefixEnd_6682551 3431360661183589222180013 := by
  unfold tailWord_6682551
  simp only [CollatzResearch.WordTrace]
  refine ⟨243732658413266490693263507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162488438942177660462175671 243732658413266490693263507)
  ·
    refine ⟨365598987619899736039895261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243732658413266490693263507 365598987619899736039895261)
    ·
      refine ⟨137099620357462401014960723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365598987619899736039895261 137099620357462401014960723)
      ·
        refine ⟨205649430536193601522441085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137099620357462401014960723 205649430536193601522441085)
        ·
          refine ⟨77118536451072600570915407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205649430536193601522441085 77118536451072600570915407)
          ·
            refine ⟨115677804676608900856373111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77118536451072600570915407 115677804676608900856373111)
            ·
              refine ⟨173516707014913351284559667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115677804676608900856373111 173516707014913351284559667)
              ·
                refine ⟨260275060522370026926839501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173516707014913351284559667 260275060522370026926839501)
                ·
                  refine ⟨97603147695888760097564813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260275060522370026926839501 97603147695888760097564813)
                  ·
                    refine ⟨36601180385958285036586805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97603147695888760097564813 36601180385958285036586805)
                    ·
                      refine ⟨3431360661183589222180013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36601180385958285036586805 3431360661183589222180013)
                      ·
                        rfl

theorem cell23_6682551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_6682551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682551 prefixEnd_6682551 := by exact prefixLift 6682551
  have htrace : WordTrace (prefixWord ++ tailWord_6682551) baseStart_6682551 baseEnd_6682551 := by
    simpa [prefixWord, tailWord_6682551, baseEnd_6682551] using wordTrace_append hprefix tailTrace_6682551
  have hstable : (prefixWord ++ tailWord_6682551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682551).length < 2 ^ (prefixWord ++ tailWord_6682551).sum := by decide
  have hdescent : baseEnd_6682551 < baseStart_6682551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682565 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 6, 2, 2]
def baseStart_6682565 : Nat := 118140960795 + 6682565 * 2 ^ 59
def prefixEnd_6682565 : Nat := 4983230072969 + 3 ^ 40 * 6682565 * 2
def baseEnd_6682565 : Nat := 3431367849912752167404949

theorem tailTrace_6682565 : CollatzResearch.WordTrace tailWord_6682565 prefixEnd_6682565 3431367849912752167404949 := by
  unfold tailWord_6682565
  simp only [CollatzResearch.WordTrace]
  refine ⟨243733169035215771084273149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162488779356810514056182099 243733169035215771084273149)
  ·
    refine ⟨91399938388205914156602431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243733169035215771084273149 91399938388205914156602431)
    ·
      refine ⟨137099907582308871234903647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91399938388205914156602431 137099907582308871234903647)
      ·
        refine ⟨205649861373463306852355471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137099907582308871234903647 205649861373463306852355471)
        ·
          refine ⟨308474792060194960278533207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205649861373463306852355471 308474792060194960278533207)
          ·
            refine ⟨462712188090292440417799811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308474792060194960278533207 462712188090292440417799811)
            ·
              refine ⟨694068282135438660626699717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462712188090292440417799811 694068282135438660626699717)
              ·
                refine ⟨130137802900394748867506197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 694068282135438660626699717 130137802900394748867506197)
                ·
                  refine ⟨6100209510956003853164353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130137802900394748867506197 6100209510956003853164353)
                  ·
                    refine ⟨4575157133217002889873265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6100209510956003853164353 4575157133217002889873265)
                    ·
                      refine ⟨3431367849912752167404949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575157133217002889873265 3431367849912752167404949)
                      ·
                        rfl

theorem cell23_6682565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 2, 2].length) (baseStart_6682565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682565 prefixEnd_6682565 := by exact prefixLift 6682565
  have htrace : WordTrace (prefixWord ++ tailWord_6682565) baseStart_6682565 baseEnd_6682565 := by
    simpa [prefixWord, tailWord_6682565, baseEnd_6682565] using wordTrace_append hprefix tailTrace_6682565
  have hstable : (prefixWord ++ tailWord_6682565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682565).length < 2 ^ (prefixWord ++ tailWord_6682565).sum := by decide
  have hdescent : baseEnd_6682565 < baseStart_6682565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682568 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_6682568 : Nat := 118140960795 + 6682568 * 2 ^ 59
def prefixEnd_6682568 : Nat := 4983230072969 + 3 ^ 40 * 6682568 * 2
def baseEnd_6682568 : Nat := 3431369390354715655667435

theorem tailTrace_6682568 : CollatzResearch.WordTrace tailWord_6682568 prefixEnd_6682568 3431369390354715655667435 := by
  unfold tailWord_6682568
  simp only [CollatzResearch.WordTrace]
  refine ⟨121866639227102451298316179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162488852302803268397754905 121866639227102451298316179)
  ·
    refine ⟨182799958840653676947474269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121866639227102451298316179 182799958840653676947474269)
    ·
      refine ⟨68549984565245128855302851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182799958840653676947474269 68549984565245128855302851)
      ·
        refine ⟨102824976847867693282954277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68549984565245128855302851 102824976847867693282954277)
        ·
          refine ⟨19279683158975192490553927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102824976847867693282954277 19279683158975192490553927)
          ·
            refine ⟨28919524738462788735830891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19279683158975192490553927 28919524738462788735830891)
            ·
              refine ⟨43379287107694183103746337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28919524738462788735830891 43379287107694183103746337)
              ·
                refine ⟨32534465330770637327809753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43379287107694183103746337 32534465330770637327809753)
                ·
                  refine ⟨24400848998077977995857315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32534465330770637327809753 24400848998077977995857315)
                  ·
                    refine ⟨36601273497116966993785973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24400848998077977995857315 36601273497116966993785973)
                    ·
                      refine ⟨3431369390354715655667435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36601273497116966993785973 3431369390354715655667435)
                      ·
                        rfl

theorem cell23_6682568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_6682568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682568 prefixEnd_6682568 := by exact prefixLift 6682568
  have htrace : WordTrace (prefixWord ++ tailWord_6682568) baseStart_6682568 baseEnd_6682568 := by
    simpa [prefixWord, tailWord_6682568, baseEnd_6682568] using wordTrace_append hprefix tailTrace_6682568
  have hstable : (prefixWord ++ tailWord_6682568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682568).length < 2 ^ (prefixWord ++ tailWord_6682568).sum := by decide
  have hdescent : baseEnd_6682568 < baseStart_6682568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682571 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 9]
def baseStart_6682571 : Nat := 118140960795 + 6682571 * 2 ^ 59
def prefixEnd_6682571 : Nat := 4983230072969 + 3 ^ 40 * 6682571 * 2
def baseEnd_6682571 : Nat := 381263436755186571547769

theorem tailTrace_6682571 : CollatzResearch.WordTrace tailWord_6682571 prefixEnd_6682571 381263436755186571547769 := by
  unfold tailWord_6682571
  simp only [CollatzResearch.WordTrace]
  refine ⟨243733387873194034108991567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162488925248796022739327711 243733387873194034108991567)
  ·
    refine ⟨365600081809791051163487351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243733387873194034108991567 365600081809791051163487351)
    ·
      refine ⟨548400122714686576745231027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365600081809791051163487351 548400122714686576745231027)
      ·
        refine ⟨822600184072029865117846541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548400122714686576745231027 822600184072029865117846541)
        ·
          refine ⟨308475069027011199419192453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 822600184072029865117846541 308475069027011199419192453)
          ·
            refine ⟨57839075442564599891098585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308475069027011199419192453 57839075442564599891098585)
            ·
              refine ⟨43379306581923449918323939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57839075442564599891098585 43379306581923449918323939)
              ·
                refine ⟨65068959872885174877485909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43379306581923449918323939 65068959872885174877485909)
                ·
                  refine ⟨381263436755186571547769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65068959872885174877485909 381263436755186571547769)
                  ·
                    rfl

theorem cell23_6682571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 9].length) (baseStart_6682571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682571 prefixEnd_6682571 := by exact prefixLift 6682571
  have htrace : WordTrace (prefixWord ++ tailWord_6682571) baseStart_6682571 baseEnd_6682571 := by
    simpa [prefixWord, tailWord_6682571, baseEnd_6682571] using wordTrace_append hprefix tailTrace_6682571
  have hstable : (prefixWord ++ tailWord_6682571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682571).length < 2 ^ (prefixWord ++ tailWord_6682571).sum := by decide
  have hdescent : baseEnd_6682571 < baseStart_6682571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682625 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_6682625 : Nat := 118140960795 + 6682625 * 2 ^ 59
def prefixEnd_6682625 : Nat := 4983230072969 + 3 ^ 40 * 6682625 * 2
def baseEnd_6682625 : Nat := 3431398658752021932654673

theorem tailTrace_6682625 : CollatzResearch.WordTrace tailWord_6682625 prefixEnd_6682625 3431398658752021932654673 := by
  unfold tailWord_6682625
  simp only [CollatzResearch.WordTrace]
  refine ⟨243735357414998401331457329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162490238276665600887638219 243735357414998401331457329)
  ·
    refine ⟨182801518061248800998592997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243735357414998401331457329 182801518061248800998592997)
    ·
      refine ⟨34275284636484150187236187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182801518061248800998592997 34275284636484150187236187)
      ·
        refine ⟨51412926954726225280854281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34275284636484150187236187 51412926954726225280854281)
        ·
          refine ⟨38559695216044668960640711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51412926954726225280854281 38559695216044668960640711)
          ·
            refine ⟨57839542824067003440961067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38559695216044668960640711 57839542824067003440961067)
            ·
              refine ⟨86759314236100505161441601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57839542824067003440961067 86759314236100505161441601)
              ·
                refine ⟨65069485677075378871081201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86759314236100505161441601 65069485677075378871081201)
                ·
                  refine ⟨48802114257806534153310901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65069485677075378871081201 48802114257806534153310901)
                  ·
                    refine ⟨4575198211669362576872897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48802114257806534153310901 4575198211669362576872897)
                    ·
                      refine ⟨3431398658752021932654673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575198211669362576872897 3431398658752021932654673)
                      ·
                        rfl

theorem cell23_6682625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_6682625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682625 prefixEnd_6682625 := by exact prefixLift 6682625
  have htrace : WordTrace (prefixWord ++ tailWord_6682625) baseStart_6682625 baseEnd_6682625 := by
    simpa [prefixWord, tailWord_6682625, baseEnd_6682625] using wordTrace_append hprefix tailTrace_6682625
  have hstable : (prefixWord ++ tailWord_6682625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682625).length < 2 ^ (prefixWord ++ tailWord_6682625).sum := by decide
  have hdescent : baseEnd_6682625 < baseStart_6682625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682637 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6682637 : Nat := 118140960795 + 6682637 * 2 ^ 59
def prefixEnd_6682637 : Nat := 4983230072969 + 3 ^ 40 * 6682637 * 2
def baseEnd_6682637 : Nat := 3431404820519875885704619

theorem tailTrace_6682637 : CollatzResearch.WordTrace tailWord_6682637 prefixEnd_6682637 3431404820519875885704619 := by
  unfold tailWord_6682637
  simp only [CollatzResearch.WordTrace]
  refine ⟨243735795090954927380894165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162490530060636618253929443 243735795090954927380894165)
  ·
    refine ⟨5712557697444256110489707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 243735795090954927380894165 5712557697444256110489707)
    ·
      refine ⟨8568836546166384165734561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5712557697444256110489707 8568836546166384165734561)
      ·
        refine ⟨6426627409624788124300921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8568836546166384165734561 6426627409624788124300921)
        ·
          refine ⟨4819970557218591093225691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6426627409624788124300921 4819970557218591093225691)
          ·
            refine ⟨7229955835827886639838537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4819970557218591093225691 7229955835827886639838537)
            ·
              refine ⟨5422466876870914979878903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7229955835827886639838537 5422466876870914979878903)
              ·
                refine ⟨8133700315306372469818355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422466876870914979878903 8133700315306372469818355)
                ·
                  refine ⟨12200550472959558704727533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8133700315306372469818355 12200550472959558704727533)
                  ·
                    refine ⟨4575206427359834514272825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12200550472959558704727533 4575206427359834514272825)
                    ·
                      refine ⟨3431404820519875885704619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575206427359834514272825 3431404820519875885704619)
                      ·
                        rfl

theorem cell23_6682637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6682637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682637 prefixEnd_6682637 := by exact prefixLift 6682637
  have htrace : WordTrace (prefixWord ++ tailWord_6682637) baseStart_6682637 baseEnd_6682637 := by
    simpa [prefixWord, tailWord_6682637, baseEnd_6682637] using wordTrace_append hprefix tailTrace_6682637
  have hstable : (prefixWord ++ tailWord_6682637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682637).length < 2 ^ (prefixWord ++ tailWord_6682637).sum := by decide
  have hdescent : baseEnd_6682637 < baseStart_6682637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682655 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 4, 4, 2]
def baseStart_6682655 : Nat := 118140960795 + 6682655 * 2 ^ 59
def prefixEnd_6682655 : Nat := 4983230072969 + 3 ^ 40 * 6682655 * 2
def baseEnd_6682655 : Nat := 3431414063171656815279535

theorem tailTrace_6682655 : CollatzResearch.WordTrace tailWord_6682655 prefixEnd_6682655 3431414063171656815279535 := by
  unfold tailWord_6682655
  simp only [CollatzResearch.WordTrace]
  refine ⟨243736451604889716455049419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162490967736593144303366279 243736451604889716455049419)
  ·
    refine ⟨365604677407334574682574129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243736451604889716455049419 365604677407334574682574129)
    ·
      refine ⟨274203508055500931011930597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365604677407334574682574129 274203508055500931011930597)
      ·
        refine ⟨51413157760406424564736987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274203508055500931011930597 51413157760406424564736987)
        ·
          refine ⟨77119736640609636847105481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51413157760406424564736987 77119736640609636847105481)
          ·
            refine ⟨57839802480457227635329111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77119736640609636847105481 57839802480457227635329111)
            ·
              refine ⟨86759703720685841452993667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57839802480457227635329111 86759703720685841452993667)
              ·
                refine ⟨130139555581028762179490501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86759703720685841452993667 130139555581028762179490501)
                ·
                  refine ⟨24401166671442892908654469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130139555581028762179490501 24401166671442892908654469)
                  ·
                    refine ⟨4575218750895542420372713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24401166671442892908654469 4575218750895542420372713)
                    ·
                      refine ⟨3431414063171656815279535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575218750895542420372713 3431414063171656815279535)
                      ·
                        rfl

theorem cell23_6682655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_6682655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682655 prefixEnd_6682655 := by exact prefixLift 6682655
  have htrace : WordTrace (prefixWord ++ tailWord_6682655) baseStart_6682655 baseEnd_6682655 := by
    simpa [prefixWord, tailWord_6682655, baseEnd_6682655] using wordTrace_append hprefix tailTrace_6682655
  have hstable : (prefixWord ++ tailWord_6682655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682655).length < 2 ^ (prefixWord ++ tailWord_6682655).sum := by decide
  have hdescent : baseEnd_6682655 < baseStart_6682655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682716 : List Nat := [2, 2, 4, 1, 1, 3, 3, 2, 1, 4]
def baseStart_6682716 : Nat := 118140960795 + 6682716 * 2 ^ 59
def prefixEnd_6682716 : Nat := 4983230072969 + 3 ^ 40 * 6682716 * 2
def baseEnd_6682716 : Nat := 1143815128497193692205585

theorem tailTrace_6682716 : CollatzResearch.WordTrace tailWord_6682716 prefixEnd_6682716 1143815128497193692205585 := by
  unfold tailWord_6682716
  simp only [CollatzResearch.WordTrace]
  refine ⟨121869338228834361936510001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162492450971779149248680001 121869338228834361936510001)
  ·
    refine ⟨91402003671625771452382501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121869338228834361936510001 91402003671625771452382501)
    ·
      refine ⟨17137875688429832147321719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91402003671625771452382501 17137875688429832147321719)
      ·
        refine ⟨25706813532644748220982579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17137875688429832147321719 25706813532644748220982579)
        ·
          refine ⟨38560220298967122331473869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25706813532644748220982579 38560220298967122331473869)
          ·
            refine ⟨14460082612112670874302701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38560220298967122331473869 14460082612112670874302701)
            ·
              refine ⟨5422530979542251577863513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14460082612112670874302701 5422530979542251577863513)
              ·
                refine ⟨4066898234656688683397635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5422530979542251577863513 4066898234656688683397635)
                ·
                  refine ⟨6100347351985033025096453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4066898234656688683397635 6100347351985033025096453)
                  ·
                    refine ⟨1143815128497193692205585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6100347351985033025096453 1143815128497193692205585)
                    ·
                      rfl

theorem cell23_6682716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_6682716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682716 prefixEnd_6682716 := by exact prefixLift 6682716
  have htrace : WordTrace (prefixWord ++ tailWord_6682716) baseStart_6682716 baseEnd_6682716 := by
    simpa [prefixWord, tailWord_6682716, baseEnd_6682716] using wordTrace_append hprefix tailTrace_6682716
  have hstable : (prefixWord ++ tailWord_6682716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682716).length < 2 ^ (prefixWord ++ tailWord_6682716).sum := by decide
  have hdescent : baseEnd_6682716 < baseStart_6682716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682742 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_6682742 : Nat := 118140960795 + 6682742 * 2 ^ 59
def prefixEnd_6682742 : Nat := 4983230072969 + 3 ^ 40 * 6682742 * 2
def baseEnd_6682742 : Nat := 1143819578662865991630545

theorem tailTrace_6682742 : CollatzResearch.WordTrace tailWord_6682742 prefixEnd_6682742 1143819578662865991630545 := by
  unfold tailWord_6682742
  simp only [CollatzResearch.WordTrace]
  refine ⟨15233726547223408144591655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162493083170383020208977653 15233726547223408144591655)
  ·
    refine ⟨22850589820835112216887483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15233726547223408144591655 22850589820835112216887483)
    ·
      refine ⟨34275884731252668325331225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22850589820835112216887483 34275884731252668325331225)
      ·
        refine ⟨25706913548439501243998419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34275884731252668325331225 25706913548439501243998419)
        ·
          refine ⟨38560370322659251865997629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25706913548439501243998419 38560370322659251865997629)
          ·
            refine ⟨14460138870997219449749111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38560370322659251865997629 14460138870997219449749111)
            ·
              refine ⟨21690208306495829174623667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14460138870997219449749111 21690208306495829174623667)
              ·
                refine ⟨32535312459743743761935501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21690208306495829174623667 32535312459743743761935501)
                ·
                  refine ⟨12200742172403903910725813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32535312459743743761935501 12200742172403903910725813)
                  ·
                    refine ⟨1143819578662865991630545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12200742172403903910725813 1143819578662865991630545)
                    ·
                      rfl

theorem cell23_6682742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_6682742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682742 prefixEnd_6682742 := by exact prefixLift 6682742
  have htrace : WordTrace (prefixWord ++ tailWord_6682742) baseStart_6682742 baseEnd_6682742 := by
    simpa [prefixWord, tailWord_6682742, baseEnd_6682742] using wordTrace_append hprefix tailTrace_6682742
  have hstable : (prefixWord ++ tailWord_6682742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682742).length < 2 ^ (prefixWord ++ tailWord_6682742).sum := by decide
  have hdescent : baseEnd_6682742 < baseStart_6682742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682749 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 2, 3, 2]
def baseStart_6682749 : Nat := 118140960795 + 6682749 * 2 ^ 59
def prefixEnd_6682749 : Nat := 4983230072969 + 3 ^ 40 * 6682749 * 2
def baseEnd_6682749 : Nat := 3431462330353179447504103

theorem tailTrace_6682749 : CollatzResearch.WordTrace tailWord_6682749 prefixEnd_6682749 3431462330353179447504103 := by
  unfold tailWord_6682749
  simp only [CollatzResearch.WordTrace]
  refine ⟨243739880066549170508971301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162493253377699447005980867 243739880066549170508971301)
  ·
    refine ⟨45701227512477969470432119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243739880066549170508971301 45701227512477969470432119)
    ·
      refine ⟨68551841268716954205648179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45701227512477969470432119 68551841268716954205648179)
      ·
        refine ⟨102827761903075431308472269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68551841268716954205648179 102827761903075431308472269)
        ·
          refine ⟨38560410713653286740677101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102827761903075431308472269 38560410713653286740677101)
          ·
            refine ⟨14460154017619982527753913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38560410713653286740677101 14460154017619982527753913)
            ·
              refine ⟨10845115513214986895815435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14460154017619982527753913 10845115513214986895815435)
              ·
                refine ⟨16267673269822480343723153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10845115513214986895815435 16267673269822480343723153)
                ·
                  refine ⟨12200754952366860257792365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16267673269822480343723153 12200754952366860257792365)
                  ·
                    refine ⟨4575283107137572596672137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12200754952366860257792365 4575283107137572596672137)
                    ·
                      refine ⟨3431462330353179447504103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575283107137572596672137 3431462330353179447504103)
                      ·
                        rfl

theorem cell23_6682749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_6682749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682749 prefixEnd_6682749 := by exact prefixLift 6682749
  have htrace : WordTrace (prefixWord ++ tailWord_6682749) baseStart_6682749 baseEnd_6682749 := by
    simpa [prefixWord, tailWord_6682749, baseEnd_6682749] using wordTrace_append hprefix tailTrace_6682749
  have hstable : (prefixWord ++ tailWord_6682749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682749).length < 2 ^ (prefixWord ++ tailWord_6682749).sum := by decide
  have hdescent : baseEnd_6682749 < baseStart_6682749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682755 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 1, 6]
def baseStart_6682755 : Nat := 118140960795 + 6682755 * 2 ^ 59
def prefixEnd_6682755 : Nat := 4983230072969 + 3 ^ 40 * 6682755 * 2
def baseEnd_6682755 : Nat := 1143821803745702141343025

theorem tailTrace_6682755 : CollatzResearch.WordTrace tailWord_6682755 prefixEnd_6682755 1143821803745702141343025 := by
  unfold tailWord_6682755
  simp only [CollatzResearch.WordTrace]
  refine ⟨243740098904527433533689719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162493399269684955689126479 243740098904527433533689719)
  ·
    refine ⟨365610148356791150300534579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243740098904527433533689719 365610148356791150300534579)
    ·
      refine ⟨548415222535186725450801869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365610148356791150300534579 548415222535186725450801869)
      ·
        refine ⟨205655708450695022044050701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548415222535186725450801869 205655708450695022044050701)
        ·
          refine ⟨77120890669010633266519013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205655708450695022044050701 77120890669010633266519013)
          ·
            refine ⟨14460167000439493737472315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77120890669010633266519013 14460167000439493737472315)
            ·
              refine ⟨21690250500659240606208473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14460167000439493737472315 21690250500659240606208473)
              ·
                refine ⟨16267687875494430454656355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21690250500659240606208473 16267687875494430454656355)
                ·
                  refine ⟨24401531813241645681984533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16267687875494430454656355 24401531813241645681984533)
                  ·
                    refine ⟨1143821803745702141343025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24401531813241645681984533 1143821803745702141343025)
                    ·
                      rfl

theorem cell23_6682755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 6].length) (baseStart_6682755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682755 prefixEnd_6682755 := by exact prefixLift 6682755
  have htrace : WordTrace (prefixWord ++ tailWord_6682755) baseStart_6682755 baseEnd_6682755 := by
    simpa [prefixWord, tailWord_6682755, baseEnd_6682755] using wordTrace_append hprefix tailTrace_6682755
  have hstable : (prefixWord ++ tailWord_6682755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682755).length < 2 ^ (prefixWord ++ tailWord_6682755).sum := by decide
  have hdescent : baseEnd_6682755 < baseStart_6682755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682785 : List Nat := [1, 2, 3, 3, 1, 2, 3, 8]
def baseStart_6682785 : Nat := 118140960795 + 6682785 * 2 ^ 59
def prefixEnd_6682785 : Nat := 4983230072969 + 3 ^ 40 * 6682785 * 2
def baseEnd_6682785 : Nat := 127091882061360789135331

theorem tailTrace_6682785 : CollatzResearch.WordTrace tailWord_6682785 prefixEnd_6682785 127091882061360789135331 := by
  unfold tailWord_6682785
  simp only [CollatzResearch.WordTrace]
  refine ⟨243741193094418748657281809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162494128729612499104854539 243741193094418748657281809)
  ·
    refine ⟨182805894820814061492961357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243741193094418748657281809 182805894820814061492961357)
    ·
      refine ⟨68552210557805273059860509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182805894820814061492961357 68552210557805273059860509)
      ·
        refine ⟨25707078959176977397447691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68552210557805273059860509 25707078959176977397447691)
        ·
          refine ⟨38560618438765466096171537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25707078959176977397447691 38560618438765466096171537)
          ·
            refine ⟨28920463829074099572128653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38560618438765466096171537 28920463829074099572128653)
            ·
              refine ⟨10845173935902787339548245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28920463829074099572128653 10845173935902787339548245)
              ·
                refine ⟨127091882061360789135331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10845173935902787339548245 127091882061360789135331)
                ·
                  rfl

theorem cell23_6682785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 8].length) (baseStart_6682785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682785 prefixEnd_6682785 := by exact prefixLift 6682785
  have htrace : WordTrace (prefixWord ++ tailWord_6682785) baseStart_6682785 baseEnd_6682785 := by
    simpa [prefixWord, tailWord_6682785, baseEnd_6682785] using wordTrace_append hprefix tailTrace_6682785
  have hstable : (prefixWord ++ tailWord_6682785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682785).length < 2 ^ (prefixWord ++ tailWord_6682785).sum := by decide
  have hdescent : baseEnd_6682785 < baseStart_6682785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682816 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 1, 2, 3]
def baseStart_6682816 : Nat := 118140960795 + 6682816 * 2 ^ 59
def prefixEnd_6682816 : Nat := 4983230072969 + 3 ^ 40 * 6682816 * 2
def baseEnd_6682816 : Nat := 3431496733557030685366295

theorem tailTrace_6682816 : CollatzResearch.WordTrace tailWord_6682816 prefixEnd_6682816 3431496733557030685366295 := by
  unfold tailWord_6682816
  simp only [CollatzResearch.WordTrace]
  refine ⟨121871161878653220475830151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162494882504870960634440201 121871161878653220475830151)
  ·
    refine ⟨182806742817979830713745227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121871161878653220475830151 182806742817979830713745227)
    ·
      refine ⟨274210114226969746070617841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182806742817979830713745227 274210114226969746070617841)
      ·
        refine ⟨205657585670227309552963381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274210114226969746070617841 205657585670227309552963381)
        ·
          refine ⟨19280398656583810270590317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205657585670227309552963381 19280398656583810270590317)
          ·
            refine ⟨7230149496218928851471369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19280398656583810270590317 7230149496218928851471369)
            ·
              refine ⟨5422612122164196638603527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7230149496218928851471369 5422612122164196638603527)
              ·
                refine ⟨8133918183246294957905291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422612122164196638603527 8133918183246294957905291)
                ·
                  refine ⟨12200877274869442436857937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8133918183246294957905291 12200877274869442436857937)
                  ·
                    refine ⟨9150657956152081827643453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12200877274869442436857937 9150657956152081827643453)
                    ·
                      refine ⟨3431496733557030685366295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9150657956152081827643453 3431496733557030685366295)
                      ·
                        rfl

theorem cell23_6682816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 2, 3].length) (baseStart_6682816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682816 prefixEnd_6682816 := by exact prefixLift 6682816
  have htrace : WordTrace (prefixWord ++ tailWord_6682816) baseStart_6682816 baseEnd_6682816 := by
    simpa [prefixWord, tailWord_6682816, baseEnd_6682816] using wordTrace_append hprefix tailTrace_6682816
  have hstable : (prefixWord ++ tailWord_6682816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682816).length < 2 ^ (prefixWord ++ tailWord_6682816).sum := by decide
  have hdescent : baseEnd_6682816 < baseStart_6682816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682850 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6682850 : Nat := 118140960795 + 6682850 * 2 ^ 59
def prefixEnd_6682850 : Nat := 4983230072969 + 3 ^ 40 * 6682850 * 2
def baseEnd_6682850 : Nat := 3431514191899283552341139

theorem tailTrace_6682850 : CollatzResearch.WordTrace tailWord_6682850 prefixEnd_6682850 3431514191899283552341139 := by
  unfold tailWord_6682850
  simp only [CollatzResearch.WordTrace]
  refine ⟨60935890959795816189599501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162495709226122176505598669 60935890959795816189599501)
  ·
    refine ⟨22850959109923431071099813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60935890959795816189599501 22850959109923431071099813)
    ·
      refine ⟨4284554833110643325831215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22850959109923431071099813 4284554833110643325831215)
      ·
        refine ⟨6426832249665964988746823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4284554833110643325831215 6426832249665964988746823)
        ·
          refine ⟨9640248374498947483120235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6426832249665964988746823 9640248374498947483120235)
          ·
            refine ⟨14460372561748421224680353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9640248374498947483120235 14460372561748421224680353)
            ·
              refine ⟨10845279421311315918510265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14460372561748421224680353 10845279421311315918510265)
              ·
                refine ⟨8133959565983486938882699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10845279421311315918510265 8133959565983486938882699)
                ·
                  refine ⟨12200939348975230408324049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8133959565983486938882699 12200939348975230408324049)
                  ·
                    refine ⟨9150704511731422806243037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12200939348975230408324049 9150704511731422806243037)
                    ·
                      refine ⟨3431514191899283552341139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9150704511731422806243037 3431514191899283552341139)
                      ·
                        rfl

theorem cell23_6682850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6682850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682850 prefixEnd_6682850 := by exact prefixLift 6682850
  have htrace : WordTrace (prefixWord ++ tailWord_6682850) baseStart_6682850 baseEnd_6682850 := by
    simpa [prefixWord, tailWord_6682850, baseEnd_6682850] using wordTrace_append hprefix tailTrace_6682850
  have hstable : (prefixWord ++ tailWord_6682850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682850).length < 2 ^ (prefixWord ++ tailWord_6682850).sum := by decide
  have hdescent : baseEnd_6682850 < baseStart_6682850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682856 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_6682856 : Nat := 118140960795 + 6682856 * 2 ^ 59
def prefixEnd_6682856 : Nat := 4983230072969 + 3 ^ 40 * 6682856 * 2
def baseEnd_6682856 : Nat := 3431517272783210528866111

theorem tailTrace_6682856 : CollatzResearch.WordTrace tailWord_6682856 prefixEnd_6682856 3431517272783210528866111 := by
  unfold tailWord_6682856
  simp only [CollatzResearch.WordTrace]
  refine ⟨121871891338580763891558211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162495855118107685188744281 121871891338580763891558211)
  ·
    refine ⟨182807837007871145837337317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121871891338580763891558211 182807837007871145837337317)
    ·
      refine ⟨34276469438975839844500747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182807837007871145837337317 34276469438975839844500747)
      ·
        refine ⟨51414704158463759766751121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34276469438975839844500747 51414704158463759766751121)
        ·
          refine ⟨38561028118847819825063341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51414704158463759766751121 38561028118847819825063341)
          ·
            refine ⟨14460385544567932434398753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38561028118847819825063341 14460385544567932434398753)
            ·
              refine ⟨10845289158425949325799065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14460385544567932434398753 10845289158425949325799065)
              ·
                refine ⟨8133966868819461994349299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10845289158425949325799065 8133966868819461994349299)
                ·
                  refine ⟨12200950303229192991523949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8133966868819461994349299 12200950303229192991523949)
                  ·
                    refine ⟨4575356363710947371821481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12200950303229192991523949 4575356363710947371821481)
                    ·
                      refine ⟨3431517272783210528866111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575356363710947371821481 3431517272783210528866111)
                      ·
                        rfl

theorem cell23_6682856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_6682856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682856 prefixEnd_6682856 := by exact prefixLift 6682856
  have htrace : WordTrace (prefixWord ++ tailWord_6682856) baseStart_6682856 baseEnd_6682856 := by
    simpa [prefixWord, tailWord_6682856, baseEnd_6682856] using wordTrace_append hprefix tailTrace_6682856
  have hstable : (prefixWord ++ tailWord_6682856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682856).length < 2 ^ (prefixWord ++ tailWord_6682856).sum := by decide
  have hdescent : baseEnd_6682856 < baseStart_6682856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682865 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_6682865 : Nat := 118140960795 + 6682865 * 2 ^ 59
def prefixEnd_6682865 : Nat := 4983230072969 + 3 ^ 40 * 6682865 * 2
def baseEnd_6682865 : Nat := 3431521894109100993653569

theorem tailTrace_6682865 : CollatzResearch.WordTrace tailWord_6682865 prefixEnd_6682865 3431521894109100993653569 := by
  unfold tailWord_6682865
  simp only [CollatzResearch.WordTrace]
  refine ⟨243744110934128922320194049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162496073956085948213462699 243744110934128922320194049)
  ·
    refine ⟨182808083200596691740145537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243744110934128922320194049 182808083200596691740145537)
    ·
      refine ⟨137106062400447518805109153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182808083200596691740145537 137106062400447518805109153)
      ·
        refine ⟨102829546800335639103831865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137106062400447518805109153 102829546800335639103831865)
        ·
          refine ⟨77122160100251729327873899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102829546800335639103831865 77122160100251729327873899)
          ·
            refine ⟨115683240150377593991810849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77122160100251729327873899 115683240150377593991810849)
            ·
              refine ⟨86762430112783195493858137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115683240150377593991810849 86762430112783195493858137)
              ·
                refine ⟨65071822584587396620393603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86762430112783195493858137 65071822584587396620393603)
                ·
                  refine ⟨97607733876881094930590405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65071822584587396620393603 97607733876881094930590405)
                  ·
                    refine ⟨18301450101915205299485701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97607733876881094930590405 18301450101915205299485701)
                    ·
                      refine ⟨3431521894109100993653569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18301450101915205299485701 3431521894109100993653569)
                      ·
                        rfl

theorem cell23_6682865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_6682865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682865 prefixEnd_6682865 := by exact prefixLift 6682865
  have htrace : WordTrace (prefixWord ++ tailWord_6682865) baseStart_6682865 baseEnd_6682865 := by
    simpa [prefixWord, tailWord_6682865, baseEnd_6682865] using wordTrace_append hprefix tailTrace_6682865
  have hstable : (prefixWord ++ tailWord_6682865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682865).length < 2 ^ (prefixWord ++ tailWord_6682865).sum := by decide
  have hdescent : baseEnd_6682865 < baseStart_6682865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682903 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 2, 2, 2]
def baseStart_6682903 : Nat := 118140960795 + 6682903 * 2 ^ 59
def prefixEnd_6682903 : Nat := 4983230072969 + 3 ^ 40 * 6682903 * 2
def baseEnd_6682903 : Nat := 3431541406373971844978395

theorem tailTrace_6682903 : CollatzResearch.WordTrace tailWord_6682903 prefixEnd_6682903 3431541406373971844978395 := by
  unfold tailWord_6682903
  simp only [CollatzResearch.WordTrace]
  refine ⟨243745496907991254810077363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162496997938660836540051575 243745496907991254810077363)
  ·
    refine ⟨365618245361986882215116045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243745496907991254810077363 365618245361986882215116045)
    ·
      refine ⟨137106842010745080830668517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365618245361986882215116045 137106842010745080830668517)
      ·
        refine ⟨25707532877014702655750347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137106842010745080830668517 25707532877014702655750347)
        ·
          refine ⟨38561299315522053983625521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25707532877014702655750347 38561299315522053983625521)
          ·
            refine ⟨28920974486641540487719141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38561299315522053983625521 28920974486641540487719141)
            ·
              refine ⟨5422682716245288841447339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28920974486641540487719141 5422682716245288841447339)
              ·
                refine ⟨8134024074367933262171009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422682716245288841447339 8134024074367933262171009)
                ·
                  refine ⟨6100518055775949946628257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8134024074367933262171009 6100518055775949946628257)
                  ·
                    refine ⟨4575388541831962459971193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6100518055775949946628257 4575388541831962459971193)
                    ·
                      refine ⟨3431541406373971844978395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575388541831962459971193 3431541406373971844978395)
                      ·
                        rfl

theorem cell23_6682903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_6682903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682903 prefixEnd_6682903 := by exact prefixLift 6682903
  have htrace : WordTrace (prefixWord ++ tailWord_6682903) baseStart_6682903 baseEnd_6682903 := by
    simpa [prefixWord, tailWord_6682903, baseEnd_6682903] using wordTrace_append hprefix tailTrace_6682903
  have hstable : (prefixWord ++ tailWord_6682903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682903).length < 2 ^ (prefixWord ++ tailWord_6682903).sum := by decide
  have hdescent : baseEnd_6682903 < baseStart_6682903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682915 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 7]
def baseStart_6682915 : Nat := 118140960795 + 6682915 * 2 ^ 59
def prefixEnd_6682915 : Nat := 4983230072969 + 3 ^ 40 * 6682915 * 2
def baseEnd_6682915 : Nat := 3431547568141825798028339

theorem tailTrace_6682915 : CollatzResearch.WordTrace tailWord_6682915 prefixEnd_6682915 3431547568141825798028339 := by
  unfold tailWord_6682915
  simp only [CollatzResearch.WordTrace]
  refine ⟨243745934583947780859514199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162497289722631853906342799 243745934583947780859514199)
  ·
    refine ⟨365618901875921671289271299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243745934583947780859514199 365618901875921671289271299)
    ·
      refine ⟨548428352813882506933906949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365618901875921671289271299 548428352813882506933906949)
      ·
        refine ⟨102830316152602970050107553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 548428352813882506933906949 102830316152602970050107553)
        ·
          refine ⟨77122737114452227537580665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102830316152602970050107553 77122737114452227537580665)
          ·
            refine ⟨57842052835839170653185499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77122737114452227537580665 57842052835839170653185499)
            ·
              refine ⟨86763079253758755979778249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57842052835839170653185499 86763079253758755979778249)
              ·
                refine ⟨65072309440319066984833687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86763079253758755979778249 65072309440319066984833687)
                ·
                  refine ⟨97608464160478600477250531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65072309440319066984833687 97608464160478600477250531)
                  ·
                    refine ⟨146412696240717900715875797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97608464160478600477250531 146412696240717900715875797)
                    ·
                      refine ⟨3431547568141825798028339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146412696240717900715875797 3431547568141825798028339)
                      ·
                        rfl

theorem cell23_6682915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_6682915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682915 prefixEnd_6682915 := by exact prefixLift 6682915
  have htrace : WordTrace (prefixWord ++ tailWord_6682915) baseStart_6682915 baseEnd_6682915 := by
    simpa [prefixWord, tailWord_6682915, baseEnd_6682915] using wordTrace_append hprefix tailTrace_6682915
  have hstable : (prefixWord ++ tailWord_6682915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682915).length < 2 ^ (prefixWord ++ tailWord_6682915).sum := by decide
  have hdescent : baseEnd_6682915 < baseStart_6682915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682955 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 6]
def baseStart_6682955 : Nat := 118140960795 + 6682955 * 2 ^ 59
def prefixEnd_6682955 : Nat := 4983230072969 + 3 ^ 40 * 6682955 * 2
def baseEnd_6682955 : Nat := 3431568107368005641528155

theorem tailTrace_6682955 : CollatzResearch.WordTrace tailWord_6682955 prefixEnd_6682955 3431568107368005641528155 := by
  unfold tailWord_6682955
  simp only [CollatzResearch.WordTrace]
  refine ⟨243747393503802867690970319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162498262335868578460646879 243747393503802867690970319)
  ·
    refine ⟨365621090255704301536455479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243747393503802867690970319 365621090255704301536455479)
    ·
      refine ⟨548431635383556452304683219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365621090255704301536455479 548431635383556452304683219)
      ·
        refine ⟨822647453075334678457024829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548431635383556452304683219 822647453075334678457024829)
        ·
          refine ⟨308492794903250504421384311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 822647453075334678457024829 308492794903250504421384311)
          ·
            refine ⟨462739192354875756632076467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308492794903250504421384311 462739192354875756632076467)
            ·
              refine ⟨694108788532313634948114701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462739192354875756632076467 694108788532313634948114701)
              ·
                refine ⟨260290795699617613105543013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 694108788532313634948114701 260290795699617613105543013)
                ·
                  refine ⟨48804524193678302457289315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260290795699617613105543013 48804524193678302457289315)
                  ·
                    refine ⟨73206786290517453685933973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48804524193678302457289315 73206786290517453685933973)
                    ·
                      refine ⟨3431568107368005641528155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73206786290517453685933973 3431568107368005641528155)
                      ·
                        rfl

theorem cell23_6682955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_6682955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682955 prefixEnd_6682955 := by exact prefixLift 6682955
  have htrace : WordTrace (prefixWord ++ tailWord_6682955) baseStart_6682955 baseEnd_6682955 := by
    simpa [prefixWord, tailWord_6682955, baseEnd_6682955] using wordTrace_append hprefix tailTrace_6682955
  have hstable : (prefixWord ++ tailWord_6682955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682955).length < 2 ^ (prefixWord ++ tailWord_6682955).sum := by decide
  have hdescent : baseEnd_6682955 < baseStart_6682955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6682976 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 4]
def baseStart_6682976 : Nat := 118140960795 + 6682976 * 2 ^ 59
def prefixEnd_6682976 : Nat := 4983230072969 + 3 ^ 40 * 6682976 * 2
def baseEnd_6682976 : Nat := 3431578890461750059365559

theorem tailTrace_6682976 : CollatzResearch.WordTrace tailWord_6682976 prefixEnd_6682976 3431578890461750059365559 := by
  unfold tailWord_6682976
  simp only [CollatzResearch.WordTrace]
  refine ⟨121874079718363394138742391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162498772957817858851656521 121874079718363394138742391)
  ·
    refine ⟨182811119577545091208113587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121874079718363394138742391 182811119577545091208113587)
    ·
      refine ⟨274216679366317636812170381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182811119577545091208113587 274216679366317636812170381)
      ·
        refine ⟨102831254762369113804563893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274216679366317636812170381 102831254762369113804563893)
        ·
          refine ⟨9640430133972104419177865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102831254762369113804563893 9640430133972104419177865)
          ·
            refine ⟨7230322600479078314383399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9640430133972104419177865 7230322600479078314383399)
            ·
              refine ⟨10845483900718617471575099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7230322600479078314383399 10845483900718617471575099)
              ·
                refine ⟨16268225851077926207362649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10845483900718617471575099 16268225851077926207362649)
                ·
                  refine ⟨12201169388308444655521987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16268225851077926207362649 12201169388308444655521987)
                  ·
                    refine ⟨18301754082462666983282981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12201169388308444655521987 18301754082462666983282981)
                    ·
                      refine ⟨3431578890461750059365559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18301754082462666983282981 3431578890461750059365559)
                      ·
                        rfl

theorem cell23_6682976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_6682976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6682976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6682976 prefixEnd_6682976 := by exact prefixLift 6682976
  have htrace : WordTrace (prefixWord ++ tailWord_6682976) baseStart_6682976 baseEnd_6682976 := by
    simpa [prefixWord, tailWord_6682976, baseEnd_6682976] using wordTrace_append hprefix tailTrace_6682976
  have hstable : (prefixWord ++ tailWord_6682976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6682976).length < 2 ^ (prefixWord ++ tailWord_6682976).sum := by decide
  have hdescent : baseEnd_6682976 < baseStart_6682976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6682976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683019 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 1, 5, 2]
def baseStart_6683019 : Nat := 118140960795 + 6683019 * 2 ^ 59
def prefixEnd_6683019 : Nat := 4983230072969 + 3 ^ 40 * 6683019 * 2
def baseEnd_6683019 : Nat := 3431600970129893391127861

theorem tailTrace_6683019 : CollatzResearch.WordTrace tailWord_6683019 prefixEnd_6683019 3431600970129893391127861 := by
  unfold tailWord_6683019
  simp only [CollatzResearch.WordTrace]
  refine ⟨243749727775571006621300111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162499818517047337747533407 243749727775571006621300111)
  ·
    refine ⟨365624591663356509931950167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243749727775571006621300111 365624591663356509931950167)
    ·
      refine ⟨548436887495034764897925251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365624591663356509931950167 548436887495034764897925251)
      ·
        refine ⟨822655331242552147346887877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548436887495034764897925251 822655331242552147346887877)
        ·
          refine ⟨154247874607978527627541477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 822655331242552147346887877 154247874607978527627541477)
          ·
            refine ⟨28921476488995973930164027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154247874607978527627541477 28921476488995973930164027)
            ·
              refine ⟨43382214733493960895246041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28921476488995973930164027 43382214733493960895246041)
              ·
                refine ⟨32536661050120470671434531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43382214733493960895246041 32536661050120470671434531)
                ·
                  refine ⟨48804991575180706007151797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32536661050120470671434531 48804991575180706007151797)
                  ·
                    refine ⟨4575467960173191188170481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48804991575180706007151797 4575467960173191188170481)
                    ·
                      refine ⟨3431600970129893391127861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575467960173191188170481 3431600970129893391127861)
                      ·
                        rfl

theorem cell23_6683019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 5, 2].length) (baseStart_6683019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683019 prefixEnd_6683019 := by exact prefixLift 6683019
  have htrace : WordTrace (prefixWord ++ tailWord_6683019) baseStart_6683019 baseEnd_6683019 := by
    simpa [prefixWord, tailWord_6683019, baseEnd_6683019] using wordTrace_append hprefix tailTrace_6683019
  have hstable : (prefixWord ++ tailWord_6683019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683019).length < 2 ^ (prefixWord ++ tailWord_6683019).sum := by decide
  have hdescent : baseEnd_6683019 < baseStart_6683019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683043 : List Nat := [1, 1, 1, 4, 1, 4, 3, 3, 1, 1, 3]
def baseStart_6683043 : Nat := 118140960795 + 6683043 * 2 ^ 59
def prefixEnd_6683043 : Nat := 4983230072969 + 3 ^ 40 * 6683043 * 2
def baseEnd_6683043 : Nat := 3431613293665601297227751

theorem tailTrace_6683043 : CollatzResearch.WordTrace tailWord_6683043 prefixEnd_6683043 3431613293665601297227751 := by
  unfold tailWord_6683043
  simp only [CollatzResearch.WordTrace]
  refine ⟨243750603127484058720173783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162500402084989372480115855 243750603127484058720173783)
  ·
    refine ⟨365625904691226088080260675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243750603127484058720173783 365625904691226088080260675)
    ·
      refine ⟨548438857036839132120391013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365625904691226088080260675 548438857036839132120391013)
      ·
        refine ⟨102832285694407337272573315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 548438857036839132120391013 102832285694407337272573315)
        ·
          refine ⟨154248428541611005908859973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102832285694407337272573315 154248428541611005908859973)
          ·
            refine ⟨28921580351552063607911245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154248428541611005908859973 28921580351552063607911245)
            ·
              refine ⟨10845592631832023852966717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28921580351552063607911245 10845592631832023852966717)
              ·
                refine ⟨4067097236937008944862519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10845592631832023852966717 4067097236937008944862519)
                ·
                  refine ⟨6100645855405513417293779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067097236937008944862519 6100645855405513417293779)
                  ·
                    refine ⟨9150968783108270125940669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6100645855405513417293779 9150968783108270125940669)
                    ·
                      refine ⟨3431613293665601297227751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9150968783108270125940669 3431613293665601297227751)
                      ·
                        rfl

theorem cell23_6683043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_6683043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683043 prefixEnd_6683043 := by exact prefixLift 6683043
  have htrace : WordTrace (prefixWord ++ tailWord_6683043) baseStart_6683043 baseEnd_6683043 := by
    simpa [prefixWord, tailWord_6683043, baseEnd_6683043] using wordTrace_append hprefix tailTrace_6683043
  have hstable : (prefixWord ++ tailWord_6683043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683043).length < 2 ^ (prefixWord ++ tailWord_6683043).sum := by decide
  have hdescent : baseEnd_6683043 < baseStart_6683043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683069 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_6683069 : Nat := 118140960795 + 6683069 * 2 ^ 59
def prefixEnd_6683069 : Nat := 4983230072969 + 3 ^ 40 * 6683069 * 2
def baseEnd_6683069 : Nat := 3431626644162618195502631

theorem tailTrace_6683069 : CollatzResearch.WordTrace tailWord_6683069 prefixEnd_6683069 3431626644162618195502631 := by
  unfold tailWord_6683069
  simp only [CollatzResearch.WordTrace]
  refine ⟨243751551425389865160620261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162501034283593243440413507 243751551425389865160620261)
  ·
    refine ⟨45703415892260599717616299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243751551425389865160620261 45703415892260599717616299)
    ·
      refine ⟨68555123838390899576424449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45703415892260599717616299 68555123838390899576424449)
      ·
        refine ⟨51416342878793174682318337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68555123838390899576424449 51416342878793174682318337)
        ·
          refine ⟨38562257159094881011738753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51416342878793174682318337 38562257159094881011738753)
          ·
            refine ⟨28921692869321160758804065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38562257159094881011738753 28921692869321160758804065)
            ·
              refine ⟨21691269651990870569103049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28921692869321160758804065 21691269651990870569103049)
              ·
                refine ⟨16268452238993152926827287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21691269651990870569103049 16268452238993152926827287)
                ·
                  refine ⟨24402678358489729390240931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16268452238993152926827287 24402678358489729390240931)
                  ·
                    refine ⟨36604017537734594085361397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24402678358489729390240931 36604017537734594085361397)
                    ·
                      refine ⟨3431626644162618195502631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36604017537734594085361397 3431626644162618195502631)
                      ·
                        rfl

theorem cell23_6683069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_6683069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683069 prefixEnd_6683069 := by exact prefixLift 6683069
  have htrace : WordTrace (prefixWord ++ tailWord_6683069) baseStart_6683069 baseEnd_6683069 := by
    simpa [prefixWord, tailWord_6683069, baseEnd_6683069] using wordTrace_append hprefix tailTrace_6683069
  have hstable : (prefixWord ++ tailWord_6683069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683069).length < 2 ^ (prefixWord ++ tailWord_6683069).sum := by decide
  have hdescent : baseEnd_6683069 < baseStart_6683069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683103 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 1, 2, 3]
def baseStart_6683103 : Nat := 118140960795 + 6683103 * 2 ^ 59
def prefixEnd_6683103 : Nat := 4983230072969 + 3 ^ 40 * 6683103 * 2
def baseEnd_6683103 : Nat := 3431644102504871062477475

theorem tailTrace_6683103 : CollatzResearch.WordTrace tailWord_6683103 prefixEnd_6683103 3431644102504871062477475 := by
  unfold tailWord_6683103
  simp only [CollatzResearch.WordTrace]
  refine ⟨243752791507266688967357963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162501861004844459311571975 243752791507266688967357963)
  ·
    refine ⟨365629187260900033451036945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243752791507266688967357963 365629187260900033451036945)
    ·
      refine ⟨274221890445675025088277709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365629187260900033451036945 274221890445675025088277709)
      ·
        refine ⟨102833208917128134408104141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274221890445675025088277709 102833208917128134408104141)
        ·
          refine ⟨38562453343923050403039053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102833208917128134408104141 38562453343923050403039053)
          ·
            refine ⟨14460920003971143901139645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38562453343923050403039053 14460920003971143901139645)
            ·
              refine ⟨5422845001489178962927367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14460920003971143901139645 5422845001489178962927367)
              ·
                refine ⟨8134267502233768444391051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422845001489178962927367 8134267502233768444391051)
                ·
                  refine ⟨12201401253350652666586577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8134267502233768444391051 12201401253350652666586577)
                  ·
                    refine ⟨9151050940012989499939933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12201401253350652666586577 9151050940012989499939933)
                    ·
                      refine ⟨3431644102504871062477475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9151050940012989499939933 3431644102504871062477475)
                      ·
                        rfl

theorem cell23_6683103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_6683103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683103 prefixEnd_6683103 := by exact prefixLift 6683103
  have htrace : WordTrace (prefixWord ++ tailWord_6683103) baseStart_6683103 baseEnd_6683103 := by
    simpa [prefixWord, tailWord_6683103, baseEnd_6683103] using wordTrace_append hprefix tailTrace_6683103
  have hstable : (prefixWord ++ tailWord_6683103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683103).length < 2 ^ (prefixWord ++ tailWord_6683103).sum := by decide
  have hdescent : baseEnd_6683103 < baseStart_6683103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683106 : List Nat := [3, 3, 3, 2, 1, 11]
def baseStart_6683106 : Nat := 118140960795 + 6683106 * 2 ^ 59
def prefixEnd_6683106 : Nat := 4983230072969 + 3 ^ 40 * 6683106 * 2
def baseEnd_6683106 : Nat := 14121998530645409673827

theorem tailTrace_6683106 : CollatzResearch.WordTrace tailWord_6683106 prefixEnd_6683106 14121998530645409673827 := by
  unfold tailWord_6683106
  simp only [CollatzResearch.WordTrace]
  refine ⟨60938225231563955119929293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162501933950837213653144781 60938225231563955119929293)
  ·
    refine ⟨22851834461836483169973485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60938225231563955119929293 22851834461836483169973485)
    ·
      refine ⟨8569437923188681188740057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22851834461836483169973485 8569437923188681188740057)
      ·
        refine ⟨6427078442391510891555043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8569437923188681188740057 6427078442391510891555043)
        ·
          refine ⟨9640617663587266337332565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6427078442391510891555043 9640617663587266337332565)
          ·
            refine ⟨14121998530645409673827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9640617663587266337332565 14121998530645409673827)
            ·
              rfl

theorem cell23_6683106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 11].length) (baseStart_6683106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683106 prefixEnd_6683106 := by exact prefixLift 6683106
  have htrace : WordTrace (prefixWord ++ tailWord_6683106) baseStart_6683106 baseEnd_6683106 := by
    simpa [prefixWord, tailWord_6683106, baseEnd_6683106] using wordTrace_append hprefix tailTrace_6683106
  have hstable : (prefixWord ++ tailWord_6683106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683106).length < 2 ^ (prefixWord ++ tailWord_6683106).sum := by decide
  have hdescent : baseEnd_6683106 < baseStart_6683106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683117 : List Nat := [1, 5, 1, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_6683117 : Nat := 118140960795 + 6683117 * 2 ^ 59
def prefixEnd_6683117 : Nat := 4983230072969 + 3 ^ 40 * 6683117 * 2
def baseEnd_6683117 : Nat := 3431651291234034007702411

theorem tailTrace_6683117 : CollatzResearch.WordTrace tailWord_6683117 prefixEnd_6683117 3431651291234034007702411 := by
  unfold tailWord_6683117
  simp only [CollatzResearch.WordTrace]
  refine ⟨243753302129215969358367605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162502201419477312905578403 243753302129215969358367605)
  ·
    refine ⟨22851872074613997127346963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243753302129215969358367605 22851872074613997127346963)
    ·
      refine ⟨34277808111920995691020445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22851872074613997127346963 34277808111920995691020445)
      ·
        refine ⟨12854178041970373384132667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34277808111920995691020445 12854178041970373384132667)
        ·
          refine ⟨19281267062955560076199001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12854178041970373384132667 19281267062955560076199001)
          ·
            refine ⟨14460950297216670057149251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19281267062955560076199001 14460950297216670057149251)
            ·
              refine ⟨21691425445825005085723877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14460950297216670057149251 21691425445825005085723877)
              ·
                refine ⟨4067142271092188453573227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21691425445825005085723877 4067142271092188453573227)
                ·
                  refine ⟨6100713406638282680359841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067142271092188453573227 6100713406638282680359841)
                  ·
                    refine ⟨4575535054978712010269881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6100713406638282680359841 4575535054978712010269881)
                    ·
                      refine ⟨3431651291234034007702411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575535054978712010269881 3431651291234034007702411)
                      ·
                        rfl

theorem cell23_6683117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_6683117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683117 prefixEnd_6683117 := by exact prefixLift 6683117
  have htrace : WordTrace (prefixWord ++ tailWord_6683117) baseStart_6683117 baseEnd_6683117 := by
    simpa [prefixWord, tailWord_6683117, baseEnd_6683117] using wordTrace_append hprefix tailTrace_6683117
  have hstable : (prefixWord ++ tailWord_6683117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683117).length < 2 ^ (prefixWord ++ tailWord_6683117).sum := by decide
  have hdescent : baseEnd_6683117 < baseStart_6683117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683152 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_6683152 : Nat := 118140960795 + 6683152 * 2 ^ 59
def prefixEnd_6683152 : Nat := 4983230072969 + 3 ^ 40 * 6683152 * 2
def baseEnd_6683152 : Nat := 3431669263056941370764749

theorem tailTrace_6683152 : CollatzResearch.WordTrace tailWord_6683152 prefixEnd_6683152 3431669263056941370764749 := by
  unfold tailWord_6683152
  simp only [CollatzResearch.WordTrace]
  refine ⟨121877289342044585167945855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162503052456059446890594473 121877289342044585167945855)
  ·
    refine ⟨182815934013066877751918783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121877289342044585167945855 182815934013066877751918783)
    ·
      refine ⟨274223901019600316627878175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182815934013066877751918783 274223901019600316627878175)
      ·
        refine ⟨411335851529400474941817263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274223901019600316627878175 411335851529400474941817263)
        ·
          refine ⟨617003777294100712412725895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411335851529400474941817263 617003777294100712412725895)
          ·
            refine ⟨925505665941151068619088843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617003777294100712412725895 925505665941151068619088843)
            ·
              refine ⟨1388258498911726602928633265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925505665941151068619088843 1388258498911726602928633265)
              ·
                refine ⟨1041193874183794952196474949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1388258498911726602928633265 1041193874183794952196474949)
                ·
                  refine ⟨195223851409461553536839053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1041193874183794952196474949 195223851409461553536839053)
                  ·
                    refine ⟨73208944278548082576314645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195223851409461553536839053 73208944278548082576314645)
                    ·
                      refine ⟨3431669263056941370764749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73208944278548082576314645 3431669263056941370764749)
                      ·
                        rfl

theorem cell23_6683152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_6683152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683152 prefixEnd_6683152 := by exact prefixLift 6683152
  have htrace : WordTrace (prefixWord ++ tailWord_6683152) baseStart_6683152 baseEnd_6683152 := by
    simpa [prefixWord, tailWord_6683152, baseEnd_6683152] using wordTrace_append hprefix tailTrace_6683152
  have hstable : (prefixWord ++ tailWord_6683152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683152).length < 2 ^ (prefixWord ++ tailWord_6683152).sum := by decide
  have hdescent : baseEnd_6683152 < baseStart_6683152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683160 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 1, 3, 2]
def baseStart_6683160 : Nat := 118140960795 + 6683160 * 2 ^ 59
def prefixEnd_6683160 : Nat := 4983230072969 + 3 ^ 40 * 6683160 * 2
def baseEnd_6683160 : Nat := 3431673370902177339464713

theorem tailTrace_6683160 : CollatzResearch.WordTrace tailWord_6683160 prefixEnd_6683160 3431673370902177339464713 := by
  unfold tailWord_6683160
  simp only [CollatzResearch.WordTrace]
  refine ⟨121877435234030093851091467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162503246978706791801455289 121877435234030093851091467)
  ·
    refine ⟨182816152851045140776637201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121877435234030093851091467 182816152851045140776637201)
    ·
      refine ⟨137112114638283855582477901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182816152851045140776637201 137112114638283855582477901)
      ·
        refine ⟨51417042989356445843429213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137112114638283855582477901 51417042989356445843429213)
        ·
          refine ⟨19281391121008667191285955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51417042989356445843429213 19281391121008667191285955)
          ·
            refine ⟨28922086681513000786928933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19281391121008667191285955 28922086681513000786928933)
            ·
              refine ⟨5422891252783687647549175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28922086681513000786928933 5422891252783687647549175)
              ·
                refine ⟨8134336879175531471323763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5422891252783687647549175 8134336879175531471323763)
                ·
                  refine ⟨12201505318763297206985645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8134336879175531471323763 12201505318763297206985645)
                  ·
                    refine ⟨4575564494536236452619617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12201505318763297206985645 4575564494536236452619617)
                    ·
                      refine ⟨3431673370902177339464713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575564494536236452619617 3431673370902177339464713)
                      ·
                        rfl

theorem cell23_6683160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_6683160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683160 prefixEnd_6683160 := by exact prefixLift 6683160
  have htrace : WordTrace (prefixWord ++ tailWord_6683160) baseStart_6683160 baseEnd_6683160 := by
    simpa [prefixWord, tailWord_6683160, baseEnd_6683160] using wordTrace_append hprefix tailTrace_6683160
  have hstable : (prefixWord ++ tailWord_6683160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683160).length < 2 ^ (prefixWord ++ tailWord_6683160).sum := by decide
  have hdescent : baseEnd_6683160 < baseStart_6683160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683169 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_6683169 : Nat := 118140960795 + 6683169 * 2 ^ 59
def prefixEnd_6683169 : Nat := 4983230072969 + 3 ^ 40 * 6683169 * 2
def baseEnd_6683169 : Nat := 3431677992228067804252171

theorem tailTrace_6683169 : CollatzResearch.WordTrace tailWord_6683169 prefixEnd_6683169 3431677992228067804252171 := by
  unfold tailWord_6683169
  simp only [CollatzResearch.WordTrace]
  refine ⟨243755198725027582239260561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162503465816685054826173707 243755198725027582239260561)
  ·
    refine ⟨182816399043770686679445421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243755198725027582239260561 182816399043770686679445421)
    ·
      refine ⟨68556149641414007504792033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182816399043770686679445421 68556149641414007504792033)
      ·
        refine ⟨51417112231060505628594025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68556149641414007504792033 51417112231060505628594025)
        ·
          refine ⟨38562834173295379221445519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51417112231060505628594025 38562834173295379221445519)
          ·
            refine ⟨57844251259943068832168279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38562834173295379221445519 57844251259943068832168279)
            ·
              refine ⟨86766376889914603248252419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57844251259943068832168279 86766376889914603248252419)
              ·
                refine ⟨130149565334871904872378629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86766376889914603248252419 130149565334871904872378629)
                ·
                  refine ⟨24403043500288482163570993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130149565334871904872378629 24403043500288482163570993)
                  ·
                    refine ⟨18302282625216361622678245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24403043500288482163570993 18302282625216361622678245)
                    ·
                      refine ⟨3431677992228067804252171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18302282625216361622678245 3431677992228067804252171)
                      ·
                        rfl

theorem cell23_6683169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_6683169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683169 prefixEnd_6683169 := by exact prefixLift 6683169
  have htrace : WordTrace (prefixWord ++ tailWord_6683169) baseStart_6683169 baseEnd_6683169 := by
    simpa [prefixWord, tailWord_6683169, baseEnd_6683169] using wordTrace_append hprefix tailTrace_6683169
  have hstable : (prefixWord ++ tailWord_6683169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683169).length < 2 ^ (prefixWord ++ tailWord_6683169).sum := by decide
  have hdescent : baseEnd_6683169 < baseStart_6683169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683190 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_6683190 : Nat := 118140960795 + 6683190 * 2 ^ 59
def prefixEnd_6683190 : Nat := 4983230072969 + 3 ^ 40 * 6683190 * 2
def baseEnd_6683190 : Nat := 3431688775321812222089575

theorem tailTrace_6683190 : CollatzResearch.WordTrace tailWord_6683190 prefixEnd_6683190 3431688775321812222089575 := by
  unfold tailWord_6683190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15234747791121968926610939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162503976438634335217183349 15234747791121968926610939)
  ·
    refine ⟨22852121686682953389916409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15234747791121968926610939 22852121686682953389916409)
    ·
      refine ⟨17139091265012215042437307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22852121686682953389916409 17139091265012215042437307)
      ·
        refine ⟨25708636897518322563655961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17139091265012215042437307 25708636897518322563655961)
        ·
          refine ⟨19281477673138741922741971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25708636897518322563655961 19281477673138741922741971)
          ·
            refine ⟨28922216509708112884112957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19281477673138741922741971 28922216509708112884112957)
            ·
              refine ⟨10845831191140542331542359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28922216509708112884112957 10845831191140542331542359)
              ·
                refine ⟨16268746786710813497313539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10845831191140542331542359 16268746786710813497313539)
                ·
                  refine ⟨24403120180066220245970309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16268746786710813497313539 24403120180066220245970309)
                  ·
                    refine ⟨4575585033762416296119433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24403120180066220245970309 4575585033762416296119433)
                    ·
                      refine ⟨3431688775321812222089575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575585033762416296119433 3431688775321812222089575)
                      ·
                        rfl

theorem cell23_6683190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_6683190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683190 prefixEnd_6683190 := by exact prefixLift 6683190
  have htrace : WordTrace (prefixWord ++ tailWord_6683190) baseStart_6683190 baseEnd_6683190 := by
    simpa [prefixWord, tailWord_6683190, baseEnd_6683190] using wordTrace_append hprefix tailTrace_6683190
  have hstable : (prefixWord ++ tailWord_6683190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683190).length < 2 ^ (prefixWord ++ tailWord_6683190).sum := by decide
  have hdescent : baseEnd_6683190 < baseStart_6683190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683273 : List Nat := [1, 2, 1, 1, 4, 1, 1, 7, 1, 4]
def baseStart_6683273 : Nat := 118140960795 + 6683273 * 2 ^ 59
def prefixEnd_6683273 : Nat := 4983230072969 + 3 ^ 40 * 6683273 * 2
def baseEnd_6683273 : Nat := 1143910464738711799117231

theorem tailTrace_6683273 : CollatzResearch.WordTrace tailWord_6683273 prefixEnd_6683273 1143910464738711799117231 := by
  unfold tailWord_6683273
  simp only [CollatzResearch.WordTrace]
  refine ⟨243758991916650808001046473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162505994611100538667364315 243758991916650808001046473)
  ·
    refine ⟨182819243937488106000784855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243758991916650808001046473 182819243937488106000784855)
    ·
      refine ⟨274228865906232159001177283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182819243937488106000784855 274228865906232159001177283)
      ·
        refine ⟨411343298859348238501765925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274228865906232159001177283 411343298859348238501765925)
        ·
          refine ⟨77126868536127794719081111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 411343298859348238501765925 77126868536127794719081111)
          ·
            refine ⟨115690302804191692078621667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77126868536127794719081111 115690302804191692078621667)
            ·
              refine ⟨173535454206287538117932501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115690302804191692078621667 173535454206287538117932501)
              ·
                refine ⟨4067237207959864174639043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 173535454206287538117932501 4067237207959864174639043)
                ·
                  refine ⟨6100855811939796261958565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067237207959864174639043 6100855811939796261958565)
                  ·
                    refine ⟨1143910464738711799117231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6100855811939796261958565 1143910464738711799117231)
                    ·
                      rfl

theorem cell23_6683273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 1, 4].length) (baseStart_6683273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683273 prefixEnd_6683273 := by exact prefixLift 6683273
  have htrace : WordTrace (prefixWord ++ tailWord_6683273) baseStart_6683273 baseEnd_6683273 := by
    simpa [prefixWord, tailWord_6683273, baseEnd_6683273] using wordTrace_append hprefix tailTrace_6683273
  have hstable : (prefixWord ++ tailWord_6683273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683273).length < 2 ^ (prefixWord ++ tailWord_6683273).sum := by decide
  have hdescent : baseEnd_6683273 < baseStart_6683273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683289 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_6683289 : Nat := 118140960795 + 6683289 * 2 ^ 59
def prefixEnd_6683289 : Nat := 4983230072969 + 3 ^ 40 * 6683289 * 2
def baseEnd_6683289 : Nat := 3431739609906607334751619

theorem tailTrace_6683289 : CollatzResearch.WordTrace tailWord_6683289 prefixEnd_6683289 3431739609906607334751619 := by
  unfold tailWord_6683289
  simp only [CollatzResearch.WordTrace]
  refine ⟨243759575484592842733628921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162506383656395228489085947 243759575484592842733628921)
  ·
    refine ⟨182819681613444632050221691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243759575484592842733628921 182819681613444632050221691)
    ·
      refine ⟨274229522420166948075332537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182819681613444632050221691 274229522420166948075332537)
      ·
        refine ⟨205672141815125211056499403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274229522420166948075332537 205672141815125211056499403)
        ·
          refine ⟨308508212722687816584749105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205672141815125211056499403 308508212722687816584749105)
          ·
            refine ⟨231381159542015862438561829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308508212722687816584749105 231381159542015862438561829)
            ·
              refine ⟨43383967414127974207230343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231381159542015862438561829 43383967414127974207230343)
              ·
                refine ⟨65075951121191961310845515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43383967414127974207230343 65075951121191961310845515)
                ·
                  refine ⟨97613926681787941966268273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65075951121191961310845515 97613926681787941966268273)
                  ·
                    refine ⟨73210445011340956474701205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97613926681787941966268273 73210445011340956474701205)
                    ·
                      refine ⟨3431739609906607334751619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73210445011340956474701205 3431739609906607334751619)
                      ·
                        rfl

theorem cell23_6683289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_6683289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683289 prefixEnd_6683289 := by exact prefixLift 6683289
  have htrace : WordTrace (prefixWord ++ tailWord_6683289) baseStart_6683289 baseEnd_6683289 := by
    simpa [prefixWord, tailWord_6683289, baseEnd_6683289] using wordTrace_append hprefix tailTrace_6683289
  have hstable : (prefixWord ++ tailWord_6683289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683289).length < 2 ^ (prefixWord ++ tailWord_6683289).sum := by decide
  have hdescent : baseEnd_6683289 < baseStart_6683289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683363 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 1, 6]
def baseStart_6683363 : Nat := 118140960795 + 6683363 * 2 ^ 59
def prefixEnd_6683363 : Nat := 4983230072969 + 3 ^ 40 * 6683363 * 2
def baseEnd_6683363 : Nat := 1143925869158346681742093

theorem tailTrace_6683363 : CollatzResearch.WordTrace tailWord_6683363 prefixEnd_6683363 1143925869158346681742093 := by
  unfold tailWord_6683363
  simp only [CollatzResearch.WordTrace]
  refine ⟨243762274486324753371822743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162508182990883168914548495 243762274486324753371822743)
  ·
    refine ⟨365643411729487130057734115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243762274486324753371822743 365643411729487130057734115)
    ·
      refine ⟨548465117594230695086601173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365643411729487130057734115 548465117594230695086601173)
      ·
        refine ⟨12854651193614781916092215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 548465117594230695086601173 12854651193614781916092215)
        ·
          refine ⟨19281976790422172874138323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12854651193614781916092215 19281976790422172874138323)
          ·
            refine ⟨28922965185633259311207485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19281976790422172874138323 28922965185633259311207485)
            ·
              refine ⟨10846111944612472241702807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28922965185633259311207485 10846111944612472241702807)
              ·
                refine ⟨16269167916918708362554211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10846111944612472241702807 16269167916918708362554211)
                ·
                  refine ⟨24403751875378062543831317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16269167916918708362554211 24403751875378062543831317)
                  ·
                    refine ⟨1143925869158346681742093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24403751875378062543831317 1143925869158346681742093)
                    ·
                      rfl

theorem cell23_6683363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 6].length) (baseStart_6683363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683363 prefixEnd_6683363 := by exact prefixLift 6683363
  have htrace : WordTrace (prefixWord ++ tailWord_6683363) baseStart_6683363 baseEnd_6683363 := by
    simpa [prefixWord, tailWord_6683363, baseEnd_6683363] using wordTrace_append hprefix tailTrace_6683363
  have hstable : (prefixWord ++ tailWord_6683363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683363).length < 2 ^ (prefixWord ++ tailWord_6683363).sum := by decide
  have hdescent : baseEnd_6683363 < baseStart_6683363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683390 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_6683390 : Nat := 118140960795 + 6683390 * 2 ^ 59
def prefixEnd_6683390 : Nat := 4983230072969 + 3 ^ 40 * 6683390 * 2
def baseEnd_6683390 : Nat := 3431791471452711439588655

theorem tailTrace_6683390 : CollatzResearch.WordTrace tailWord_6683390 prefixEnd_6683390 3431791471452711439588655 := by
  unfold tailWord_6683390
  simp only [CollatzResearch.WordTrace]
  refine ⟨30470407407153367122881953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162508839504817957988703749 30470407407153367122881953)
  ·
    refine ⟨22852805555365025342161465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30470407407153367122881953 22852805555365025342161465)
    ·
      refine ⟨17139604166523769006621099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22852805555365025342161465 17139604166523769006621099)
      ·
        refine ⟨25709406249785653509931649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17139604166523769006621099 25709406249785653509931649)
        ·
          refine ⟨19282054687339240132448737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25709406249785653509931649 19282054687339240132448737)
          ·
            refine ⟨14461541015504430099336553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19282054687339240132448737 14461541015504430099336553)
            ·
              refine ⟨10846155761628322574502415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14461541015504430099336553 10846155761628322574502415)
              ·
                refine ⟨16269233642442483861753623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10846155761628322574502415 16269233642442483861753623)
                ·
                  refine ⟨24403850463663725792630435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16269233642442483861753623 24403850463663725792630435)
                  ·
                    refine ⟨36605775695495588688945653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24403850463663725792630435 36605775695495588688945653)
                    ·
                      refine ⟨3431791471452711439588655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36605775695495588688945653 3431791471452711439588655)
                      ·
                        rfl

theorem cell23_6683390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_6683390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683390 prefixEnd_6683390 := by exact prefixLift 6683390
  have htrace : WordTrace (prefixWord ++ tailWord_6683390) baseStart_6683390 baseEnd_6683390 := by
    simpa [prefixWord, tailWord_6683390, baseEnd_6683390] using wordTrace_append hprefix tailTrace_6683390
  have hstable : (prefixWord ++ tailWord_6683390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683390).length < 2 ^ (prefixWord ++ tailWord_6683390).sum := by decide
  have hdescent : baseEnd_6683390 < baseStart_6683390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683406 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_6683406 : Nat := 118140960795 + 6683406 * 2 ^ 59
def prefixEnd_6683406 : Nat := 4983230072969 + 3 ^ 40 * 6683406 * 2
def baseEnd_6683406 : Nat := 1143933229047727792329527

theorem tailTrace_6683406 : CollatzResearch.WordTrace tailWord_6683406 prefixEnd_6683406 1143933229047727792329527 := by
  unfold tailWord_6683406
  simp only [CollatzResearch.WordTrace]
  refine ⟨30470480353146121464454759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162509228550112647810425381 30470480353146121464454759)
  ·
    refine ⟨45705720529719182196682139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30470480353146121464454759 45705720529719182196682139)
    ·
      refine ⟨68558580794578773295023209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45705720529719182196682139 68558580794578773295023209)
      ·
        refine ⟨51418935595934079971267407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68558580794578773295023209 51418935595934079971267407)
        ·
          refine ⟨77128403393901119956901111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51418935595934079971267407 77128403393901119956901111)
          ·
            refine ⟨115692605090851679935351667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77128403393901119956901111 115692605090851679935351667)
            ·
              refine ⟨173538907636277519903027501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115692605090851679935351667 173538907636277519903027501)
              ·
                refine ⟨65077090363604069963635313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173538907636277519903027501 65077090363604069963635313)
                ·
                  refine ⟨48807817772703052472726485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65077090363604069963635313 48807817772703052472726485)
                  ·
                    refine ⟨1143933229047727792329527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48807817772703052472726485 1143933229047727792329527)
                    ·
                      rfl

theorem cell23_6683406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_6683406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683406 prefixEnd_6683406 := by exact prefixLift 6683406
  have htrace : WordTrace (prefixWord ++ tailWord_6683406) baseStart_6683406 baseEnd_6683406 := by
    simpa [prefixWord, tailWord_6683406, baseEnd_6683406] using wordTrace_append hprefix tailTrace_6683406
  have hstable : (prefixWord ++ tailWord_6683406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683406).length < 2 ^ (prefixWord ++ tailWord_6683406).sum := by decide
  have hdescent : baseEnd_6683406 < baseStart_6683406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683410 : List Nat := [3, 2, 4, 1, 2, 1, 2, 8]
def baseStart_6683410 : Nat := 118140960795 + 6683410 * 2 ^ 59
def prefixEnd_6683410 : Nat := 4983230072969 + 3 ^ 40 * 6683410 * 2
def baseEnd_6683410 : Nat := 127103768187622272642169

theorem tailTrace_6683410 : CollatzResearch.WordTrace tailWord_6683410 prefixEnd_6683410 127103768187622272642169 := by
  unfold tailWord_6683410
  simp only [CollatzResearch.WordTrace]
  refine ⟨60940997179288620099695921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162509325811436320265855789 60940997179288620099695921)
  ·
    refine ⟨45705747884466465074771941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60940997179288620099695921 45705747884466465074771941)
    ·
      refine ⟨8569827728337462201519739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45705747884466465074771941 8569827728337462201519739)
      ·
        refine ⟨12854741592506193302279609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8569827728337462201519739 12854741592506193302279609)
        ·
          refine ⟨9641056194379644976709707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12854741592506193302279609 9641056194379644976709707)
          ·
            refine ⟨14461584291569467465064561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9641056194379644976709707 14461584291569467465064561)
            ·
              refine ⟨10846188218677100598798421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14461584291569467465064561 10846188218677100598798421)
              ·
                refine ⟨127103768187622272642169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10846188218677100598798421 127103768187622272642169)
                ·
                  rfl

theorem cell23_6683410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 8].length) (baseStart_6683410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683410 prefixEnd_6683410 := by exact prefixLift 6683410
  have htrace : WordTrace (prefixWord ++ tailWord_6683410) baseStart_6683410 baseEnd_6683410 := by
    simpa [prefixWord, tailWord_6683410, baseEnd_6683410] using wordTrace_append hprefix tailTrace_6683410
  have hstable : (prefixWord ++ tailWord_6683410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683410).length < 2 ^ (prefixWord ++ tailWord_6683410).sum := by decide
  have hdescent : baseEnd_6683410 < baseStart_6683410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683447 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 1, 3, 2]
def baseStart_6683447 : Nat := 118140960795 + 6683447 * 2 ^ 59
def prefixEnd_6683447 : Nat := 4983230072969 + 3 ^ 40 * 6683447 * 2
def baseEnd_6683447 : Nat := 3431820739850017716575893

theorem tailTrace_6683447 : CollatzResearch.WordTrace tailWord_6683447 prefixEnd_6683447 3431820739850017716575893 := by
  unfold tailWord_6683447
  simp only [CollatzResearch.WordTrace]
  refine ⟨243765338218020435717880595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162510225478680290478587063 243765338218020435717880595)
  ·
    refine ⟨365648007327030653576820893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243765338218020435717880595 365648007327030653576820893)
    ·
      refine ⟨137118002747636495091307835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365648007327030653576820893 137118002747636495091307835)
      ·
        refine ⟨205677004121454742636961753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137118002747636495091307835 205677004121454742636961753)
        ·
          refine ⟨154257753091091056977721315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205677004121454742636961753 154257753091091056977721315)
          ·
            refine ⟨231386629636636585466581973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154257753091091056977721315 231386629636636585466581973)
            ·
              refine ⟨5423124132108669971873015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 231386629636636585466581973 5423124132108669971873015)
              ·
                refine ⟨8134686198163004957809523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5423124132108669971873015 8134686198163004957809523)
                ·
                  refine ⟨12202029297244507436714285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8134686198163004957809523 12202029297244507436714285)
                  ·
                    refine ⟨4575760986466690288767857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12202029297244507436714285 4575760986466690288767857)
                    ·
                      refine ⟨3431820739850017716575893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575760986466690288767857 3431820739850017716575893)
                      ·
                        rfl

theorem cell23_6683447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 3, 2].length) (baseStart_6683447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683447 prefixEnd_6683447 := by exact prefixLift 6683447
  have htrace : WordTrace (prefixWord ++ tailWord_6683447) baseStart_6683447 baseEnd_6683447 := by
    simpa [prefixWord, tailWord_6683447, baseEnd_6683447] using wordTrace_append hprefix tailTrace_6683447
  have hstable : (prefixWord ++ tailWord_6683447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683447).length < 2 ^ (prefixWord ++ tailWord_6683447).sum := by decide
  have hdescent : baseEnd_6683447 < baseStart_6683447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683454 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_6683454 : Nat := 118140960795 + 6683454 * 2 ^ 59
def prefixEnd_6683454 : Nat := 4983230072969 + 3 ^ 40 * 6683454 * 2
def baseEnd_6683454 : Nat := 3431824334214599189188361

theorem tailTrace_6683454 : CollatzResearch.WordTrace tailWord_6683454 prefixEnd_6683454 3431824334214599189188361 := by
  unfold tailWord_6683454
  simp only [CollatzResearch.WordTrace]
  refine ⟨30470699191124384489173177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162510395685996717275590277 30470699191124384489173177)
  ·
    refine ⟨22853024393343288366879883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30470699191124384489173177 22853024393343288366879883)
    ·
      refine ⟨34279536590014932550319825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22853024393343288366879883 34279536590014932550319825)
      ·
        refine ⟨25709652442511199412739869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34279536590014932550319825 25709652442511199412739869)
        ·
          refine ⟨9641119665941699779777451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25709652442511199412739869 9641119665941699779777451)
          ·
            refine ⟨14461679498912549669666177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9641119665941699779777451 14461679498912549669666177)
            ·
              refine ⟨10846259624184412252249633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14461679498912549669666177 10846259624184412252249633)
              ·
                refine ⟨8134694718138309189187225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10846259624184412252249633 8134694718138309189187225)
                ·
                  refine ⟨6101021038603731891890419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8134694718138309189187225 6101021038603731891890419)
                  ·
                    refine ⟨9151531557905597837835629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6101021038603731891890419 9151531557905597837835629)
                    ·
                      refine ⟨3431824334214599189188361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9151531557905597837835629 3431824334214599189188361)
                      ·
                        rfl

theorem cell23_6683454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_6683454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683454 prefixEnd_6683454 := by exact prefixLift 6683454
  have htrace : WordTrace (prefixWord ++ tailWord_6683454) baseStart_6683454 baseEnd_6683454 := by
    simpa [prefixWord, tailWord_6683454, baseEnd_6683454] using wordTrace_append hprefix tailTrace_6683454
  have hstable : (prefixWord ++ tailWord_6683454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683454).length < 2 ^ (prefixWord ++ tailWord_6683454).sum := by decide
  have hdescent : baseEnd_6683454 < baseStart_6683454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683456 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 4]
def baseStart_6683456 : Nat := 118140960795 + 6683456 * 2 ^ 59
def prefixEnd_6683456 : Nat := 4983230072969 + 3 ^ 40 * 6683456 * 2
def baseEnd_6683456 : Nat := 3431825361175908181363351

theorem tailTrace_6683456 : CollatzResearch.WordTrace tailWord_6683456 prefixEnd_6683456 3431825361175908181363351 := by
  unfold tailWord_6683456
  simp only [CollatzResearch.WordTrace]
  refine ⟨121882833237493915127479111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162510444316658553503305481 121882833237493915127479111)
  ·
    refine ⟨182824249856240872691218667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121882833237493915127479111 182824249856240872691218667)
    ·
      refine ⟨274236374784361309036828001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182824249856240872691218667 274236374784361309036828001)
      ·
        refine ⟨205677281088270981777621001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274236374784361309036828001 205677281088270981777621001)
        ·
          refine ⟨154257960816203236333215751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205677281088270981777621001 154257960816203236333215751)
          ·
            refine ⟨231386941224304854499823627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154257960816203236333215751 231386941224304854499823627)
            ·
              refine ⟨347080411836457281749735441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231386941224304854499823627 347080411836457281749735441)
              ·
                refine ⟨260310308877342961312301581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347080411836457281749735441 260310308877342961312301581)
                ·
                  refine ⟨97616365829003610492113093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260310308877342961312301581 97616365829003610492113093)
                  ·
                    refine ⟨18303068592938176967271205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97616365829003610492113093 18303068592938176967271205)
                    ·
                      refine ⟨3431825361175908181363351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18303068592938176967271205 3431825361175908181363351)
                      ·
                        rfl

theorem cell23_6683456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_6683456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683456 prefixEnd_6683456 := by exact prefixLift 6683456
  have htrace : WordTrace (prefixWord ++ tailWord_6683456) baseStart_6683456 baseEnd_6683456 := by
    simpa [prefixWord, tailWord_6683456, baseEnd_6683456] using wordTrace_append hprefix tailTrace_6683456
  have hstable : (prefixWord ++ tailWord_6683456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683456).length < 2 ^ (prefixWord ++ tailWord_6683456).sum := by decide
  have hdescent : baseEnd_6683456 < baseStart_6683456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683477 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 2, 2, 2]
def baseStart_6683477 : Nat := 118140960795 + 6683477 * 2 ^ 59
def prefixEnd_6683477 : Nat := 4983230072969 + 3 ^ 40 * 6683477 * 2
def baseEnd_6683477 : Nat := 3431836144269652599200755

theorem tailTrace_6683477 : CollatzResearch.WordTrace tailWord_6683477 prefixEnd_6683477 3431836144269652599200755 := by
  unfold tailWord_6683477
  simp only [CollatzResearch.WordTrace]
  refine ⟨243766432407911750841472685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162510954938607833894315123 243766432407911750841472685)
  ·
    refine ⟨91412412152966906565552257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243766432407911750841472685 91412412152966906565552257)
    ·
      refine ⟨68559309114725179924164193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91412412152966906565552257 68559309114725179924164193)
      ·
        refine ⟨51419481836043884943123145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68559309114725179924164193 51419481836043884943123145)
        ·
          refine ⟨38564611377032913707342359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51419481836043884943123145 38564611377032913707342359)
          ·
            refine ⟨57846917065549370561013539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38564611377032913707342359 57846917065549370561013539)
            ·
              refine ⟨86770375598324055841520309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57846917065549370561013539 86770375598324055841520309)
              ·
                refine ⟨8134722712342880235142529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86770375598324055841520309 8134722712342880235142529)
                ·
                  refine ⟨6101042034257160176356897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8134722712342880235142529 6101042034257160176356897)
                  ·
                    refine ⟨4575781525692870132267673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6101042034257160176356897 4575781525692870132267673)
                    ·
                      refine ⟨3431836144269652599200755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575781525692870132267673 3431836144269652599200755)
                      ·
                        rfl

theorem cell23_6683477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_6683477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683477 prefixEnd_6683477 := by exact prefixLift 6683477
  have htrace : WordTrace (prefixWord ++ tailWord_6683477) baseStart_6683477 baseEnd_6683477 := by
    simpa [prefixWord, tailWord_6683477, baseEnd_6683477] using wordTrace_append hprefix tailTrace_6683477
  have hstable : (prefixWord ++ tailWord_6683477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683477).length < 2 ^ (prefixWord ++ tailWord_6683477).sum := by decide
  have hdescent : baseEnd_6683477 < baseStart_6683477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683500 : List Nat := [2, 2, 1, 1, 4, 1, 4, 3, 5]
def baseStart_6683500 : Nat := 118140960795 + 6683500 * 2 ^ 59
def prefixEnd_6683500 : Nat := 4983230072969 + 3 ^ 40 * 6683500 * 2
def baseEnd_6683500 : Nat := 381316439369411778801461

theorem tailTrace_6683500 : CollatzResearch.WordTrace tailWord_6683500 prefixEnd_6683500 381316439369411778801461 := by
  unfold tailWord_6683500
  simp only [CollatzResearch.WordTrace]
  refine ⟨121883635643414212884779977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162511514191218950513039969 121883635643414212884779977)
  ·
    refine ⟨91412726732560659663584983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121883635643414212884779977 91412726732560659663584983)
    ·
      refine ⟨137119090098840989495377475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91412726732560659663584983 137119090098840989495377475)
      ·
        refine ⟨205678635148261484243066213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137119090098840989495377475 205678635148261484243066213)
        ·
          refine ⟨38564744090299028295574915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205678635148261484243066213 38564744090299028295574915)
          ·
            refine ⟨57847116135448542443362373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38564744090299028295574915 57847116135448542443362373)
            ·
              refine ⟨10846334275396601708130445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57847116135448542443362373 10846334275396601708130445)
              ·
                refine ⟨4067375353273725640548917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10846334275396601708130445 4067375353273725640548917)
                ·
                  refine ⟨381316439369411778801461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4067375353273725640548917 381316439369411778801461)
                  ·
                    rfl

theorem cell23_6683500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_6683500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683500 prefixEnd_6683500 := by exact prefixLift 6683500
  have htrace : WordTrace (prefixWord ++ tailWord_6683500) baseStart_6683500 baseEnd_6683500 := by
    simpa [prefixWord, tailWord_6683500, baseEnd_6683500] using wordTrace_append hprefix tailTrace_6683500
  have hstable : (prefixWord ++ tailWord_6683500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683500).length < 2 ^ (prefixWord ++ tailWord_6683500).sum := by decide
  have hdescent : baseEnd_6683500 < baseStart_6683500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683536 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_6683536 : Nat := 118140960795 + 6683536 * 2 ^ 59
def prefixEnd_6683536 : Nat := 4983230072969 + 3 ^ 40 * 6683536 * 2
def baseEnd_6683536 : Nat := 3431866439628267868362983

theorem tailTrace_6683536 : CollatzResearch.WordTrace tailWord_6683536 prefixEnd_6683536 3431866439628267868362983 := by
  unfold tailWord_6683536
  simp only [CollatzResearch.WordTrace]
  refine ⟨121884292157349001958935231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162512389543132002611913641 121884292157349001958935231)
  ·
    refine ⟨182826438236023502938402847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121884292157349001958935231 182826438236023502938402847)
    ·
      refine ⟨274239657354035254407604271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182826438236023502938402847 274239657354035254407604271)
      ·
        refine ⟨411359486031052881611406407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274239657354035254407604271 411359486031052881611406407)
        ·
          refine ⟨617039229046579322417109611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411359486031052881611406407 617039229046579322417109611)
          ·
            refine ⟨925558843569868983625664417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617039229046579322417109611 925558843569868983625664417)
            ·
              refine ⟨694169132677401737719248313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925558843569868983625664417 694169132677401737719248313)
              ·
                refine ⟨520626849508051303289436235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694169132677401737719248313 520626849508051303289436235)
                ·
                  refine ⟨780940274262076954934154353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520626849508051303289436235 780940274262076954934154353)
                  ·
                    refine ⟨585705205696557716200615765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 780940274262076954934154353 585705205696557716200615765)
                    ·
                      refine ⟨3431866439628267868362983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 585705205696557716200615765 3431866439628267868362983)
                      ·
                        rfl

theorem cell23_6683536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_6683536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683536 prefixEnd_6683536 := by exact prefixLift 6683536
  have htrace : WordTrace (prefixWord ++ tailWord_6683536) baseStart_6683536 baseEnd_6683536 := by
    simpa [prefixWord, tailWord_6683536, baseEnd_6683536] using wordTrace_append hprefix tailTrace_6683536
  have hstable : (prefixWord ++ tailWord_6683536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683536).length < 2 ^ (prefixWord ++ tailWord_6683536).sum := by decide
  have hdescent : baseEnd_6683536 < baseStart_6683536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683573 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 8]
def baseStart_6683573 : Nat := 118140960795 + 6683573 * 2 ^ 59
def prefixEnd_6683573 : Nat := 4983230072969 + 3 ^ 40 * 6683573 * 2
def baseEnd_6683573 : Nat := 381320604268053802622257

theorem tailTrace_6683573 : CollatzResearch.WordTrace tailWord_6683573 prefixEnd_6683573 381320604268053802622257 := by
  unfold tailWord_6683573
  simp only [CollatzResearch.WordTrace]
  refine ⟨243769933815563959236967373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162513289210375972824644915 243769933815563959236967373)
  ·
    refine ⟨91413725180836484713862765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243769933815563959236967373 91413725180836484713862765)
    ·
      refine ⟨34280146942813681767698537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91413725180836484713862765 34280146942813681767698537)
      ·
        refine ⟨25710110207110261325773903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34280146942813681767698537 25710110207110261325773903)
        ·
          refine ⟨38565165310665391988660855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25710110207110261325773903 38565165310665391988660855)
          ·
            refine ⟨57847747965998087982991283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38565165310665391988660855 57847747965998087982991283)
            ·
              refine ⟨86771621948997131974486925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57847747965998087982991283 86771621948997131974486925)
              ·
                refine ⟨32539358230873924490432597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86771621948997131974486925 32539358230873924490432597)
                ·
                  refine ⟨381320604268053802622257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32539358230873924490432597 381320604268053802622257)
                  ·
                    rfl

theorem cell23_6683573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_6683573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683573 prefixEnd_6683573 := by exact prefixLift 6683573
  have htrace : WordTrace (prefixWord ++ tailWord_6683573) baseStart_6683573 baseEnd_6683573 := by
    simpa [prefixWord, tailWord_6683573, baseEnd_6683573] using wordTrace_append hprefix tailTrace_6683573
  have hstable : (prefixWord ++ tailWord_6683573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683573).length < 2 ^ (prefixWord ++ tailWord_6683573).sum := by decide
  have hdescent : baseEnd_6683573 < baseStart_6683573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683577 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 3, 4]
def baseStart_6683577 : Nat := 118140960795 + 6683577 * 2 ^ 59
def prefixEnd_6683577 : Nat := 4983230072969 + 3 ^ 40 * 6683577 * 2
def baseEnd_6683577 : Nat := 1143962497445034069316765

theorem tailTrace_6683577 : CollatzResearch.WordTrace tailWord_6683577 prefixEnd_6683577 1143962497445034069316765 := by
  unfold tailWord_6683577
  simp only [CollatzResearch.WordTrace]
  refine ⟨243770079707549467920112985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162513386471699645280075323 243770079707549467920112985)
  ·
    refine ⟨182827559780662100940084739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243770079707549467920112985 182827559780662100940084739)
    ·
      refine ⟨274241339670993151410127109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182827559780662100940084739 274241339670993151410127109)
      ·
        refine ⟨51420251188311215889398833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274241339670993151410127109 51420251188311215889398833)
        ·
          refine ⟨38565188391233411917049125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51420251188311215889398833 38565188391233411917049125)
          ·
            refine ⟨7230972823356264734446711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38565188391233411917049125 7230972823356264734446711)
            ·
              refine ⟨10846459235034397101670067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7230972823356264734446711 10846459235034397101670067)
              ·
                refine ⟨16269688852551595652505101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10846459235034397101670067 16269688852551595652505101)
                ·
                  refine ⟨6101133319706848369689413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16269688852551595652505101 6101133319706848369689413)
                  ·
                    refine ⟨1143962497445034069316765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6101133319706848369689413 1143962497445034069316765)
                    ·
                      rfl

theorem cell23_6683577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 4].length) (baseStart_6683577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683577 prefixEnd_6683577 := by exact prefixLift 6683577
  have htrace : WordTrace (prefixWord ++ tailWord_6683577) baseStart_6683577 baseEnd_6683577 := by
    simpa [prefixWord, tailWord_6683577, baseEnd_6683577] using wordTrace_append hprefix tailTrace_6683577
  have hstable : (prefixWord ++ tailWord_6683577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683577).length < 2 ^ (prefixWord ++ tailWord_6683577).sum := by decide
  have hdescent : baseEnd_6683577 < baseStart_6683577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683583 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 3]
def baseStart_6683583 : Nat := 118140960795 + 6683583 * 2 ^ 59
def prefixEnd_6683583 : Nat := 4983230072969 + 3 ^ 40 * 6683583 * 2
def baseEnd_6683583 : Nat := 3431890573219029184475267

theorem tailTrace_6683583 : CollatzResearch.WordTrace tailWord_6683583 prefixEnd_6683583 3431890573219029184475267 := by
  unfold tailWord_6683583
  simp only [CollatzResearch.WordTrace]
  refine ⟨243770298545527730944831403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162513532363685153963220935 243770298545527730944831403)
  ·
    refine ⟨365655447818291596417247105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243770298545527730944831403 365655447818291596417247105)
    ·
      refine ⟨274241585863718697312935329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365655447818291596417247105 274241585863718697312935329)
      ·
        refine ⟨205681189397789022984701497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274241585863718697312935329 205681189397789022984701497)
        ·
          refine ⟨154260892048341767238526123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205681189397789022984701497 154260892048341767238526123)
          ·
            refine ⟨231391338072512650857789185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154260892048341767238526123 231391338072512650857789185)
            ·
              refine ⟨173543503554384488143341889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231391338072512650857789185 173543503554384488143341889)
              ·
                refine ⟨130157627665788366107506417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173543503554384488143341889 130157627665788366107506417)
                ·
                  refine ⟨97618220749341274580629813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130157627665788366107506417 97618220749341274580629813)
                  ·
                    refine ⟨9151708195250744491934045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97618220749341274580629813 9151708195250744491934045)
                    ·
                      refine ⟨3431890573219029184475267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9151708195250744491934045 3431890573219029184475267)
                      ·
                        rfl

theorem cell23_6683583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_6683583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683583 prefixEnd_6683583 := by exact prefixLift 6683583
  have htrace : WordTrace (prefixWord ++ tailWord_6683583) baseStart_6683583 baseEnd_6683583 := by
    simpa [prefixWord, tailWord_6683583, baseEnd_6683583] using wordTrace_append hprefix tailTrace_6683583
  have hstable : (prefixWord ++ tailWord_6683583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683583).length < 2 ^ (prefixWord ++ tailWord_6683583).sum := by decide
  have hdescent : baseEnd_6683583 < baseStart_6683583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683600 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 5, 1, 3]
def baseStart_6683600 : Nat := 118140960795 + 6683600 * 2 ^ 59
def prefixEnd_6683600 : Nat := 4983230072969 + 3 ^ 40 * 6683600 * 2
def baseEnd_6683600 : Nat := 3431899302390155617962689

theorem tailTrace_6683600 : CollatzResearch.WordTrace tailWord_6683600 prefixEnd_6683600 3431899302390155617962689 := by
  unfold tailWord_6683600
  simp only [CollatzResearch.WordTrace]
  refine ⟨121885459293233071424100127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162513945724310761898800169 121885459293233071424100127)
  ·
    refine ⟨182828188939849607136150191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121885459293233071424100127 182828188939849607136150191)
    ·
      refine ⟨274242283409774410704225287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182828188939849607136150191 274242283409774410704225287)
      ·
        refine ⟨411363425114661616056337931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274242283409774410704225287 411363425114661616056337931)
        ·
          refine ⟨617045137671992424084506897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411363425114661616056337931 617045137671992424084506897)
          ·
            refine ⟨462783853253994318063380173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617045137671992424084506897 462783853253994318063380173)
            ·
              refine ⟨173543944970247869273767565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462783853253994318063380173 173543944970247869273767565)
              ·
                refine ⟨65078979363842950977662837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173543944970247869273767565 65078979363842950977662837)
                ·
                  refine ⟨6101154315360276654155891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65078979363842950977662837 6101154315360276654155891)
                  ·
                    refine ⟨9151731473040414981233837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6101154315360276654155891 9151731473040414981233837)
                    ·
                      refine ⟨3431899302390155617962689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9151731473040414981233837 3431899302390155617962689)
                      ·
                        rfl

theorem cell23_6683600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5, 1, 3].length) (baseStart_6683600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683600 prefixEnd_6683600 := by exact prefixLift 6683600
  have htrace : WordTrace (prefixWord ++ tailWord_6683600) baseStart_6683600 baseEnd_6683600 := by
    simpa [prefixWord, tailWord_6683600, baseEnd_6683600] using wordTrace_append hprefix tailTrace_6683600
  have hstable : (prefixWord ++ tailWord_6683600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683600).length < 2 ^ (prefixWord ++ tailWord_6683600).sum := by decide
  have hdescent : baseEnd_6683600 < baseStart_6683600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683640 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 2, 6, 2]
def baseStart_6683640 : Nat := 118140960795 + 6683640 * 2 ^ 59
def prefixEnd_6683640 : Nat := 4983230072969 + 3 ^ 40 * 6683640 * 2
def baseEnd_6683640 : Nat := 3431919841616335461462505

theorem tailTrace_6683640 : CollatzResearch.WordTrace tailWord_6683640 prefixEnd_6683640 3431919841616335461462505 := by
  unfold tailWord_6683640
  simp only [CollatzResearch.WordTrace]
  refine ⟨121886188753160614839828187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162514918337547486453104249 121886188753160614839828187)
  ·
    refine ⟨182829283129740922259742281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121886188753160614839828187 182829283129740922259742281)
    ·
      refine ⟨137121962347305691694806711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182829283129740922259742281 137121962347305691694806711)
      ·
        refine ⟨205682943520958537542210067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137121962347305691694806711 205682943520958537542210067)
        ·
          refine ⟨308524415281437806313315101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205682943520958537542210067 308524415281437806313315101)
          ·
            refine ⟨115696655730539177367493163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308524415281437806313315101 115696655730539177367493163)
            ·
              refine ⟨173544983595808766051239745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115696655730539177367493163 173544983595808766051239745)
              ·
                refine ⟨130158737696856574538429809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173544983595808766051239745 130158737696856574538429809)
                ·
                  refine ⟨97619053272642430903822357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130158737696856574538429809 97619053272642430903822357)
                  ·
                    refine ⟨4575893122155113948616673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97619053272642430903822357 4575893122155113948616673)
                    ·
                      refine ⟨3431919841616335461462505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575893122155113948616673 3431919841616335461462505)
                      ·
                        rfl

theorem cell23_6683640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 6, 2].length) (baseStart_6683640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683640 prefixEnd_6683640 := by exact prefixLift 6683640
  have htrace : WordTrace (prefixWord ++ tailWord_6683640) baseStart_6683640 baseEnd_6683640 := by
    simpa [prefixWord, tailWord_6683640, baseEnd_6683640] using wordTrace_append hprefix tailTrace_6683640
  have hstable : (prefixWord ++ tailWord_6683640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683640).length < 2 ^ (prefixWord ++ tailWord_6683640).sum := by decide
  have hdescent : baseEnd_6683640 < baseStart_6683640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683643 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 5]
def baseStart_6683643 : Nat := 118140960795 + 6683643 * 2 ^ 59
def prefixEnd_6683643 : Nat := 4983230072969 + 3 ^ 40 * 6683643 * 2
def baseEnd_6683643 : Nat := 3431921382058298949724991

theorem tailTrace_6683643 : CollatzResearch.WordTrace tailWord_6683643 prefixEnd_6683643 3431921382058298949724991 := by
  unfold tailWord_6683643
  simp only [CollatzResearch.WordTrace]
  refine ⟨243772486925310361192015583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162514991283540240794677055 243772486925310361192015583)
  ·
    refine ⟨365658730387965541788023375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243772486925310361192015583 365658730387965541788023375)
    ·
      refine ⟨548488095581948312682035063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365658730387965541788023375 548488095581948312682035063)
      ·
        refine ⟨822732143372922469023052595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548488095581948312682035063 822732143372922469023052595)
        ·
          refine ⟨1234098215059383703534578893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822732143372922469023052595 1234098215059383703534578893)
          ·
            refine ⟨462786830647268888825467085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1234098215059383703534578893 462786830647268888825467085)
            ·
              refine ⟨173545061492725833309550157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462786830647268888825467085 173545061492725833309550157)
              ·
                refine ⟨65079398059772187491081309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173545061492725833309550157 65079398059772187491081309)
                ·
                  refine ⟨24404774272414570309155491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65079398059772187491081309 24404774272414570309155491)
                  ·
                    refine ⟨36607161408621855463733237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24404774272414570309155491 36607161408621855463733237)
                    ·
                      refine ⟨3431921382058298949724991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36607161408621855463733237 3431921382058298949724991)
                      ·
                        rfl

theorem cell23_6683643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 5].length) (baseStart_6683643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683643 prefixEnd_6683643 := by exact prefixLift 6683643
  have htrace : WordTrace (prefixWord ++ tailWord_6683643) baseStart_6683643 baseEnd_6683643 := by
    simpa [prefixWord, tailWord_6683643, baseEnd_6683643] using wordTrace_append hprefix tailTrace_6683643
  have hstable : (prefixWord ++ tailWord_6683643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683643).length < 2 ^ (prefixWord ++ tailWord_6683643).sum := by decide
  have hdescent : baseEnd_6683643 < baseStart_6683643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683684 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_6683684 : Nat := 118140960795 + 6683684 * 2 ^ 59
def prefixEnd_6683684 : Nat := 4983230072969 + 3 ^ 40 * 6683684 * 2
def baseEnd_6683684 : Nat := 1143980811588377763104101

theorem tailTrace_6683684 : CollatzResearch.WordTrace tailWord_6683684 prefixEnd_6683684 1143980811588377763104101 := by
  unfold tailWord_6683684
  simp only [CollatzResearch.WordTrace]
  refine ⟨121886991159080912597129053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162515988212107883462838737 121886991159080912597129053)
  ·
    refine ⟨45707621684655342223923395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121886991159080912597129053 45707621684655342223923395)
    ·
      refine ⟨68561432526983013335885093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45707621684655342223923395 68561432526983013335885093)
      ·
        refine ⟨12855268598809315000478455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68561432526983013335885093 12855268598809315000478455)
        ·
          refine ⟨19282902898213972500717683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12855268598809315000478455 19282902898213972500717683)
          ·
            refine ⟨28924354347320958751076525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19282902898213972500717683 28924354347320958751076525)
            ·
              refine ⟨10846632880245359531653697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28924354347320958751076525 10846632880245359531653697)
              ·
                refine ⟨8134974660184019648740273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10846632880245359531653697 8134974660184019648740273)
                ·
                  refine ⟨6101230995138014736555205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8134974660184019648740273 6101230995138014736555205)
                  ·
                    refine ⟨1143980811588377763104101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6101230995138014736555205 1143980811588377763104101)
                    ·
                      rfl

theorem cell23_6683684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_6683684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683684 prefixEnd_6683684 := by exact prefixLift 6683684
  have htrace : WordTrace (prefixWord ++ tailWord_6683684) baseStart_6683684 baseEnd_6683684 := by
    simpa [prefixWord, tailWord_6683684, baseEnd_6683684] using wordTrace_append hprefix tailTrace_6683684
  have hstable : (prefixWord ++ tailWord_6683684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683684).length < 2 ^ (prefixWord ++ tailWord_6683684).sum := by decide
  have hdescent : baseEnd_6683684 < baseStart_6683684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683717 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 3, 3, 2]
def baseStart_6683717 : Nat := 118140960795 + 6683717 * 2 ^ 59
def prefixEnd_6683717 : Nat := 4983230072969 + 3 ^ 40 * 6683717 * 2
def baseEnd_6683717 : Nat := 3431959379626731660199651

theorem tailTrace_6683717 : CollatzResearch.WordTrace tailWord_6683717 prefixEnd_6683717 3431959379626731660199651 := by
  unfold tailWord_6683717
  simp only [CollatzResearch.WordTrace]
  refine ⟨243775185927042271830209405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162516790618028181220139603 243775185927042271830209405)
  ·
    refine ⟨91415694722640851936328527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243775185927042271830209405 91415694722640851936328527)
    ·
      refine ⟨137123542083961277904492791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91415694722640851936328527 137123542083961277904492791)
      ·
        refine ⟨205685313125941916856739187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137123542083961277904492791 205685313125941916856739187)
        ·
          refine ⟨308527969688912875285108781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205685313125941916856739187 308527969688912875285108781)
          ·
            refine ⟨115697988633342328231915793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308527969688912875285108781 115697988633342328231915793)
            ·
              refine ⟨86773491475006746173936845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115697988633342328231915793 86773491475006746173936845)
              ·
                refine ⟨32540059303127529815226317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86773491475006746173936845 32540059303127529815226317)
                ·
                  refine ⟨12202522238672823680709869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32540059303127529815226317 12202522238672823680709869)
                  ·
                    refine ⟨4575945839502308880266201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12202522238672823680709869 4575945839502308880266201)
                    ·
                      refine ⟨3431959379626731660199651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575945839502308880266201 3431959379626731660199651)
                      ·
                        rfl

theorem cell23_6683717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 3, 2].length) (baseStart_6683717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683717 prefixEnd_6683717 := by exact prefixLift 6683717
  have htrace : WordTrace (prefixWord ++ tailWord_6683717) baseStart_6683717 baseEnd_6683717 := by
    simpa [prefixWord, tailWord_6683717, baseEnd_6683717] using wordTrace_append hprefix tailTrace_6683717
  have hstable : (prefixWord ++ tailWord_6683717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683717).length < 2 ^ (prefixWord ++ tailWord_6683717).sum := by decide
  have hdescent : baseEnd_6683717 < baseStart_6683717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683725 : List Nat := [1, 6, 1, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_6683725 : Nat := 118140960795 + 6683725 * 2 ^ 59
def prefixEnd_6683725 : Nat := 4983230072969 + 3 ^ 40 * 6683725 * 2
def baseEnd_6683725 : Nat := 3431963487471967628899615

theorem tailTrace_6683725 : CollatzResearch.WordTrace tailWord_6683725 prefixEnd_6683725 3431963487471967628899615 := by
  unfold tailWord_6683725
  simp only [CollatzResearch.WordTrace]
  refine ⟨243775477711013289196500629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162516985140675526131000419 243775477711013289196500629)
  ·
    refine ⟨11426975517703747931085967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 243775477711013289196500629 11426975517703747931085967)
    ·
      refine ⟨17140463276555621896628951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11426975517703747931085967 17140463276555621896628951)
      ·
        refine ⟨25710694914833432844943427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17140463276555621896628951 25710694914833432844943427)
        ·
          refine ⟨38566042372250149267415141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25710694914833432844943427 38566042372250149267415141)
          ·
            refine ⟨7231132944796902987640339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38566042372250149267415141 7231132944796902987640339)
            ·
              refine ⟨10846699417195354481460509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7231132944796902987640339 10846699417195354481460509)
              ·
                refine ⟨4067512281448257930547691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10846699417195354481460509 4067512281448257930547691)
                ·
                  refine ⟨6101268422172386895821537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067512281448257930547691 6101268422172386895821537)
                  ·
                    refine ⟨4575951316629290171866153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6101268422172386895821537 4575951316629290171866153)
                    ·
                      refine ⟨3431963487471967628899615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4575951316629290171866153 3431963487471967628899615)
                      ·
                        rfl

theorem cell23_6683725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_6683725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683725 prefixEnd_6683725 := by exact prefixLift 6683725
  have htrace : WordTrace (prefixWord ++ tailWord_6683725) baseStart_6683725 baseEnd_6683725 := by
    simpa [prefixWord, tailWord_6683725, baseEnd_6683725] using wordTrace_append hprefix tailTrace_6683725
  have hstable : (prefixWord ++ tailWord_6683725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683725).length < 2 ^ (prefixWord ++ tailWord_6683725).sum := by decide
  have hdescent : baseEnd_6683725 < baseStart_6683725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683758 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_6683758 : Nat := 118140960795 + 6683758 * 2 ^ 59
def prefixEnd_6683758 : Nat := 4983230072969 + 3 ^ 40 * 6683758 * 2
def baseEnd_6683758 : Nat := 3431980432333565999786963

theorem tailTrace_6683758 : CollatzResearch.WordTrace tailWord_6683758 prefixEnd_6683758 3431980432333565999786963 := by
  unfold tailWord_6683758
  simp only [CollatzResearch.WordTrace]
  refine ⟨30472085164986716979056491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162517787546595823888301285 30472085164986716979056491)
  ·
    refine ⟨45708127747480075468584737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30472085164986716979056491 45708127747480075468584737)
    ·
      refine ⟨34281095810610056601438553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45708127747480075468584737 34281095810610056601438553)
      ·
        refine ⟨25710821857957542451078915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34281095810610056601438553 25710821857957542451078915)
        ·
          refine ⟨38566232786936313676618373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25710821857957542451078915 38566232786936313676618373)
          ·
            refine ⟨7231168647550558814365945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38566232786936313676618373 7231168647550558814365945)
            ·
              refine ⟨5423376485662919110774459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7231168647550558814365945 5423376485662919110774459)
              ·
                refine ⟨8135064728494378666161689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5423376485662919110774459 8135064728494378666161689)
                ·
                  refine ⟨6101298546370783999621267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8135064728494378666161689 6101298546370783999621267)
                  ·
                    refine ⟨9151947819556175999431901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6101298546370783999621267 9151947819556175999431901)
                    ·
                      refine ⟨3431980432333565999786963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9151947819556175999431901 3431980432333565999786963)
                      ·
                        rfl

theorem cell23_6683758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_6683758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683758 prefixEnd_6683758 := by exact prefixLift 6683758
  have htrace : WordTrace (prefixWord ++ tailWord_6683758) baseStart_6683758 baseEnd_6683758 := by
    simpa [prefixWord, tailWord_6683758, baseEnd_6683758] using wordTrace_append hprefix tailTrace_6683758
  have hstable : (prefixWord ++ tailWord_6683758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683758).length < 2 ^ (prefixWord ++ tailWord_6683758).sum := by decide
  have hdescent : baseEnd_6683758 < baseStart_6683758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683760 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 4]
def baseStart_6683760 : Nat := 118140960795 + 6683760 * 2 ^ 59
def prefixEnd_6683760 : Nat := 4983230072969 + 3 ^ 40 * 6683760 * 2
def baseEnd_6683760 : Nat := 3431981459294874991961953

theorem tailTrace_6683760 : CollatzResearch.WordTrace tailWord_6683760 prefixEnd_6683760 3431981459294874991961953 := by
  unfold tailWord_6683760
  simp only [CollatzResearch.WordTrace]
  refine ⟨121888377132943245087012367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162517836177257660116016489 121888377132943245087012367)
  ·
    refine ⟨182832565699414867630518551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121888377132943245087012367 182832565699414867630518551)
    ·
      refine ⟨274248848549122301445777827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182832565699414867630518551 274248848549122301445777827)
      ·
        refine ⟨411373272823683452168666741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274248848549122301445777827 411373272823683452168666741)
        ·
          refine ⟨38566244327220323640812507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 411373272823683452168666741 38566244327220323640812507)
          ·
            refine ⟨57849366490830485461218761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38566244327220323640812507 57849366490830485461218761)
            ·
              refine ⟨43387024868122864095914071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57849366490830485461218761 43387024868122864095914071)
              ·
                refine ⟨65080537302184296143871107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43387024868122864095914071 65080537302184296143871107)
                ·
                  refine ⟨97620805953276444215806661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65080537302184296143871107 97620805953276444215806661)
                  ·
                    refine ⟨18303901116239333290463749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97620805953276444215806661 18303901116239333290463749)
                    ·
                      refine ⟨3431981459294874991961953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18303901116239333290463749 3431981459294874991961953)
                      ·
                        rfl

theorem cell23_6683760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_6683760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683760 prefixEnd_6683760 := by exact prefixLift 6683760
  have htrace : WordTrace (prefixWord ++ tailWord_6683760) baseStart_6683760 baseEnd_6683760 := by
    simpa [prefixWord, tailWord_6683760, baseEnd_6683760] using wordTrace_append hprefix tailTrace_6683760
  have hstable : (prefixWord ++ tailWord_6683760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683760).length < 2 ^ (prefixWord ++ tailWord_6683760).sum := by decide
  have hdescent : baseEnd_6683760 < baseStart_6683760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683804 : List Nat := [2, 2, 3, 2, 1, 3, 1, 4, 5]
def baseStart_6683804 : Nat := 118140960795 + 6683804 * 2 ^ 59
def prefixEnd_6683804 : Nat := 4983230072969 + 3 ^ 40 * 6683804 * 2
def baseEnd_6683804 : Nat := 381333783604852535534639

theorem tailTrace_6683804 : CollatzResearch.WordTrace tailWord_6683804 prefixEnd_6683804 381333783604852535534639 := by
  unfold tailWord_6683804
  simp only [CollatzResearch.WordTrace]
  refine ⟨121889179538863542844313233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162518906051818057125750977 121889179538863542844313233)
  ·
    refine ⟨91416884654147657133234925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121889179538863542844313233 91416884654147657133234925)
    ·
      refine ⟨34281331745305371424963097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91416884654147657133234925 34281331745305371424963097)
      ·
        refine ⟨25710998808979028568722323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34281331745305371424963097 25710998808979028568722323)
        ·
          refine ⟨38566498213468542853083485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25710998808979028568722323 38566498213468542853083485)
          ·
            refine ⟨14462436830050703569906307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38566498213468542853083485 14462436830050703569906307)
            ·
              refine ⟨21693655245076055354859461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14462436830050703569906307 21693655245076055354859461)
              ·
                refine ⟨4067560358451760379036149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21693655245076055354859461 4067560358451760379036149)
                ·
                  refine ⟨381333783604852535534639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4067560358451760379036149 381333783604852535534639)
                  ·
                    rfl

theorem cell23_6683804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_6683804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683804 prefixEnd_6683804 := by exact prefixLift 6683804
  have htrace : WordTrace (prefixWord ++ tailWord_6683804) baseStart_6683804 baseEnd_6683804 := by
    simpa [prefixWord, tailWord_6683804, baseEnd_6683804] using wordTrace_append hprefix tailTrace_6683804
  have hstable : (prefixWord ++ tailWord_6683804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683804).length < 2 ^ (prefixWord ++ tailWord_6683804).sum := by decide
  have hdescent : baseEnd_6683804 < baseStart_6683804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683857 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 4, 2, 3]
def baseStart_6683857 : Nat := 118140960795 + 6683857 * 2 ^ 59
def prefixEnd_6683857 : Nat := 4983230072969 + 3 ^ 40 * 6683857 * 2
def baseEnd_6683857 : Nat := 3432031266918361112449007

theorem tailTrace_6683857 : CollatzResearch.WordTrace tailWord_6683857 prefixEnd_6683857 3432031266918361112449007 := by
  unfold tailWord_6683857
  simp only [CollatzResearch.WordTrace]
  refine ⟨243780292146535075740305825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162520194764356717160203883 243780292146535075740305825)
  ·
    refine ⟨182835219109901306805229369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243780292146535075740305825 182835219109901306805229369)
    ·
      refine ⟨137126414332425980103922027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182835219109901306805229369 137126414332425980103922027)
      ·
        refine ⟨205689621498638970155883041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137126414332425980103922027 205689621498638970155883041)
        ·
          refine ⟨154267216123979227616912281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205689621498638970155883041 154267216123979227616912281)
          ·
            refine ⟨115700412092984420712684211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154267216123979227616912281 115700412092984420712684211)
            ·
              refine ⟨173550618139476631069026317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115700412092984420712684211 173550618139476631069026317)
              ·
                refine ⟨65081481802303736650884869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173550618139476631069026317 65081481802303736650884869)
                ·
                  refine ⟨12202777837931950622040913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65081481802303736650884869 12202777837931950622040913)
                  ·
                    refine ⟨9152083378448962966530685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12202777837931950622040913 9152083378448962966530685)
                    ·
                      refine ⟨3432031266918361112449007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9152083378448962966530685 3432031266918361112449007)
                      ·
                        rfl

theorem cell23_6683857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_6683857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683857 prefixEnd_6683857 := by exact prefixLift 6683857
  have htrace : WordTrace (prefixWord ++ tailWord_6683857) baseStart_6683857 baseEnd_6683857 := by
    simpa [prefixWord, tailWord_6683857, baseEnd_6683857] using wordTrace_append hprefix tailTrace_6683857
  have hstable : (prefixWord ++ tailWord_6683857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683857).length < 2 ^ (prefixWord ++ tailWord_6683857).sum := by decide
  have hdescent : baseEnd_6683857 < baseStart_6683857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683937 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 1, 6]
def baseStart_6683937 : Nat := 118140960795 + 6683937 * 2 ^ 59
def prefixEnd_6683937 : Nat := 4983230072969 + 3 ^ 40 * 6683937 * 2
def baseEnd_6683937 : Nat := 1144024115123573599816213

theorem tailTrace_6683937 : CollatzResearch.WordTrace tailWord_6683937 prefixEnd_6683937 1144024115123573599816213 := by
  unfold tailWord_6683937
  simp only [CollatzResearch.WordTrace]
  refine ⟨243783209986245249403218065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162522139990830166268812043 243783209986245249403218065)
  ·
    refine ⟨182837407489683937052413549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243783209986245249403218065 182837407489683937052413549)
    ·
      refine ⟨68564027808631476394655081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182837407489683937052413549 68564027808631476394655081)
      ·
        refine ⟨51423020856473607295991311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68564027808631476394655081 51423020856473607295991311)
        ·
          refine ⟨77134531284710410943986967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51423020856473607295991311 77134531284710410943986967)
          ·
            refine ⟨115701796927065616415980451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77134531284710410943986967 115701796927065616415980451)
            ·
              refine ⟨173552695390598424623970677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115701796927065616415980451 173552695390598424623970677)
              ·
                refine ⟨16270565192868602308497251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173552695390598424623970677 16270565192868602308497251)
                ·
                  refine ⟨24405847789302903462745877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16270565192868602308497251 24405847789302903462745877)
                  ·
                    refine ⟨1144024115123573599816213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24405847789302903462745877 1144024115123573599816213)
                    ·
                      rfl

theorem cell23_6683937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_6683937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683937 prefixEnd_6683937 := by exact prefixLift 6683937
  have htrace : WordTrace (prefixWord ++ tailWord_6683937) baseStart_6683937 baseEnd_6683937 := by
    simpa [prefixWord, tailWord_6683937, baseEnd_6683937] using wordTrace_append hprefix tailTrace_6683937
  have hstable : (prefixWord ++ tailWord_6683937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683937).length < 2 ^ (prefixWord ++ tailWord_6683937).sum := by decide
  have hdescent : baseEnd_6683937 < baseStart_6683937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683941 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 1, 5]
def baseStart_6683941 : Nat := 118140960795 + 6683941 * 2 ^ 59
def prefixEnd_6683941 : Nat := 4983230072969 + 3 ^ 40 * 6683941 * 2
def baseEnd_6683941 : Nat := 1144024799764446261266207

theorem tailTrace_6683941 : CollatzResearch.WordTrace tailWord_6683941 prefixEnd_6683941 1144024799764446261266207 := by
  unfold tailWord_6683941
  simp only [CollatzResearch.WordTrace]
  refine ⟨243783355878230758086363677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162522237252153838724242451 243783355878230758086363677)
  ·
    refine ⟨91418758454336534282386379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243783355878230758086363677 91418758454336534282386379)
    ·
      refine ⟨137128137681504801423579569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91418758454336534282386379 137128137681504801423579569)
      ·
        refine ⟨102846103261128601067684677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137128137681504801423579569 102846103261128601067684677)
        ·
          refine ⟨19283644361461612700190877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102846103261128601067684677 19283644361461612700190877)
          ·
            refine ⟨7231366635548104762571579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19283644361461612700190877 7231366635548104762571579)
            ·
              refine ⟨10847049953322157143857369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7231366635548104762571579 10847049953322157143857369)
              ·
                refine ⟨8135287464991617857893027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10847049953322157143857369 8135287464991617857893027)
                ·
                  refine ⟨12202931197487426786839541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8135287464991617857893027 12202931197487426786839541)
                  ·
                    refine ⟨1144024799764446261266207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12202931197487426786839541 1144024799764446261266207)
                    ·
                      rfl

theorem cell23_6683941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_6683941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683941 prefixEnd_6683941 := by exact prefixLift 6683941
  have htrace : WordTrace (prefixWord ++ tailWord_6683941) baseStart_6683941 baseEnd_6683941 := by
    simpa [prefixWord, tailWord_6683941, baseEnd_6683941] using wordTrace_append hprefix tailTrace_6683941
  have hstable : (prefixWord ++ tailWord_6683941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683941).length < 2 ^ (prefixWord ++ tailWord_6683941).sum := by decide
  have hdescent : baseEnd_6683941 < baseStart_6683941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683954 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_6683954 : Nat := 118140960795 + 6683954 * 2 ^ 59
def prefixEnd_6683954 : Nat := 4983230072969 + 3 ^ 40 * 6683954 * 2
def baseEnd_6683954 : Nat := 1144027024847282410978687

theorem tailTrace_6683954 : CollatzResearch.WordTrace tailWord_6683954 prefixEnd_6683954 1144027024847282410978687 := by
  unfold tailWord_6683954
  simp only [CollatzResearch.WordTrace]
  refine ⟨60945957506795915326646729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162522553351455774204391277 60945957506795915326646729)
  ·
    refine ⟨45709468130096936494985047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60945957506795915326646729 45709468130096936494985047)
    ·
      refine ⟨68564202195145404742477571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45709468130096936494985047 68564202195145404742477571)
      ·
        refine ⟨102846303292718107113716357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68564202195145404742477571 102846303292718107113716357)
        ·
          refine ⟨19283681867384645083821817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102846303292718107113716357 19283681867384645083821817)
          ·
            refine ⟨14462761400538483812866363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19283681867384645083821817 14462761400538483812866363)
            ·
              refine ⟨21694142100807725719299545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14462761400538483812866363 21694142100807725719299545)
              ·
                refine ⟨16270606575605794289474659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21694142100807725719299545 16270606575605794289474659)
                ·
                  refine ⟨24405909863408691434211989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16270606575605794289474659 24405909863408691434211989)
                  ·
                    refine ⟨1144027024847282410978687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24405909863408691434211989 1144027024847282410978687)
                    ·
                      rfl

theorem cell23_6683954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_6683954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683954 prefixEnd_6683954 := by exact prefixLift 6683954
  have htrace : WordTrace (prefixWord ++ tailWord_6683954) baseStart_6683954 baseEnd_6683954 := by
    simpa [prefixWord, tailWord_6683954, baseEnd_6683954] using wordTrace_append hprefix tailTrace_6683954
  have hstable : (prefixWord ++ tailWord_6683954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683954).length < 2 ^ (prefixWord ++ tailWord_6683954).sum := by decide
  have hdescent : baseEnd_6683954 < baseStart_6683954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683964 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_6683964 : Nat := 118140960795 + 6683964 * 2 ^ 59
def prefixEnd_6683964 : Nat := 4983230072969 + 3 ^ 40 * 6683964 * 2
def baseEnd_6683964 : Nat := 3432086209348392193811015

theorem tailTrace_6683964 : CollatzResearch.WordTrace tailWord_6683964 prefixEnd_6683964 3432086209348392193811015 := by
  unfold tailWord_6683964
  simp only [CollatzResearch.WordTrace]
  refine ⟨121892097378573716507225473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162522796504764955342967297 121892097378573716507225473)
  ·
    refine ⟨91419073033930287380419105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121892097378573716507225473 91419073033930287380419105)
    ·
      refine ⟨68564304775447715535314329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91419073033930287380419105 68564304775447715535314329)
      ·
        refine ⟨51423228581585786651485747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68564304775447715535314329 51423228581585786651485747)
        ·
          refine ⟨77134842872378679977228621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51423228581585786651485747 77134842872378679977228621)
          ·
            refine ⟨28925566077142004991460733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77134842872378679977228621 28925566077142004991460733)
            ·
              refine ⟨10847087278928251871797775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28925566077142004991460733 10847087278928251871797775)
              ·
                refine ⟨16270630918392377807696663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10847087278928251871797775 16270630918392377807696663)
                ·
                  refine ⟨24405946377588566711544995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16270630918392377807696663 24405946377588566711544995)
                  ·
                    refine ⟨36608919566382850067317493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24405946377588566711544995 36608919566382850067317493)
                    ·
                      refine ⟨3432086209348392193811015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36608919566382850067317493 3432086209348392193811015)
                      ·
                        rfl

theorem cell23_6683964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_6683964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683964 prefixEnd_6683964 := by exact prefixLift 6683964
  have htrace : WordTrace (prefixWord ++ tailWord_6683964) baseStart_6683964 baseEnd_6683964 := by
    simpa [prefixWord, tailWord_6683964, baseEnd_6683964] using wordTrace_append hprefix tailTrace_6683964
  have hstable : (prefixWord ++ tailWord_6683964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683964).length < 2 ^ (prefixWord ++ tailWord_6683964).sum := by decide
  have hdescent : baseEnd_6683964 < baseStart_6683964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683972 : List Nat := [2, 3, 4, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_6683972 : Nat := 118140960795 + 6683972 * 2 ^ 59
def prefixEnd_6683972 : Nat := 4983230072969 + 3 ^ 40 * 6683972 * 2
def baseEnd_6683972 : Nat := 3432090317193628162510979

theorem tailTrace_6683972 : CollatzResearch.WordTrace tailWord_6683972 prefixEnd_6683972 3432090317193628162510979 := by
  unfold tailWord_6683972
  simp only [CollatzResearch.WordTrace]
  refine ⟨121892243270559225190371085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162522991027412300253828113 121892243270559225190371085)
  ·
    refine ⟨45709591226459709446389157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121892243270559225190371085 45709591226459709446389157)
    ·
      refine ⟨8570548354961195521197967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45709591226459709446389157 8570548354961195521197967)
      ·
        refine ⟨12855822532441793281796951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8570548354961195521197967 12855822532441793281796951)
        ·
          refine ⟨19283733798662689922695427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12855822532441793281796951 19283733798662689922695427)
          ·
            refine ⟨28925600697994034884043141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19283733798662689922695427 28925600697994034884043141)
            ·
              refine ⟨5423550130873881540758089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28925600697994034884043141 5423550130873881540758089)
              ·
                refine ⟨4067662598155411155568567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5423550130873881540758089 4067662598155411155568567)
                ·
                  refine ⟨6101493897233116733352851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067662598155411155568567 6101493897233116733352851)
                  ·
                    refine ⟨9152240845849675100029277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6101493897233116733352851 9152240845849675100029277)
                    ·
                      refine ⟨3432090317193628162510979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9152240845849675100029277 3432090317193628162510979)
                      ·
                        rfl

theorem cell23_6683972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_6683972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683972 prefixEnd_6683972 := by exact prefixLift 6683972
  have htrace : WordTrace (prefixWord ++ tailWord_6683972) baseStart_6683972 baseEnd_6683972 := by
    simpa [prefixWord, tailWord_6683972, baseEnd_6683972] using wordTrace_append hprefix tailTrace_6683972
  have hstable : (prefixWord ++ tailWord_6683972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683972).length < 2 ^ (prefixWord ++ tailWord_6683972).sum := by decide
  have hdescent : baseEnd_6683972 < baseStart_6683972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6683994 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3]
def baseStart_6683994 : Nat := 118140960795 + 6683994 * 2 ^ 59
def prefixEnd_6683994 : Nat := 4983230072969 + 3 ^ 40 * 6683994 * 2
def baseEnd_6683994 : Nat := 3432101613768027076435877

theorem tailTrace_6683994 : CollatzResearch.WordTrace tailWord_6683994 prefixEnd_6683994 3432101613768027076435877 := by
  unfold tailWord_6683994
  simp only [CollatzResearch.WordTrace]
  refine ⟨60946322236759687034510759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162523525964692498758695357 60946322236759687034510759)
  ·
    refine ⟨91419483355139530551766139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60946322236759687034510759 91419483355139530551766139)
    ·
      refine ⟨137129225032709295827649209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91419483355139530551766139 137129225032709295827649209)
      ·
        refine ⟨102846918774531971870736907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137129225032709295827649209 102846918774531971870736907)
        ·
          refine ⟨154270378161797957806105361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102846918774531971870736907 154270378161797957806105361)
          ·
            refine ⟨115702783621348468354579021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154270378161797957806105361 115702783621348468354579021)
            ·
              refine ⟨43388543858005675632967133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115702783621348468354579021 43388543858005675632967133)
              ·
                refine ⟨16270703946752128362362675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43388543858005675632967133 16270703946752128362362675)
                ·
                  refine ⟨24406055920128192543544013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16270703946752128362362675 24406055920128192543544013)
                  ·
                    refine ⟨9152270970048072203829005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24406055920128192543544013 9152270970048072203829005)
                    ·
                      refine ⟨3432101613768027076435877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9152270970048072203829005 3432101613768027076435877)
                      ·
                        rfl

theorem cell23_6683994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_6683994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6683994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6683994 prefixEnd_6683994 := by exact prefixLift 6683994
  have htrace : WordTrace (prefixWord ++ tailWord_6683994) baseStart_6683994 baseEnd_6683994 := by
    simpa [prefixWord, tailWord_6683994, baseEnd_6683994] using wordTrace_append hprefix tailTrace_6683994
  have hstable : (prefixWord ++ tailWord_6683994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6683994).length < 2 ^ (prefixWord ++ tailWord_6683994).sum := by decide
  have hdescent : baseEnd_6683994 < baseStart_6683994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6683994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684027 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 4, 6]
def baseStart_6684027 : Nat := 118140960795 + 6684027 * 2 ^ 59
def prefixEnd_6684027 : Nat := 4983230072969 + 3 ^ 40 * 6684027 * 2
def baseEnd_6684027 : Nat := 1144039519543208482441075

theorem tailTrace_6684027 : CollatzResearch.WordTrace tailWord_6684027 prefixEnd_6684027 1144039519543208482441075 := by
  unfold tailWord_6684027
  simp only [CollatzResearch.WordTrace]
  refine ⟨243786492555919194773994335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162524328370612796515996223 243786492555919194773994335)
  ·
    refine ⟨365679738833878792160991503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243786492555919194773994335 365679738833878792160991503)
    ·
      refine ⟨548519608250818188241487255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365679738833878792160991503 548519608250818188241487255)
      ·
        refine ⟨822779412376227282362230883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548519608250818188241487255 822779412376227282362230883)
        ·
          refine ⟨1234169118564340923543346325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822779412376227282362230883 1234169118564340923543346325)
          ·
            refine ⟨57851677432703480791094359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1234169118564340923543346325 57851677432703480791094359)
            ·
              refine ⟨86777516149055221186641539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57851677432703480791094359 86777516149055221186641539)
              ·
                refine ⟨130166274223582831779962309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86777516149055221186641539 130166274223582831779962309)
                ·
                  refine ⟨24406176416921780958742933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130166274223582831779962309 24406176416921780958742933)
                  ·
                    refine ⟨1144039519543208482441075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24406176416921780958742933 1144039519543208482441075)
                    ·
                      rfl

theorem cell23_6684027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 6].length) (baseStart_6684027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684027 prefixEnd_6684027 := by exact prefixLift 6684027
  have htrace : WordTrace (prefixWord ++ tailWord_6684027) baseStart_6684027 baseEnd_6684027 := by
    simpa [prefixWord, tailWord_6684027, baseEnd_6684027] using wordTrace_append hprefix tailTrace_6684027
  have hstable : (prefixWord ++ tailWord_6684027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684027).length < 2 ^ (prefixWord ++ tailWord_6684027).sum := by decide
  have hdescent : baseEnd_6684027 < baseStart_6684027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684104 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 4, 5]
def baseStart_6684104 : Nat := 118140960795 + 6684104 * 2 ^ 59
def prefixEnd_6684104 : Nat := 4983230072969 + 3 ^ 40 * 6684104 * 2
def baseEnd_6684104 : Nat := 1144052698880007215353457

theorem tailTrace_6684104 : CollatzResearch.WordTrace tailWord_6684104 prefixEnd_6684104 1144052698880007215353457 := by
  unfold tailWord_6684104
  simp only [CollatzResearch.WordTrace]
  refine ⟨121894650488320118462273683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162526200651093491283031577 121894650488320118462273683)
  ·
    refine ⟨182841975732480177693410525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121894650488320118462273683 182841975732480177693410525)
    ·
      refine ⟨68565740899680066635028947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182841975732480177693410525 68565740899680066635028947)
      ·
        refine ⟨102848611349520099952543421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68565740899680066635028947 102848611349520099952543421)
        ·
          refine ⟨38568229256070037482203783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102848611349520099952543421 38568229256070037482203783)
          ·
            refine ⟨57852343884105056223305675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38568229256070037482203783 57852343884105056223305675)
            ·
              refine ⟨86778515826157584334958513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57852343884105056223305675 86778515826157584334958513)
              ·
                refine ⟨65083886869618188251218885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86778515826157584334958513 65083886869618188251218885)
                ·
                  refine ⟨12203228788053410297103541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65083886869618188251218885 12203228788053410297103541)
                  ·
                    refine ⟨1144052698880007215353457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12203228788053410297103541 1144052698880007215353457)
                    ·
                      rfl

theorem cell23_6684104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_6684104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684104 prefixEnd_6684104 := by exact prefixLift 6684104
  have htrace : WordTrace (prefixWord ++ tailWord_6684104) baseStart_6684104 baseEnd_6684104 := by
    simpa [prefixWord, tailWord_6684104, baseEnd_6684104] using wordTrace_append hprefix tailTrace_6684104
  have hstable : (prefixWord ++ tailWord_6684104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684104).length < 2 ^ (prefixWord ++ tailWord_6684104).sum := by decide
  have hdescent : baseEnd_6684104 < baseStart_6684104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684121 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 2, 5]
def baseStart_6684121 : Nat := 118140960795 + 6684121 * 2 ^ 59
def prefixEnd_6684121 : Nat := 4983230072969 + 3 ^ 40 * 6684121 * 2
def baseEnd_6684121 : Nat := 1144055608603716026515931

theorem tailTrace_6684121 : CollatzResearch.WordTrace tailWord_6684121 prefixEnd_6684121 1144055608603716026515931 := by
  unfold tailWord_6684121
  simp only [CollatzResearch.WordTrace]
  refine ⟨243789921017578648827916217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162526614011719099218610811 243789921017578648827916217)
  ·
    refine ⟨182842440763183986620937163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243789921017578648827916217 182842440763183986620937163)
    ·
      refine ⟨274263661144775979931405745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182842440763183986620937163 274263661144775979931405745)
      ·
        refine ⟨205697745858581984948554309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274263661144775979931405745 205697745858581984948554309)
        ·
          refine ⟨38568327348484122177853933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205697745858581984948554309 38568327348484122177853933)
          ·
            refine ⟨14463122755681545816695225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38568327348484122177853933 14463122755681545816695225)
            ·
              refine ⟨10847342066761159362521419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14463122755681545816695225 10847342066761159362521419)
              ·
                refine ⟨16271013100141739043782129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10847342066761159362521419 16271013100141739043782129)
                ·
                  refine ⟨12203259825106304282836597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16271013100141739043782129 12203259825106304282836597)
                  ·
                    refine ⟨1144055608603716026515931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12203259825106304282836597 1144055608603716026515931)
                    ·
                      rfl

theorem cell23_6684121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 5].length) (baseStart_6684121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684121 prefixEnd_6684121 := by exact prefixLift 6684121
  have htrace : WordTrace (prefixWord ++ tailWord_6684121) baseStart_6684121 baseEnd_6684121 := by
    simpa [prefixWord, tailWord_6684121, baseEnd_6684121] using wordTrace_append hprefix tailTrace_6684121
  have hstable : (prefixWord ++ tailWord_6684121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684121).length < 2 ^ (prefixWord ++ tailWord_6684121).sum := by decide
  have hdescent : baseEnd_6684121 < baseStart_6684121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684241 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 6, 4]
def baseStart_6684241 : Nat := 118140960795 + 6684241 * 2 ^ 59
def prefixEnd_6684241 : Nat := 4983230072969 + 3 ^ 40 * 6684241 * 2
def baseEnd_6684241 : Nat := 1144076147829895870015747

theorem tailTrace_6684241 : CollatzResearch.WordTrace tailWord_6684241 prefixEnd_6684241 1144076147829895870015747 := by
  unfold tailWord_6684241
  simp only [CollatzResearch.WordTrace]
  refine ⟨243794297777143909322284577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162529531851429272881523051 243794297777143909322284577)
  ·
    refine ⟨182845723332857931991713433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243794297777143909322284577 182845723332857931991713433)
    ·
      refine ⟨137134292499643448993785075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182845723332857931991713433 137134292499643448993785075)
      ·
        refine ⟨205701438749465173490677613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137134292499643448993785075 205701438749465173490677613)
        ·
          refine ⟨77138039531049440059004105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205701438749465173490677613 77138039531049440059004105)
          ·
            refine ⟨57853529648287080044253079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77138039531049440059004105 57853529648287080044253079)
            ·
              refine ⟨86780294472430620066379619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57853529648287080044253079 86780294472430620066379619)
              ·
                refine ⟨130170441708645930099569429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86780294472430620066379619 130170441708645930099569429)
                ·
                  refine ⟨6101739455092777973417317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130170441708645930099569429 6101739455092777973417317)
                  ·
                    refine ⟨1144076147829895870015747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6101739455092777973417317 1144076147829895870015747)
                    ·
                      rfl

theorem cell23_6684241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_6684241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684241 prefixEnd_6684241 := by exact prefixLift 6684241
  have htrace : WordTrace (prefixWord ++ tailWord_6684241) baseStart_6684241 baseEnd_6684241 := by
    simpa [prefixWord, tailWord_6684241, baseEnd_6684241] using wordTrace_append hprefix tailTrace_6684241
  have hstable : (prefixWord ++ tailWord_6684241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684241).length < 2 ^ (prefixWord ++ tailWord_6684241).sum := by decide
  have hdescent : baseEnd_6684241 < baseStart_6684241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684242 : List Nat := [3, 2, 2, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_6684242 : Nat := 118140960795 + 6684242 * 2 ^ 59
def prefixEnd_6684242 : Nat := 4983230072969 + 3 ^ 40 * 6684242 * 2
def baseEnd_6684242 : Nat := 3432228956970342106134737

theorem tailTrace_6684242 : CollatzResearch.WordTrace tailWord_6684242 prefixEnd_6684242 3432228956970342106134737 := by
  unfold tailWord_6684242
  simp only [CollatzResearch.WordTrace]
  refine ⟨60948583562535071623267745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162529556166760190995380653 60948583562535071623267745)
  ·
    refine ⟨45711437671901303717450809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60948583562535071623267745 45711437671901303717450809)
    ·
      refine ⟨34283578253925977788088107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45711437671901303717450809 34283578253925977788088107)
      ·
        refine ⟨51425367380888966682132161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34283578253925977788088107 51425367380888966682132161)
        ·
          refine ⟨38569025535666725011599121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51425367380888966682132161 38569025535666725011599121)
          ·
            refine ⟨28926769151750043758699341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38569025535666725011599121 28926769151750043758699341)
            ·
              refine ⟨10847538431906266409512253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28926769151750043758699341 10847538431906266409512253)
              ·
                refine ⟨4067826911964849903567095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10847538431906266409512253 4067826911964849903567095)
                ·
                  refine ⟨6101740367947274855350643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067826911964849903567095 6101740367947274855350643)
                  ·
                    refine ⟨9152610551920912283025965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6101740367947274855350643 9152610551920912283025965)
                    ·
                      refine ⟨3432228956970342106134737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9152610551920912283025965 3432228956970342106134737)
                      ·
                        rfl

theorem cell23_6684242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_6684242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684242 prefixEnd_6684242 := by exact prefixLift 6684242
  have htrace : WordTrace (prefixWord ++ tailWord_6684242) baseStart_6684242 baseEnd_6684242 := by
    simpa [prefixWord, tailWord_6684242, baseEnd_6684242] using wordTrace_append hprefix tailTrace_6684242
  have hstable : (prefixWord ++ tailWord_6684242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684242).length < 2 ^ (prefixWord ++ tailWord_6684242).sum := by decide
  have hdescent : baseEnd_6684242 < baseStart_6684242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684261 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_6684261 : Nat := 118140960795 + 6684261 * 2 ^ 59
def prefixEnd_6684261 : Nat := 4983230072969 + 3 ^ 40 * 6684261 * 2
def baseEnd_6684261 : Nat := 3432238713102777531797149

theorem tailTrace_6684261 : CollatzResearch.WordTrace tailWord_6684261 prefixEnd_6684261 3432238713102777531797149 := by
  unfold tailWord_6684261
  simp only [CollatzResearch.WordTrace]
  refine ⟨243795027237071452738012637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162530018158047635158675091 243795027237071452738012637)
  ·
    refine ⟨91423135213901794776754739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243795027237071452738012637 91423135213901794776754739)
    ·
      refine ⟨137134702820852692165132109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91423135213901794776754739 137134702820852692165132109)
      ·
        refine ⟨51425513557819759561924541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137134702820852692165132109 51425513557819759561924541)
        ·
          refine ⟨19284567584182409835721703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51425513557819759561924541 19284567584182409835721703)
          ·
            refine ⟨28926851376273614753582555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19284567584182409835721703 28926851376273614753582555)
            ·
              refine ⟨43390277064410422130373833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28926851376273614753582555 43390277064410422130373833)
              ·
                refine ⟨32542707798307816597780375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43390277064410422130373833 32542707798307816597780375)
                ·
                  refine ⟨48814061697461724896670563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32542707798307816597780375 48814061697461724896670563)
                  ·
                    refine ⟨73221092546192587345005845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48814061697461724896670563 73221092546192587345005845)
                    ·
                      refine ⟨3432238713102777531797149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73221092546192587345005845 3432238713102777531797149)
                      ·
                        rfl

theorem cell23_6684261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_6684261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684261 prefixEnd_6684261 := by exact prefixLift 6684261
  have htrace : WordTrace (prefixWord ++ tailWord_6684261) baseStart_6684261 baseEnd_6684261 := by
    simpa [prefixWord, tailWord_6684261, baseEnd_6684261] using wordTrace_append hprefix tailTrace_6684261
  have hstable : (prefixWord ++ tailWord_6684261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684261).length < 2 ^ (prefixWord ++ tailWord_6684261).sum := by decide
  have hdescent : baseEnd_6684261 < baseStart_6684261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684265 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 3, 2, 2]
def baseStart_6684265 : Nat := 118140960795 + 6684265 * 2 ^ 59
def prefixEnd_6684265 : Nat := 4983230072969 + 3 ^ 40 * 6684265 * 2
def baseEnd_6684265 : Nat := 3432240767025395516147131

theorem tailTrace_6684265 : CollatzResearch.WordTrace tailWord_6684265 prefixEnd_6684265 3432240767025395516147131 := by
  unfold tailWord_6684265
  simp only [CollatzResearch.WordTrace]
  refine ⟨243795173129056961421158249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162530115419371307614105499 243795173129056961421158249)
  ·
    refine ⟨182846379846792721065868687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243795173129056961421158249 182846379846792721065868687)
    ·
      refine ⟨274269569770189081598803031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182846379846792721065868687 274269569770189081598803031)
      ·
        refine ⟨411404354655283622398204547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274269569770189081598803031 411404354655283622398204547)
        ·
          refine ⟨617106531982925433597306821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411404354655283622398204547 617106531982925433597306821)
          ·
            refine ⟨115707474746798518799495029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 617106531982925433597306821 115707474746798518799495029)
            ·
              refine ⟨10847575757512361137452659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115707474746798518799495029 10847575757512361137452659)
              ·
                refine ⟨16271363636268541706178989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10847575757512361137452659 16271363636268541706178989)
                ·
                  refine ⟨6101761363600703139817121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16271363636268541706178989 6101761363600703139817121)
                  ·
                    refine ⟨4576321022700527354862841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6101761363600703139817121 4576321022700527354862841)
                    ·
                      refine ⟨3432240767025395516147131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4576321022700527354862841 3432240767025395516147131)
                      ·
                        rfl

theorem cell23_6684265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 2, 2].length) (baseStart_6684265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684265 prefixEnd_6684265 := by exact prefixLift 6684265
  have htrace : WordTrace (prefixWord ++ tailWord_6684265) baseStart_6684265 baseEnd_6684265 := by
    simpa [prefixWord, tailWord_6684265, baseEnd_6684265] using wordTrace_append hprefix tailTrace_6684265
  have hstable : (prefixWord ++ tailWord_6684265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684265).length < 2 ^ (prefixWord ++ tailWord_6684265).sum := by decide
  have hdescent : baseEnd_6684265 < baseStart_6684265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684278 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_6684278 : Nat := 118140960795 + 6684278 * 2 ^ 59
def prefixEnd_6684278 : Nat := 4983230072969 + 3 ^ 40 * 6684278 * 2
def baseEnd_6684278 : Nat := 3432247442273903965284571

theorem tailTrace_6684278 : CollatzResearch.WordTrace tailWord_6684278 prefixEnd_6684278 3432247442273903965284571 := by
  unfold tailWord_6684278
  simp only [CollatzResearch.WordTrace]
  refine ⟨15237227954875616540086343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162530431518673243094254325 15237227954875616540086343)
  ·
    refine ⟨22855841932313424810129515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15237227954875616540086343 22855841932313424810129515)
    ·
      refine ⟨34283762898470137215194273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22855841932313424810129515 34283762898470137215194273)
      ·
        refine ⟨25712822173852602911395705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34283762898470137215194273 25712822173852602911395705)
        ·
          refine ⟨19284616630389452183546779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25712822173852602911395705 19284616630389452183546779)
          ·
            refine ⟨28926924945584178275320169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19284616630389452183546779 28926924945584178275320169)
            ·
              refine ⟨21695193709188133706490127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28926924945584178275320169 21695193709188133706490127)
              ·
                refine ⟨32542790563782200559735191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21695193709188133706490127 32542790563782200559735191)
                ·
                  refine ⟨48814185845673300839602787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32542790563782200559735191 48814185845673300839602787)
                  ·
                    refine ⟨73221278768509951259404181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48814185845673300839602787 73221278768509951259404181)
                    ·
                      refine ⟨3432247442273903965284571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73221278768509951259404181 3432247442273903965284571)
                      ·
                        rfl

theorem cell23_6684278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_6684278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684278 prefixEnd_6684278 := by exact prefixLift 6684278
  have htrace : WordTrace (prefixWord ++ tailWord_6684278) baseStart_6684278 baseEnd_6684278 := by
    simpa [prefixWord, tailWord_6684278, baseEnd_6684278] using wordTrace_append hprefix tailTrace_6684278
  have hstable : (prefixWord ++ tailWord_6684278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684278).length < 2 ^ (prefixWord ++ tailWord_6684278).sum := by decide
  have hdescent : baseEnd_6684278 < baseStart_6684278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684285 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_6684285 : Nat := 118140960795 + 6684285 * 2 ^ 59
def prefixEnd_6684285 : Nat := 4983230072969 + 3 ^ 40 * 6684285 * 2
def baseEnd_6684285 : Nat := 3432251036638485437897039

theorem tailTrace_6684285 : CollatzResearch.WordTrace tailWord_6684285 prefixEnd_6684285 3432251036638485437897039 := by
  unfold tailWord_6684285
  simp only [CollatzResearch.WordTrace]
  refine ⟨243795902588984504836886309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162530601725989669891257539 243795902588984504836886309)
  ·
    refine ⟨45711731735434594656916183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243795902588984504836886309 45711731735434594656916183)
    ·
      refine ⟨68567597603151891985374275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45711731735434594656916183 68567597603151891985374275)
      ·
        refine ⟨102851396404727837978061413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68567597603151891985374275 102851396404727837978061413)
        ·
          refine ⟨19284636825886469620886515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102851396404727837978061413 19284636825886469620886515)
          ·
            refine ⟨28926955238829704431329773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19284636825886469620886515 28926955238829704431329773)
            ·
              refine ⟨10847608214561139161748665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28926955238829704431329773 10847608214561139161748665)
              ·
                refine ⟨8135706160920854371311499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10847608214561139161748665 8135706160920854371311499)
                ·
                  refine ⟨12203559241381281556967249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8135706160920854371311499 12203559241381281556967249)
                  ·
                    refine ⟨9152669431035961167725437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12203559241381281556967249 9152669431035961167725437)
                    ·
                      refine ⟨3432251036638485437897039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9152669431035961167725437 3432251036638485437897039)
                      ·
                        rfl

theorem cell23_6684285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_6684285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684285 prefixEnd_6684285 := by exact prefixLift 6684285
  have htrace : WordTrace (prefixWord ++ tailWord_6684285) baseStart_6684285 baseEnd_6684285 := by
    simpa [prefixWord, tailWord_6684285, baseEnd_6684285] using wordTrace_append hprefix tailTrace_6684285
  have hstable : (prefixWord ++ tailWord_6684285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684285).length < 2 ^ (prefixWord ++ tailWord_6684285).sum := by decide
  have hdescent : baseEnd_6684285 < baseStart_6684285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684298 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_6684298 : Nat := 118140960795 + 6684298 * 2 ^ 59
def prefixEnd_6684298 : Nat := 4983230072969 + 3 ^ 40 * 6684298 * 2
def baseEnd_6684298 : Nat := 3432257711886993887034479

theorem tailTrace_6684298 : CollatzResearch.WordTrace tailWord_6684298 prefixEnd_6684298 3432257711886993887034479 := by
  unfold tailWord_6684298
  simp only [CollatzResearch.WordTrace]
  refine ⟨60949094184484352014277387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162530917825291605371406365 60949094184484352014277387)
  ·
    refine ⟨91423641276726528021416081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60949094184484352014277387 91423641276726528021416081)
    ·
      refine ⟨68567730957544896016062061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91423641276726528021416081 68567730957544896016062061)
      ·
        refine ⟨25712899109079336006023273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68567730957544896016062061 25712899109079336006023273)
        ·
          refine ⟨19284674331809502004517455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25712899109079336006023273 19284674331809502004517455)
          ·
            refine ⟨28927011497714253006776183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19284674331809502004517455 28927011497714253006776183)
            ·
              refine ⟨43390517246571379510164275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28927011497714253006776183 43390517246571379510164275)
              ·
                refine ⟨65085775869857069265246413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43390517246571379510164275 65085775869857069265246413)
                ·
                  refine ⟨24407165951196400974467405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65085775869857069265246413 24407165951196400974467405)
                  ·
                    refine ⟨9152687231698650365425277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24407165951196400974467405 9152687231698650365425277)
                    ·
                      refine ⟨3432257711886993887034479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9152687231698650365425277 3432257711886993887034479)
                      ·
                        rfl

theorem cell23_6684298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_6684298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684298 prefixEnd_6684298 := by exact prefixLift 6684298
  have htrace : WordTrace (prefixWord ++ tailWord_6684298) baseStart_6684298 baseEnd_6684298 := by
    simpa [prefixWord, tailWord_6684298, baseEnd_6684298] using wordTrace_append hprefix tailTrace_6684298
  have hstable : (prefixWord ++ tailWord_6684298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684298).length < 2 ^ (prefixWord ++ tailWord_6684298).sum := by decide
  have hdescent : baseEnd_6684298 < baseStart_6684298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684302 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3]
def baseStart_6684302 : Nat := 118140960795 + 6684302 * 2 ^ 59
def prefixEnd_6684302 : Nat := 4983230072969 + 3 ^ 40 * 6684302 * 2
def baseEnd_6684302 : Nat := 3432259765809611871384461

theorem tailTrace_6684302 : CollatzResearch.WordTrace tailWord_6684302 prefixEnd_6684302 3432259765809611871384461 := by
  unfold tailWord_6684302
  simp only [CollatzResearch.WordTrace]
  refine ⟨30474565328740364592531895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162531015086615277826836773 30474565328740364592531895)
  ·
    refine ⟨45711847993110546888797843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30474565328740364592531895 45711847993110546888797843)
    ·
      refine ⟨68567771989665820333196765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45711847993110546888797843 68567771989665820333196765)
      ·
        refine ⟨25712914496124682624948787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68567771989665820333196765 25712914496124682624948787)
        ·
          refine ⟨38569371744187023937423181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25712914496124682624948787 38569371744187023937423181)
          ·
            refine ⟨14463514404070133976533693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38569371744187023937423181 14463514404070133976533693)
            ·
              refine ⟨5423817901526300241200135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14463514404070133976533693 5423817901526300241200135)
              ·
                refine ⟨8135726852289450361800203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5423817901526300241200135 8135726852289450361800203)
                ·
                  refine ⟨12203590278434175542700305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8135726852289450361800203 12203590278434175542700305)
                  ·
                    refine ⟨9152692708825631657025229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12203590278434175542700305 9152692708825631657025229)
                    ·
                      refine ⟨3432259765809611871384461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9152692708825631657025229 3432259765809611871384461)
                      ·
                        rfl

theorem cell23_6684302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_6684302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684302 prefixEnd_6684302 := by exact prefixLift 6684302
  have htrace : WordTrace (prefixWord ++ tailWord_6684302) baseStart_6684302 baseEnd_6684302 := by
    simpa [prefixWord, tailWord_6684302, baseEnd_6684302] using wordTrace_append hprefix tailTrace_6684302
  have hstable : (prefixWord ++ tailWord_6684302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684302).length < 2 ^ (prefixWord ++ tailWord_6684302).sum := by decide
  have hdescent : baseEnd_6684302 < baseStart_6684302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684318 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_6684318 : Nat := 118140960795 + 6684318 * 2 ^ 59
def prefixEnd_6684318 : Nat := 4983230072969 + 3 ^ 40 * 6684318 * 2
def baseEnd_6684318 : Nat := 1144089327166694602928129

theorem tailTrace_6684318 : CollatzResearch.WordTrace tailWord_6684318 prefixEnd_6684318 1144089327166694602928129 := by
  unfold tailWord_6684318
  simp only [CollatzResearch.WordTrace]
  refine ⟨30474638274733118934104701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162531404131909967648558405 30474638274733118934104701)
  ·
    refine ⟨11427989353024919600289263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30474638274733118934104701 11427989353024919600289263)
    ·
      refine ⟨17141984029537379400433895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11427989353024919600289263 17141984029537379400433895)
      ·
        refine ⟨25712976044306069100650843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17141984029537379400433895 25712976044306069100650843)
        ·
          refine ⟨38569464066459103650976265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25712976044306069100650843 38569464066459103650976265)
          ·
            refine ⟨28927098049844327738232199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38569464066459103650976265 28927098049844327738232199)
            ·
              refine ⟨43390647074766491607348299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28927098049844327738232199 43390647074766491607348299)
              ·
                refine ⟨65085970612149737411022449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43390647074766491607348299 65085970612149737411022449)
                ·
                  refine ⟨48814477959112303058266837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65085970612149737411022449 48814477959112303058266837)
                  ·
                    refine ⟨1144089327166694602928129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48814477959112303058266837 1144089327166694602928129)
                    ·
                      rfl

theorem cell23_6684318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_6684318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684318 prefixEnd_6684318 := by exact prefixLift 6684318
  have htrace : WordTrace (prefixWord ++ tailWord_6684318) baseStart_6684318 baseEnd_6684318 := by
    simpa [prefixWord, tailWord_6684318, baseEnd_6684318] using wordTrace_append hprefix tailTrace_6684318
  have hstable : (prefixWord ++ tailWord_6684318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684318).length < 2 ^ (prefixWord ++ tailWord_6684318).sum := by decide
  have hdescent : baseEnd_6684318 < baseStart_6684318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684322 : List Nat := [3, 3, 1, 4, 2, 1, 1, 8]
def baseStart_6684322 : Nat := 118140960795 + 6684322 * 2 ^ 59
def prefixEnd_6684322 : Nat := 4983230072969 + 3 ^ 40 * 6684322 * 2
def baseEnd_6684322 : Nat := 127121112423063029375347

theorem tailTrace_6684322 : CollatzResearch.WordTrace tailWord_6684322 prefixEnd_6684322 127121112423063029375347 := by
  unfold tailWord_6684322
  simp only [CollatzResearch.WordTrace]
  refine ⟨60949313022462615038995805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162531501393233640103988813 60949313022462615038995805)
  ·
    refine ⟨22855992383423480639623427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60949313022462615038995805 22855992383423480639623427)
    ·
      refine ⟨34283988575135220959435141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22855992383423480639623427 34283988575135220959435141)
      ·
        refine ⟨6428247857837853929894089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34283988575135220959435141 6428247857837853929894089)
        ·
          refine ⟨4821185893378390447420567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6428247857837853929894089 4821185893378390447420567)
          ·
            refine ⟨7231778840067585671130851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4821185893378390447420567 7231778840067585671130851)
            ·
              refine ⟨10847668260101378506696277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7231778840067585671130851 10847668260101378506696277)
              ·
                refine ⟨127121112423063029375347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10847668260101378506696277 127121112423063029375347)
                ·
                  rfl

theorem cell23_6684322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 8].length) (baseStart_6684322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684322 prefixEnd_6684322 := by exact prefixLift 6684322
  have htrace : WordTrace (prefixWord ++ tailWord_6684322) baseStart_6684322 baseEnd_6684322 := by
    simpa [prefixWord, tailWord_6684322, baseEnd_6684322] using wordTrace_append hprefix tailTrace_6684322
  have hstable : (prefixWord ++ tailWord_6684322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684322).length < 2 ^ (prefixWord ++ tailWord_6684322).sum := by decide
  have hdescent : baseEnd_6684322 < baseStart_6684322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684351 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 4]
def baseStart_6684351 : Nat := 118140960795 + 6684351 * 2 ^ 59
def prefixEnd_6684351 : Nat := 4983230072969 + 3 ^ 40 * 6684351 * 2
def baseEnd_6684351 : Nat := 3432284926361682179671735

theorem tailTrace_6684351 : CollatzResearch.WordTrace tailWord_6684351 prefixEnd_6684351 3432284926361682179671735 := by
  unfold tailWord_6684351
  simp only [CollatzResearch.WordTrace]
  refine ⟨243798309806745398108788907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162532206537830265405859271 243798309806745398108788907)
  ·
    refine ⟨365697464710118097163183361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243798309806745398108788907 365697464710118097163183361)
    ·
      refine ⟨274273098532588572872387521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365697464710118097163183361 274273098532588572872387521)
      ·
        refine ⟨205704823899441429654290641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274273098532588572872387521 205704823899441429654290641)
        ·
          refine ⟨154278617924581072240717981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205704823899441429654290641 154278617924581072240717981)
          ·
            refine ⟨57854481721717902090269243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154278617924581072240717981 57854481721717902090269243)
            ·
              refine ⟨86781722582576853135403865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57854481721717902090269243 86781722582576853135403865)
              ·
                refine ⟨65086291936932639851552899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86781722582576853135403865 65086291936932639851552899)
                ·
                  refine ⟨97629437905398959777329349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65086291936932639851552899 97629437905398959777329349)
                  ·
                    refine ⟨18305519607262304958249253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97629437905398959777329349 18305519607262304958249253)
                    ·
                      refine ⟨3432284926361682179671735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18305519607262304958249253 3432284926361682179671735)
                      ·
                        rfl

theorem cell23_6684351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_6684351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684351 prefixEnd_6684351 := by exact prefixLift 6684351
  have htrace : WordTrace (prefixWord ++ tailWord_6684351) baseStart_6684351 baseEnd_6684351 := by
    simpa [prefixWord, tailWord_6684351, baseEnd_6684351] using wordTrace_append hprefix tailTrace_6684351
  have hstable : (prefixWord ++ tailWord_6684351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684351).length < 2 ^ (prefixWord ++ tailWord_6684351).sum := by decide
  have hdescent : baseEnd_6684351 < baseStart_6684351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684365 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_6684365 : Nat := 118140960795 + 6684365 * 2 ^ 59
def prefixEnd_6684365 : Nat := 4983230072969 + 3 ^ 40 * 6684365 * 2
def baseEnd_6684365 : Nat := 1144097371696948374965557

theorem tailTrace_6684365 : CollatzResearch.WordTrace tailWord_6684365 prefixEnd_6684365 1144097371696948374965557 := by
  unfold tailWord_6684365
  simp only [CollatzResearch.WordTrace]
  refine ⟨243798820428694678499798549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162532546952463118999865699 243798820428694678499798549)
  ·
    refine ⟨11428069707595063054678057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 243798820428694678499798549 11428069707595063054678057)
    ·
      refine ⟨8571052280696297291008543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11428069707595063054678057 8571052280696297291008543)
      ·
        refine ⟨12856578421044445936512815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8571052280696297291008543 12856578421044445936512815)
        ·
          refine ⟨19284867631566668904769223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12856578421044445936512815 19284867631566668904769223)
          ·
            refine ⟨28927301447350003357153835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19284867631566668904769223 28927301447350003357153835)
            ·
              refine ⟨43390952171025005035730753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28927301447350003357153835 43390952171025005035730753)
              ·
                refine ⟨32543214128268753776798065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43390952171025005035730753 32543214128268753776798065)
                ·
                  refine ⟨24407410596201565332598549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32543214128268753776798065 24407410596201565332598549)
                  ·
                    refine ⟨1144097371696948374965557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24407410596201565332598549 1144097371696948374965557)
                    ·
                      rfl

theorem cell23_6684365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_6684365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684365 prefixEnd_6684365 := by exact prefixLift 6684365
  have htrace : WordTrace (prefixWord ++ tailWord_6684365) baseStart_6684365 baseEnd_6684365 := by
    simpa [prefixWord, tailWord_6684365, baseEnd_6684365] using wordTrace_append hprefix tailTrace_6684365
  have hstable : (prefixWord ++ tailWord_6684365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684365).length < 2 ^ (prefixWord ++ tailWord_6684365).sum := by decide
  have hdescent : baseEnd_6684365 < baseStart_6684365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684378 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 7]
def baseStart_6684378 : Nat := 118140960795 + 6684378 * 2 ^ 59
def prefixEnd_6684378 : Nat := 4983230072969 + 3 ^ 40 * 6684378 * 2
def baseEnd_6684378 : Nat := 381366532259928174892679

theorem tailTrace_6684378 : CollatzResearch.WordTrace tailWord_6684378 prefixEnd_6684378 381366532259928174892679 := by
  unfold tailWord_6684378
  simp only [CollatzResearch.WordTrace]
  refine ⟨60949823644411895430005447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162532863051765054480014525 60949823644411895430005447)
  ·
    refine ⟨91424735466617843145008171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60949823644411895430005447 91424735466617843145008171)
    ·
      refine ⟨137137103199926764717512257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91424735466617843145008171 137137103199926764717512257)
      ·
        refine ⟨102852827399945073538134193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137137103199926764717512257 102852827399945073538134193)
        ·
          refine ⟨77139620549958805153600645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102852827399945073538134193 77139620549958805153600645)
          ·
            refine ⟨14463678853117275966300121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77139620549958805153600645 14463678853117275966300121)
            ·
              refine ⟨10847759139837956974725091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14463678853117275966300121 10847759139837956974725091)
              ·
                refine ⟨16271638709756935462087637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10847759139837956974725091 16271638709756935462087637)
                ·
                  refine ⟨381366532259928174892679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16271638709756935462087637 381366532259928174892679)
                  ·
                    rfl

theorem cell23_6684378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_6684378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684378 prefixEnd_6684378 := by exact prefixLift 6684378
  have htrace : WordTrace (prefixWord ++ tailWord_6684378) baseStart_6684378 baseEnd_6684378 := by
    simpa [prefixWord, tailWord_6684378, baseEnd_6684378] using wordTrace_append hprefix tailTrace_6684378
  have hstable : (prefixWord ++ tailWord_6684378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684378).length < 2 ^ (prefixWord ++ tailWord_6684378).sum := by decide
  have hdescent : baseEnd_6684378 < baseStart_6684378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684388 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_6684388 : Nat := 118140960795 + 6684388 * 2 ^ 59
def prefixEnd_6684388 : Nat := 4983230072969 + 3 ^ 40 * 6684388 * 2
def baseEnd_6684388 : Nat := 3432303925145898534909065

theorem tailTrace_6684388 : CollatzResearch.WordTrace tailWord_6684388 prefixEnd_6684388 3432303925145898534909065 := by
  unfold tailWord_6684388
  simp only [CollatzResearch.WordTrace]
  refine ⟨121899829653805676713942909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162533106205074235618590545 121899829653805676713942909)
  ·
    refine ⟨45712436120177128767728591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121899829653805676713942909 45712436120177128767728591)
    ·
      refine ⟨68568654180265693151592887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45712436120177128767728591 68568654180265693151592887)
      ·
        refine ⟨102852981270398539727389331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68568654180265693151592887 102852981270398539727389331)
        ·
          refine ⟨154279471905597809591083997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102852981270398539727389331 154279471905597809591083997)
          ·
            refine ⟨57854801964599178596656499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154279471905597809591083997 57854801964599178596656499)
            ·
              refine ⟨86782202946898767894984749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57854801964599178596656499 86782202946898767894984749)
              ·
                refine ⟨32543326105087037960619281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86782202946898767894984749 32543326105087037960619281)
                ·
                  refine ⟨24407494578815278470464461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32543326105087037960619281 24407494578815278470464461)
                  ·
                    refine ⟨9152810467055729426424173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24407494578815278470464461 9152810467055729426424173)
                    ·
                      refine ⟨3432303925145898534909065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9152810467055729426424173 3432303925145898534909065)
                      ·
                        rfl

theorem cell23_6684388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_6684388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684388 prefixEnd_6684388 := by exact prefixLift 6684388
  have htrace : WordTrace (prefixWord ++ tailWord_6684388) baseStart_6684388 baseEnd_6684388 := by
    simpa [prefixWord, tailWord_6684388, baseEnd_6684388] using wordTrace_append hprefix tailTrace_6684388
  have hstable : (prefixWord ++ tailWord_6684388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684388).length < 2 ^ (prefixWord ++ tailWord_6684388).sum := by decide
  have hdescent : baseEnd_6684388 < baseStart_6684388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684389 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 2, 2, 2]
def baseStart_6684389 : Nat := 118140960795 + 6684389 * 2 ^ 59
def prefixEnd_6684389 : Nat := 4983230072969 + 3 ^ 40 * 6684389 * 2
def baseEnd_6684389 : Nat := 3432304438626553030996561

theorem tailTrace_6684389 : CollatzResearch.WordTrace tailWord_6684389 prefixEnd_6684389 3432304438626553030996561 := by
  unfold tailWord_6684389
  simp only [CollatzResearch.WordTrace]
  refine ⟨243799695780607730598672221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162533130520405153732448147 243799695780607730598672221)
  ·
    refine ⟨91424885917727898974502083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243799695780607730598672221 91424885917727898974502083)
    ·
      refine ⟨137137328876591848461753125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91424885917727898974502083 137137328876591848461753125)
      ·
        refine ⟨25713249164360971586578711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137137328876591848461753125 25713249164360971586578711)
        ·
          refine ⟨38569873746541457379868067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25713249164360971586578711 38569873746541457379868067)
          ·
            refine ⟨57854810619812186069802101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38569873746541457379868067 57854810619812186069802101)
            ·
              refine ⟨5423888495607392444043947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57854810619812186069802101 5423888495607392444043947)
              ·
                refine ⟨8135832743411088666065921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5423888495607392444043947 8135832743411088666065921)
                ·
                  refine ⟨6101874557558316499549441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8135832743411088666065921 6101874557558316499549441)
                  ·
                    refine ⟨4576405918168737374662081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6101874557558316499549441 4576405918168737374662081)
                    ·
                      refine ⟨3432304438626553030996561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4576405918168737374662081 3432304438626553030996561)
                      ·
                        rfl

theorem cell23_6684389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_6684389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684389 prefixEnd_6684389 := by exact prefixLift 6684389
  have htrace : WordTrace (prefixWord ++ tailWord_6684389) baseStart_6684389 baseEnd_6684389 := by
    simpa [prefixWord, tailWord_6684389, baseEnd_6684389] using wordTrace_append hprefix tailTrace_6684389
  have hstable : (prefixWord ++ tailWord_6684389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684389).length < 2 ^ (prefixWord ++ tailWord_6684389).sum := by decide
  have hdescent : baseEnd_6684389 < baseStart_6684389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684428 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_6684428 : Nat := 118140960795 + 6684428 * 2 ^ 59
def prefixEnd_6684428 : Nat := 4983230072969 + 3 ^ 40 * 6684428 * 2
def baseEnd_6684428 : Nat := 3432324464372078378408881

theorem tailTrace_6684428 : CollatzResearch.WordTrace tailWord_6684428 prefixEnd_6684428 3432324464372078378408881 := by
  unfold tailWord_6684428
  simp only [CollatzResearch.WordTrace]
  refine ⟨121900559113733220129670969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162534078818310960172894625 121900559113733220129670969)
  ·
    refine ⟨91425419335299915097253227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121900559113733220129670969 91425419335299915097253227)
    ·
      refine ⟨137138129002949872645879841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91425419335299915097253227 137138129002949872645879841)
      ·
        refine ⟨102853596752212404484409881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137138129002949872645879841 102853596752212404484409881)
        ·
          refine ⟨77140197564159303363307411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102853596752212404484409881 77140197564159303363307411)
          ·
            refine ⟨115710296346238955044961117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77140197564159303363307411 115710296346238955044961117)
            ·
              refine ⟨43391361129839608141860419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115710296346238955044961117 43391361129839608141860419)
              ·
                refine ⟨65087041694759412212790629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43391361129839608141860419 65087041694759412212790629)
                ·
                  refine ⟨12203820317767389789898243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65087041694759412212790629 12203820317767389789898243)
                  ·
                    refine ⟨18305730476651084684847365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12203820317767389789898243 18305730476651084684847365)
                    ·
                      refine ⟨3432324464372078378408881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18305730476651084684847365 3432324464372078378408881)
                      ·
                        rfl

theorem cell23_6684428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_6684428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684428 prefixEnd_6684428 := by exact prefixLift 6684428
  have htrace : WordTrace (prefixWord ++ tailWord_6684428) baseStart_6684428 baseEnd_6684428 := by
    simpa [prefixWord, tailWord_6684428, baseEnd_6684428] using wordTrace_append hprefix tailTrace_6684428
  have hstable : (prefixWord ++ tailWord_6684428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684428).length < 2 ^ (prefixWord ++ tailWord_6684428).sum := by decide
  have hdescent : baseEnd_6684428 < baseStart_6684428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684431 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_6684431 : Nat := 118140960795 + 6684431 * 2 ^ 59
def prefixEnd_6684431 : Nat := 4983230072969 + 3 ^ 40 * 6684431 * 2
def baseEnd_6684431 : Nat := 3432326004814041866671367

theorem tailTrace_6684431 : CollatzResearch.WordTrace tailWord_6684431 prefixEnd_6684431 3432326004814041866671367 := by
  unfold tailWord_6684431
  simp only [CollatzResearch.WordTrace]
  refine ⟨243801227646455571771701147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162534151764303714514467431 243801227646455571771701147)
  ·
    refine ⟨365701841469683357657551721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243801227646455571771701147 365701841469683357657551721)
    ·
      refine ⟨274276381102262518243163791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365701841469683357657551721 274276381102262518243163791)
      ·
        refine ⟨411414571653393777364745687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274276381102262518243163791 411414571653393777364745687)
        ·
          refine ⟨617121857480090666047118531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411414571653393777364745687 617121857480090666047118531)
          ·
            refine ⟨925682786220135999070677797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617121857480090666047118531 925682786220135999070677797)
            ·
              refine ⟨173565522416275499825752087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 925682786220135999070677797 173565522416275499825752087)
              ·
                refine ⟨260348283624413249738628131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173565522416275499825752087 260348283624413249738628131)
                ·
                  refine ⟨390522425436619874607942197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260348283624413249738628131 390522425436619874607942197)
                  ·
                    refine ⟨36611477384683113244494581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 390522425436619874607942197 36611477384683113244494581)
                    ·
                      refine ⟨3432326004814041866671367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36611477384683113244494581 3432326004814041866671367)
                      ·
                        rfl

theorem cell23_6684431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_6684431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684431 prefixEnd_6684431 := by exact prefixLift 6684431
  have htrace : WordTrace (prefixWord ++ tailWord_6684431) baseStart_6684431 baseEnd_6684431 := by
    simpa [prefixWord, tailWord_6684431, baseEnd_6684431] using wordTrace_append hprefix tailTrace_6684431
  have hstable : (prefixWord ++ tailWord_6684431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684431).length < 2 ^ (prefixWord ++ tailWord_6684431).sum := by decide
  have hdescent : baseEnd_6684431 < baseStart_6684431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684441 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_6684441 : Nat := 118140960795 + 6684441 * 2 ^ 59
def prefixEnd_6684441 : Nat := 4983230072969 + 3 ^ 40 * 6684441 * 2
def baseEnd_6684441 : Nat := 3432331139620586827546321

theorem tailTrace_6684441 : CollatzResearch.WordTrace tailWord_6684441 prefixEnd_6684441 3432331139620586827546321 := by
  unfold tailWord_6684441
  simp only [CollatzResearch.WordTrace]
  refine ⟨243801592376419343479565177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162534394917612895653043451 243801592376419343479565177)
  ·
    refine ⟨182851194282314507609673883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243801592376419343479565177 182851194282314507609673883)
    ·
      refine ⟨274276791423471761414510825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182851194282314507609673883 274276791423471761414510825)
      ·
        refine ⟨205707593567603821060883119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274276791423471761414510825 205707593567603821060883119)
        ·
          refine ⟨308561390351405731591324679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205707593567603821060883119 308561390351405731591324679)
          ·
            refine ⟨462842085527108597386987019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308561390351405731591324679 462842085527108597386987019)
            ·
              refine ⟨694263128290662896080480529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462842085527108597386987019 694263128290662896080480529)
              ·
                refine ⟨520697346217997172060360397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694263128290662896080480529 520697346217997172060360397)
                ·
                  refine ⟨195261504831748939522635149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520697346217997172060360397 195261504831748939522635149)
                  ·
                    refine ⟨73223064311905852320988181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195261504831748939522635149 73223064311905852320988181)
                    ·
                      refine ⟨3432331139620586827546321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73223064311905852320988181 3432331139620586827546321)
                      ·
                        rfl

theorem cell23_6684441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_6684441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684441 prefixEnd_6684441 := by exact prefixLift 6684441
  have htrace : WordTrace (prefixWord ++ tailWord_6684441) baseStart_6684441 baseEnd_6684441 := by
    simpa [prefixWord, tailWord_6684441, baseEnd_6684441] using wordTrace_append hprefix tailTrace_6684441
  have hstable : (prefixWord ++ tailWord_6684441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684441).length < 2 ^ (prefixWord ++ tailWord_6684441).sum := by decide
  have hdescent : baseEnd_6684441 < baseStart_6684441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684465 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 2, 2, 3]
def baseStart_6684465 : Nat := 118140960795 + 6684465 * 2 ^ 59
def prefixEnd_6684465 : Nat := 4983230072969 + 3 ^ 40 * 6684465 * 2
def baseEnd_6684465 : Nat := 3432343463156294733646211

theorem tailTrace_6684465 : CollatzResearch.WordTrace tailWord_6684465 prefixEnd_6684465 3432343463156294733646211 := by
  unfold tailWord_6684465
  simp only [CollatzResearch.WordTrace]
  refine ⟨243802467728332395578438849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162534978485554930385625899 243802467728332395578438849)
  ·
    refine ⟨182851850796249296683829137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243802467728332395578438849 182851850796249296683829137)
    ·
      refine ⟨137138888097186972512871853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182851850796249296683829137 137138888097186972512871853)
      ·
        refine ⟨51427083036445114692326945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137138888097186972512871853 51427083036445114692326945)
        ·
          refine ⟨38570312277333836019245209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51427083036445114692326945 38570312277333836019245209)
          ·
            refine ⟨28927734208000377014433907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38570312277333836019245209 28927734208000377014433907)
            ·
              refine ⟨43391601312000565521650861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28927734208000377014433907 43391601312000565521650861)
              ·
                refine ⟨16271850492000212070619073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43391601312000565521650861 16271850492000212070619073)
                ·
                  refine ⟨12203887869000159052964305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16271850492000212070619073 12203887869000159052964305)
                  ·
                    refine ⟨9152915901750119289723229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12203887869000159052964305 9152915901750119289723229)
                    ·
                      refine ⟨3432343463156294733646211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9152915901750119289723229 3432343463156294733646211)
                      ·
                        rfl

theorem cell23_6684465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_6684465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684465 prefixEnd_6684465 := by exact prefixLift 6684465
  have htrace : WordTrace (prefixWord ++ tailWord_6684465) baseStart_6684465 baseEnd_6684465 := by
    simpa [prefixWord, tailWord_6684465, baseEnd_6684465] using wordTrace_append hprefix tailTrace_6684465
  have hstable : (prefixWord ++ tailWord_6684465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684465).length < 2 ^ (prefixWord ++ tailWord_6684465).sum := by decide
  have hdescent : baseEnd_6684465 < baseStart_6684465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684505 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 1, 5, 2]
def baseStart_6684505 : Nat := 118140960795 + 6684505 * 2 ^ 59
def prefixEnd_6684505 : Nat := 4983230072969 + 3 ^ 40 * 6684505 * 2
def baseEnd_6684505 : Nat := 3432364002382474577146027

theorem tailTrace_6684505 : CollatzResearch.WordTrace tailWord_6684505 prefixEnd_6684505 3432364002382474577146027 := by
  unfold tailWord_6684505
  simp only [CollatzResearch.WordTrace]
  refine ⟨243803926648187482409894969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162535951098791654939929979 243803926648187482409894969)
  ·
    refine ⟨182852944986140611807421227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243803926648187482409894969 182852944986140611807421227)
    ·
      refine ⟨274279417479210917711131841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182852944986140611807421227 274279417479210917711131841)
      ·
        refine ⟨205709563109408188283348881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274279417479210917711131841 205709563109408188283348881)
        ·
          refine ⟨154282172332056141212511661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205709563109408188283348881 154282172332056141212511661)
          ·
            refine ⟨57855814624521052954691873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154282172332056141212511661 57855814624521052954691873)
            ·
              refine ⟨43391860968390789716018905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57855814624521052954691873 43391860968390789716018905)
              ·
                refine ⟨32543895726293092287014179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43391860968390789716018905 32543895726293092287014179)
                ·
                  refine ⟨48815843589439638430521269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32543895726293092287014179 48815843589439638430521269)
                  ·
                    refine ⟨4576485336509966102861369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48815843589439638430521269 4576485336509966102861369)
                    ·
                      refine ⟨3432364002382474577146027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4576485336509966102861369 3432364002382474577146027)
                      ·
                        rfl

theorem cell23_6684505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 5, 2].length) (baseStart_6684505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684505 prefixEnd_6684505 := by exact prefixLift 6684505
  have htrace : WordTrace (prefixWord ++ tailWord_6684505) baseStart_6684505 baseEnd_6684505 := by
    simpa [prefixWord, tailWord_6684505, baseEnd_6684505] using wordTrace_append hprefix tailTrace_6684505
  have hstable : (prefixWord ++ tailWord_6684505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684505).length < 2 ^ (prefixWord ++ tailWord_6684505).sum := by decide
  have hdescent : baseEnd_6684505 < baseStart_6684505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684512 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 3, 1, 3]
def baseStart_6684512 : Nat := 118140960795 + 6684512 * 2 ^ 59
def prefixEnd_6684512 : Nat := 4983230072969 + 3 ^ 40 * 6684512 * 2
def baseEnd_6684512 : Nat := 3432367596747056049758495

theorem tailTrace_6684512 : CollatzResearch.WordTrace tailWord_6684512 prefixEnd_6684512 3432367596747056049758495 := by
  unfold tailWord_6684512
  simp only [CollatzResearch.WordTrace]
  refine ⟨121902090979581061302699895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162536121306108081736933193 121902090979581061302699895)
  ·
    refine ⟨182853136469371591954049843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121902090979581061302699895 182853136469371591954049843)
    ·
      refine ⟨274279704704057387931074765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182853136469371591954049843 274279704704057387931074765)
      ·
        refine ⟨102854889264021520474153037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274279704704057387931074765 102854889264021520474153037)
        ·
          refine ⟨38570583474008070177807389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102854889264021520474153037 38570583474008070177807389)
          ·
            refine ⟨14463968802753026316677771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38570583474008070177807389 14463968802753026316677771)
            ·
              refine ⟨21695953204129539475016657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14463968802753026316677771 21695953204129539475016657)
              ·
                refine ⟨16271964903097154606262493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21695953204129539475016657 16271964903097154606262493)
                ·
                  refine ⟨6101986838661432977348435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16271964903097154606262493 6101986838661432977348435)
                  ·
                    refine ⟨9152980257992149466022653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6101986838661432977348435 9152980257992149466022653)
                    ·
                      refine ⟨3432367596747056049758495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9152980257992149466022653 3432367596747056049758495)
                      ·
                        rfl

theorem cell23_6684512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_6684512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684512 prefixEnd_6684512 := by exact prefixLift 6684512
  have htrace : WordTrace (prefixWord ++ tailWord_6684512) baseStart_6684512 baseEnd_6684512 := by
    simpa [prefixWord, tailWord_6684512, baseEnd_6684512] using wordTrace_append hprefix tailTrace_6684512
  have hstable : (prefixWord ++ tailWord_6684512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684512).length < 2 ^ (prefixWord ++ tailWord_6684512).sum := by decide
  have hdescent : baseEnd_6684512 < baseStart_6684512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684529 : List Nat := [1, 2, 2, 2, 1, 3, 4, 3, 1, 1, 3]
def baseStart_6684529 : Nat := 118140960795 + 6684529 * 2 ^ 59
def prefixEnd_6684529 : Nat := 4983230072969 + 3 ^ 40 * 6684529 * 2
def baseEnd_6684529 : Nat := 3432376325918182483245917

theorem tailTrace_6684529 : CollatzResearch.WordTrace tailWord_6684529 prefixEnd_6684529 3432376325918182483245917 := by
  unfold tailWord_6684529
  simp only [CollatzResearch.WordTrace]
  refine ⟨243804802000100534508768641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162536534666733689672512427 243804802000100534508768641)
  ·
    refine ⟨182853601500075400881576481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243804802000100534508768641 182853601500075400881576481)
    ·
      refine ⟨137140201125056550661182361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182853601500075400881576481 137140201125056550661182361)
      ·
        refine ⟨102855150843792412995886771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137140201125056550661182361 102855150843792412995886771)
        ·
          refine ⟨154282726265688619493830157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102855150843792412995886771 154282726265688619493830157)
          ·
            refine ⟨57856022349633232310186309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154282726265688619493830157 57856022349633232310186309)
            ·
              refine ⟨10848004190556231058159933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57856022349633232310186309 10848004190556231058159933)
              ·
                refine ⟨4068001571458586646809975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10848004190556231058159933 4068001571458586646809975)
                ·
                  refine ⟨6102002357187879970214963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068001571458586646809975 6102002357187879970214963)
                  ·
                    refine ⟨9153003535781819955322445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6102002357187879970214963 9153003535781819955322445)
                    ·
                      refine ⟨3432376325918182483245917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9153003535781819955322445 3432376325918182483245917)
                      ·
                        rfl

theorem cell23_6684529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_6684529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684529 prefixEnd_6684529 := by exact prefixLift 6684529
  have htrace : WordTrace (prefixWord ++ tailWord_6684529) baseStart_6684529 baseEnd_6684529 := by
    simpa [prefixWord, tailWord_6684529, baseEnd_6684529] using wordTrace_append hprefix tailTrace_6684529
  have hstable : (prefixWord ++ tailWord_6684529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684529).length < 2 ^ (prefixWord ++ tailWord_6684529).sum := by decide
  have hdescent : baseEnd_6684529 < baseStart_6684529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684562 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_6684562 : Nat := 118140960795 + 6684562 * 2 ^ 59
def prefixEnd_6684562 : Nat := 4983230072969 + 3 ^ 40 * 6684562 * 2
def baseEnd_6684562 : Nat := 1144131090259926951377755

theorem tailTrace_6684562 : CollatzResearch.WordTrace tailWord_6684562 prefixEnd_6684562 1144131090259926951377755 := by
  unfold tailWord_6684562
  simp only [CollatzResearch.WordTrace]
  refine ⟨60951501402245245286179985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162537337072653987429813293 60951501402245245286179985)
  ·
    refine ⟨45713626051683933964634989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60951501402245245286179985 45713626051683933964634989)
    ·
      refine ⟨17142609769381475236738121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45713626051683933964634989 17142609769381475236738121)
      ·
        refine ⟨12856957327036106427553591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17142609769381475236738121 12856957327036106427553591)
        ·
          refine ⟨19285435990554159641330387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12856957327036106427553591 19285435990554159641330387)
          ·
            refine ⟨28928153985831239461995581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19285435990554159641330387 28928153985831239461995581)
            ·
              refine ⟨10848057744686714798248343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28928153985831239461995581 10848057744686714798248343)
              ·
                refine ⟨16272086617030072197372515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10848057744686714798248343 16272086617030072197372515)
                ·
                  refine ⟨24408129925545108296058773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16272086617030072197372515 24408129925545108296058773)
                  ·
                    refine ⟨1144131090259926951377755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24408129925545108296058773 1144131090259926951377755)
                    ·
                      rfl

theorem cell23_6684562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_6684562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684562 prefixEnd_6684562 := by exact prefixLift 6684562
  have htrace : WordTrace (prefixWord ++ tailWord_6684562) baseStart_6684562 baseEnd_6684562 := by
    simpa [prefixWord, tailWord_6684562, baseEnd_6684562] using wordTrace_append hprefix tailTrace_6684562
  have hstable : (prefixWord ++ tailWord_6684562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684562).length < 2 ^ (prefixWord ++ tailWord_6684562).sum := by decide
  have hdescent : baseEnd_6684562 < baseStart_6684562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684575 : List Nat := [1, 1, 2, 5, 3, 1, 1, 9]
def baseStart_6684575 : Nat := 118140960795 + 6684575 * 2 ^ 59
def prefixEnd_6684575 : Nat := 4983230072969 + 3 ^ 40 * 6684575 * 2
def baseEnd_6684575 : Nat := 127125923926973677898915

theorem tailTrace_6684575 : CollatzResearch.WordTrace tailWord_6684575 prefixEnd_6684575 127125923926973677898915 := by
  unfold tailWord_6684575
  simp only [CollatzResearch.WordTrace]
  refine ⟨243806479757933884364943179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162537653171955922909962119 243806479757933884364943179)
  ·
    refine ⟨365709719636900826547414769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243806479757933884364943179 365709719636900826547414769)
    ·
      refine ⟨274282289727675619910561077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365709719636900826547414769 274282289727675619910561077)
      ·
        refine ⟨25713964661969589366615101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 274282289727675619910561077 25713964661969589366615101)
        ·
          refine ⟨9642736748238596012480663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25713964661969589366615101 9642736748238596012480663)
          ·
            refine ⟨14464105122357894018720995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9642736748238596012480663 14464105122357894018720995)
            ·
              refine ⟨21696157683536841028081493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14464105122357894018720995 21696157683536841028081493)
              ·
                refine ⟨127125923926973677898915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21696157683536841028081493 127125923926973677898915)
                ·
                  rfl

theorem cell23_6684575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 9].length) (baseStart_6684575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684575 prefixEnd_6684575 := by exact prefixLift 6684575
  have htrace : WordTrace (prefixWord ++ tailWord_6684575) baseStart_6684575 baseEnd_6684575 := by
    simpa [prefixWord, tailWord_6684575, baseEnd_6684575] using wordTrace_append hprefix tailTrace_6684575
  have hstable : (prefixWord ++ tailWord_6684575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684575).length < 2 ^ (prefixWord ++ tailWord_6684575).sum := by decide
  have hdescent : baseEnd_6684575 < baseStart_6684575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684629 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 3, 3, 2]
def baseStart_6684629 : Nat := 118140960795 + 6684629 * 2 ^ 59
def prefixEnd_6684629 : Nat := 4983230072969 + 3 ^ 40 * 6684629 * 2
def baseEnd_6684629 : Nat := 3432427673983632091995457

theorem tailTrace_6684629 : CollatzResearch.WordTrace tailWord_6684629 prefixEnd_6684629 3432427673983632091995457 := by
  unfold tailWord_6684629
  simp only [CollatzResearch.WordTrace]
  refine ⟨243808449299738251587408941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162538966199825501058272627 243808449299738251587408941)
  ·
    refine ⟨91428168487401844345278353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243808449299738251587408941 91428168487401844345278353)
    ·
      refine ⟨68571126365551383258958765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91428168487401844345278353 68571126365551383258958765)
      ·
        refine ⟨25714172387081768722109537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68571126365551383258958765 25714172387081768722109537)
        ·
          refine ⟨19285629290311326541582153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25714172387081768722109537 19285629290311326541582153)
          ·
            refine ⟨14464221967733494906186615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19285629290311326541582153 14464221967733494906186615)
            ·
              refine ⟨21696332951600242359279923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14464221967733494906186615 21696332951600242359279923)
              ·
                refine ⟨32544499427400363538919885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21696332951600242359279923 32544499427400363538919885)
                ·
                  refine ⟨12204187285275136327094957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32544499427400363538919885 12204187285275136327094957)
                  ·
                    refine ⟨4576570231978176122660609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12204187285275136327094957 4576570231978176122660609)
                    ·
                      refine ⟨3432427673983632091995457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4576570231978176122660609 3432427673983632091995457)
                      ·
                        rfl

theorem cell23_6684629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_6684629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684629 prefixEnd_6684629 := by exact prefixLift 6684629
  have htrace : WordTrace (prefixWord ++ tailWord_6684629) baseStart_6684629 baseEnd_6684629 := by
    simpa [prefixWord, tailWord_6684629, baseEnd_6684629] using wordTrace_append hprefix tailTrace_6684629
  have hstable : (prefixWord ++ tailWord_6684629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684629).length < 2 ^ (prefixWord ++ tailWord_6684629).sum := by decide
  have hdescent : baseEnd_6684629 < baseStart_6684629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684653 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6684653 : Nat := 118140960795 + 6684653 * 2 ^ 59
def prefixEnd_6684653 : Nat := 4983230072969 + 3 ^ 40 * 6684653 * 2
def baseEnd_6684653 : Nat := 3432439997519339998095347

theorem tailTrace_6684653 : CollatzResearch.WordTrace tailWord_6684653 prefixEnd_6684653 3432439997519339998095347 := by
  unfold tailWord_6684653
  simp only [CollatzResearch.WordTrace]
  refine ⟨243809324651651303686282613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162539549767767535790855075 243809324651651303686282613)
  ·
    refine ⟨22857124186092309720588995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243809324651651303686282613 22857124186092309720588995)
    ·
      refine ⟨34285686279138464580883493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22857124186092309720588995 34285686279138464580883493)
      ·
        refine ⟨6428566177338462108915655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34285686279138464580883493 6428566177338462108915655)
        ·
          refine ⟨9642849266007693163373483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6428566177338462108915655 9642849266007693163373483)
          ·
            refine ⟨14464273899011539745060225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9642849266007693163373483 14464273899011539745060225)
            ·
              refine ⟨10848205424258654808795169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14464273899011539745060225 10848205424258654808795169)
              ·
                refine ⟨8136154068193991106596377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10848205424258654808795169 8136154068193991106596377)
                ·
                  refine ⟨6102115551145493329947283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8136154068193991106596377 6102115551145493329947283)
                  ·
                    refine ⟨9153173326718239994920925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6102115551145493329947283 9153173326718239994920925)
                    ·
                      refine ⟨3432439997519339998095347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9153173326718239994920925 3432439997519339998095347)
                      ·
                        rfl

theorem cell23_6684653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6684653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684653 prefixEnd_6684653 := by exact prefixLift 6684653
  have htrace : WordTrace (prefixWord ++ tailWord_6684653) baseStart_6684653 baseEnd_6684653 := by
    simpa [prefixWord, tailWord_6684653, baseEnd_6684653] using wordTrace_append hprefix tailTrace_6684653
  have hstable : (prefixWord ++ tailWord_6684653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684653).length < 2 ^ (prefixWord ++ tailWord_6684653).sum := by decide
  have hdescent : baseEnd_6684653 < baseStart_6684653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684655 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 4]
def baseStart_6684655 : Nat := 118140960795 + 6684655 * 2 ^ 59
def prefixEnd_6684655 : Nat := 4983230072969 + 3 ^ 40 * 6684655 * 2
def baseEnd_6684655 : Nat := 3432441024480648990270337

theorem tailTrace_6684655 : CollatzResearch.WordTrace tailWord_6684655 prefixEnd_6684655 3432441024480648990270337 := by
  unfold tailWord_6684655
  simp only [CollatzResearch.WordTrace]
  refine ⟨243809397597644058027855419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162539598398429372018570279 243809397597644058027855419)
  ·
    refine ⟨365714096396466087041783129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243809397597644058027855419 365714096396466087041783129)
    ·
      refine ⟨274285572297349565281337347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365714096396466087041783129 274285572297349565281337347)
      ·
        refine ⟨411428358446024347922006021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274285572297349565281337347 411428358446024347922006021)
        ·
          refine ⟨77142817208629565235376129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 411428358446024347922006021 77142817208629565235376129)
          ·
            refine ⟨57857112906472173926532097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77142817208629565235376129 57857112906472173926532097)
            ·
              refine ⟨43392834679854130444899073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57857112906472173926532097 43392834679854130444899073)
              ·
                refine ⟨32544626009890597833674305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43392834679854130444899073 32544626009890597833674305)
                ·
                  refine ⟨24408469507417948375255729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32544626009890597833674305 24408469507417948375255729)
                  ·
                    refine ⟨18306352130563461281441797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24408469507417948375255729 18306352130563461281441797)
                    ·
                      refine ⟨3432441024480648990270337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18306352130563461281441797 3432441024480648990270337)
                      ·
                        rfl

theorem cell23_6684655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_6684655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684655 prefixEnd_6684655 := by exact prefixLift 6684655
  have htrace : WordTrace (prefixWord ++ tailWord_6684655) baseStart_6684655 baseEnd_6684655 := by
    simpa [prefixWord, tailWord_6684655, baseEnd_6684655] using wordTrace_append hprefix tailTrace_6684655
  have hstable : (prefixWord ++ tailWord_6684655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684655).length < 2 ^ (prefixWord ++ tailWord_6684655).sum := by decide
  have hdescent : baseEnd_6684655 < baseStart_6684655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684682 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 7]
def baseStart_6684682 : Nat := 118140960795 + 6684682 * 2 ^ 59
def prefixEnd_6684682 : Nat := 4983230072969 + 3 ^ 40 * 6684682 * 2
def baseEnd_6684682 : Nat := 381383876495368931625857

theorem tailTrace_6684682 : CollatzResearch.WordTrace tailWord_6684682 prefixEnd_6684682 381383876495368931625857 := by
  unfold tailWord_6684682
  simp only [CollatzResearch.WordTrace]
  refine ⟨60952595592136560409772075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162540254912364161092725533 60952595592136560409772075)
  ·
    refine ⟨91428893388204840614658113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60952595592136560409772075 91428893388204840614658113)
    ·
      refine ⟨68571670041153630460993585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91428893388204840614658113 68571670041153630460993585)
      ·
        refine ⟨51428752530865222845745189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68571670041153630460993585 51428752530865222845745189)
        ·
          refine ⟨9642891099537229283577223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51428752530865222845745189 9642891099537229283577223)
          ·
            refine ⟨14464336649305843925365835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9642891099537229283577223 14464336649305843925365835)
            ·
              refine ⟨21696504973958765888048753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14464336649305843925365835 21696504973958765888048753)
              ·
                refine ⟨16272378730469074416036565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21696504973958765888048753 16272378730469074416036565)
                ·
                  refine ⟨381383876495368931625857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16272378730469074416036565 381383876495368931625857)
                  ·
                    rfl

theorem cell23_6684682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_6684682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684682 prefixEnd_6684682 := by exact prefixLift 6684682
  have htrace : WordTrace (prefixWord ++ tailWord_6684682) baseStart_6684682 baseEnd_6684682 := by
    simpa [prefixWord, tailWord_6684682, baseEnd_6684682] using wordTrace_append hprefix tailTrace_6684682
  have hstable : (prefixWord ++ tailWord_6684682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684682).length < 2 ^ (prefixWord ++ tailWord_6684682).sum := by decide
  have hdescent : baseEnd_6684682 < baseStart_6684682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684745 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 4]
def baseStart_6684745 : Nat := 118140960795 + 6684745 * 2 ^ 59
def prefixEnd_6684745 : Nat := 4983230072969 + 3 ^ 40 * 6684745 * 2
def baseEnd_6684745 : Nat := 3432487237739553638144923

theorem tailTrace_6684745 : CollatzResearch.WordTrace tailWord_6684745 prefixEnd_6684745 3432487237739553638144923 := by
  unfold tailWord_6684745
  simp only [CollatzResearch.WordTrace]
  refine ⟨243812680167318003398631689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162541786778212002265754459 243812680167318003398631689)
  ·
    refine ⟨182859510125488502548973767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243812680167318003398631689 182859510125488502548973767)
    ·
      refine ⟨274289265188232753823460651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182859510125488502548973767 274289265188232753823460651)
      ·
        refine ⟨411433897782349130735190977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274289265188232753823460651 411433897782349130735190977)
        ·
          refine ⟨308575423336761848051393233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411433897782349130735190977 308575423336761848051393233)
          ·
            refine ⟨231431567502571386038544925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308575423336761848051393233 231431567502571386038544925)
            ·
              refine ⟨86786837813464269764454347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231431567502571386038544925 86786837813464269764454347)
              ·
                refine ⟨130180256720196404646681521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86786837813464269764454347 130180256720196404646681521)
                ·
                  refine ⟨97635192540147303485011141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130180256720196404646681521 97635192540147303485011141)
                  ·
                    refine ⟨18306598601277619403439589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97635192540147303485011141 18306598601277619403439589)
                    ·
                      refine ⟨3432487237739553638144923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18306598601277619403439589 3432487237739553638144923)
                      ·
                        rfl

theorem cell23_6684745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_6684745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684745 prefixEnd_6684745 := by exact prefixLift 6684745
  have htrace : WordTrace (prefixWord ++ tailWord_6684745) baseStart_6684745 baseEnd_6684745 := by
    simpa [prefixWord, tailWord_6684745, baseEnd_6684745] using wordTrace_append hprefix tailTrace_6684745
  have hstable : (prefixWord ++ tailWord_6684745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684745).length < 2 ^ (prefixWord ++ tailWord_6684745).sum := by decide
  have hdescent : baseEnd_6684745 < baseStart_6684745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684749 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_6684749 : Nat := 118140960795 + 6684749 * 2 ^ 59
def prefixEnd_6684749 : Nat := 4983230072969 + 3 ^ 40 * 6684749 * 2
def baseEnd_6684749 : Nat := 3432489291662171622494905

theorem tailTrace_6684749 : CollatzResearch.WordTrace tailWord_6684749 prefixEnd_6684749 3432489291662171622494905 := by
  unfold tailWord_6684749
  simp only [CollatzResearch.WordTrace]
  refine ⟨243812826059303512081777301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162541884039535674721184867 243812826059303512081777301)
  ·
    refine ⟨11428726221529852128833311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 243812826059303512081777301 11428726221529852128833311)
    ·
      refine ⟨17143089332294778193249967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11428726221529852128833311 17143089332294778193249967)
      ·
        refine ⟨25714633998442167289874951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17143089332294778193249967 25714633998442167289874951)
        ·
          refine ⟨38571950997663250934812427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25714633998442167289874951 38571950997663250934812427)
          ·
            refine ⟨57857926496494876402218641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38571950997663250934812427 57857926496494876402218641)
            ·
              refine ⟨43393444872371157301663981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57857926496494876402218641 43393444872371157301663981)
              ·
                refine ⟨16272541827139183988123993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43393444872371157301663981 16272541827139183988123993)
                ·
                  refine ⟨12204406370354387991092995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16272541827139183988123993 12204406370354387991092995)
                  ·
                    refine ⟨18306609555531581986639493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12204406370354387991092995 18306609555531581986639493)
                    ·
                      refine ⟨3432489291662171622494905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18306609555531581986639493 3432489291662171622494905)
                      ·
                        rfl

theorem cell23_6684749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_6684749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684749 prefixEnd_6684749 := by exact prefixLift 6684749
  have htrace : WordTrace (prefixWord ++ tailWord_6684749) baseStart_6684749 baseEnd_6684749 := by
    simpa [prefixWord, tailWord_6684749, baseEnd_6684749] using wordTrace_append hprefix tailTrace_6684749
  have hstable : (prefixWord ++ tailWord_6684749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684749).length < 2 ^ (prefixWord ++ tailWord_6684749).sum := by decide
  have hdescent : baseEnd_6684749 < baseStart_6684749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684816 : List Nat := [2, 1, 1, 1, 1, 1, 6, 5, 1, 1, 3]
def baseStart_6684816 : Nat := 118140960795 + 6684816 * 2 ^ 59
def prefixEnd_6684816 : Nat := 4983230072969 + 3 ^ 40 * 6684816 * 2
def baseEnd_6684816 : Nat := 3432523694866022860357097

theorem tailTrace_6684816 : CollatzResearch.WordTrace tailWord_6684816 prefixEnd_6684816 3432523694866022860357097 := by
  unfold tailWord_6684816
  simp only [CollatzResearch.WordTrace]
  refine ⟨121907634875030391262233151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162543513166707188349644201 121907634875030391262233151)
  ·
    refine ⟨182861452312545586893349727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121907634875030391262233151 182861452312545586893349727)
    ·
      refine ⟨274292178468818380340024591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182861452312545586893349727 274292178468818380340024591)
      ·
        refine ⟨411438267703227570510036887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274292178468818380340024591 411438267703227570510036887)
        ·
          refine ⟨617157401554841355765055331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411438267703227570510036887 617157401554841355765055331)
          ·
            refine ⟨925736102332262033647582997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617157401554841355765055331 925736102332262033647582997)
            ·
              refine ⟨43393879796824782827230453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 925736102332262033647582997 43393879796824782827230453)
              ·
                refine ⟨4068176230952323390052855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43393879796824782827230453 4068176230952323390052855)
                ·
                  refine ⟨6102264346428485085079283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068176230952323390052855 6102264346428485085079283)
                  ·
                    refine ⟨9153396519642727627618925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6102264346428485085079283 9153396519642727627618925)
                    ·
                      refine ⟨3432523694866022860357097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9153396519642727627618925 3432523694866022860357097)
                      ·
                        rfl

theorem cell23_6684816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 1, 1, 3].length) (baseStart_6684816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684816 prefixEnd_6684816 := by exact prefixLift 6684816
  have htrace : WordTrace (prefixWord ++ tailWord_6684816) baseStart_6684816 baseEnd_6684816 := by
    simpa [prefixWord, tailWord_6684816, baseEnd_6684816] using wordTrace_append hprefix tailTrace_6684816
  have hstable : (prefixWord ++ tailWord_6684816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684816).length < 2 ^ (prefixWord ++ tailWord_6684816).sum := by decide
  have hdescent : baseEnd_6684816 < baseStart_6684816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684833 : List Nat := [1, 2, 3, 3, 1, 3, 1, 4, 1, 1, 3]
def baseStart_6684833 : Nat := 118140960795 + 6684833 * 2 ^ 59
def prefixEnd_6684833 : Nat := 4983230072969 + 3 ^ 40 * 6684833 * 2
def baseEnd_6684833 : Nat := 3432532424037149293844519

theorem tailTrace_6684833 : CollatzResearch.WordTrace tailWord_6684833 prefixEnd_6684833 3432532424037149293844519 := by
  unfold tailWord_6684833
  simp only [CollatzResearch.WordTrace]
  refine ⟨243815889790999194427835153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162543926527332796285223435 243815889790999194427835153)
  ·
    refine ⟨182861917343249395820876365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243815889790999194427835153 182861917343249395820876365)
    ·
      refine ⟨68573219003718523432828637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182861917343249395820876365 68573219003718523432828637)
      ·
        refine ⟨25714957126394446287310739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68573219003718523432828637 25714957126394446287310739)
        ·
          refine ⟨38572435689591669430966109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25714957126394446287310739 38572435689591669430966109)
          ·
            refine ⟨14464663383596876036612291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38572435689591669430966109 14464663383596876036612291)
            ·
              refine ⟨21696995075395314054918437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14464663383596876036612291 21696995075395314054918437)
              ·
                refine ⟨4068186576636621385297207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21696995075395314054918437 4068186576636621385297207)
                ·
                  refine ⟨6102279864954932077945811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068186576636621385297207 6102279864954932077945811)
                  ·
                    refine ⟨9153419797432398116918717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6102279864954932077945811 9153419797432398116918717)
                    ·
                      refine ⟨3432532424037149293844519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9153419797432398116918717 3432532424037149293844519)
                      ·
                        rfl

theorem cell23_6684833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_6684833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684833 prefixEnd_6684833 := by exact prefixLift 6684833
  have htrace : WordTrace (prefixWord ++ tailWord_6684833) baseStart_6684833 baseEnd_6684833 := by
    simpa [prefixWord, tailWord_6684833, baseEnd_6684833] using wordTrace_append hprefix tailTrace_6684833
  have hstable : (prefixWord ++ tailWord_6684833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684833).length < 2 ^ (prefixWord ++ tailWord_6684833).sum := by decide
  have hdescent : baseEnd_6684833 < baseStart_6684833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684856 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 3, 2, 2]
def baseStart_6684856 : Nat := 118140960795 + 6684856 * 2 ^ 59
def prefixEnd_6684856 : Nat := 4983230072969 + 3 ^ 40 * 6684856 * 2
def baseEnd_6684856 : Nat := 3432544234092202703856913

theorem tailTrace_6684856 : CollatzResearch.WordTrace tailWord_6684856 prefixEnd_6684856 3432544234092202703856913 := by
  unfold tailWord_6684856
  simp only [CollatzResearch.WordTrace]
  refine ⟨121908364334957934677961211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162544485779943912903948281 121908364334957934677961211)
  ·
    refine ⟨182862546502436902016941817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121908364334957934677961211 182862546502436902016941817)
    ·
      refine ⟨137146909876827676512706363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182862546502436902016941817 137146909876827676512706363)
      ·
        refine ⟨205720364815241514769059545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137146909876827676512706363 205720364815241514769059545)
        ·
          refine ⟨154290273611431136076794659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205720364815241514769059545 154290273611431136076794659)
          ·
            refine ⟨231435410417146704115191989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154290273611431136076794659 231435410417146704115191989)
            ·
              refine ⟨21697069726607503510799249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231435410417146704115191989 21697069726607503510799249)
              ·
                refine ⟨16272802294955627633099437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21697069726607503510799249 16272802294955627633099437)
                ·
                  refine ⟨6102300860608360362412289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16272802294955627633099437 6102300860608360362412289)
                  ·
                    refine ⟨4576725645456270271809217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6102300860608360362412289 4576725645456270271809217)
                    ·
                      refine ⟨3432544234092202703856913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4576725645456270271809217 3432544234092202703856913)
                      ·
                        rfl

theorem cell23_6684856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3, 2, 2].length) (baseStart_6684856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684856 prefixEnd_6684856 := by exact prefixLift 6684856
  have htrace : WordTrace (prefixWord ++ tailWord_6684856) baseStart_6684856 baseEnd_6684856 := by
    simpa [prefixWord, tailWord_6684856, baseEnd_6684856] using wordTrace_append hprefix tailTrace_6684856
  have hstable : (prefixWord ++ tailWord_6684856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684856).length < 2 ^ (prefixWord ++ tailWord_6684856).sum := by decide
  have hdescent : baseEnd_6684856 < baseStart_6684856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684859 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 1, 2, 3]
def baseStart_6684859 : Nat := 118140960795 + 6684859 * 2 ^ 59
def prefixEnd_6684859 : Nat := 4983230072969 + 3 ^ 40 * 6684859 * 2
def baseEnd_6684859 : Nat := 3432545774534166192119399

theorem tailTrace_6684859 : CollatzResearch.WordTrace tailWord_6684859 prefixEnd_6684859 3432545774534166192119399 := by
  unfold tailWord_6684859
  simp only [CollatzResearch.WordTrace]
  refine ⟨243816838088905000868281631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162544558725936667245521087 243816838088905000868281631)
  ·
    refine ⟨365725257133357501302422447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243816838088905000868281631 365725257133357501302422447)
    ·
      refine ⟨548587885700036251953633671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365725257133357501302422447 548587885700036251953633671)
      ·
        refine ⟨822881828550054377930450507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548587885700036251953633671 822881828550054377930450507)
        ·
          refine ⟨1234322742825081566895675761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822881828550054377930450507 1234322742825081566895675761)
          ·
            refine ⟨925742057118811175171756821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1234322742825081566895675761 925742057118811175171756821)
            ·
              refine ⟨43394158927444273836176101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 925742057118811175171756821 43394158927444273836176101)
              ·
                refine ⟨8136404798895801344283019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43394158927444273836176101 8136404798895801344283019)
                ·
                  refine ⟨12204607198343702016424529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8136404798895801344283019 12204607198343702016424529)
                  ·
                    refine ⟨9153455398757776512318397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12204607198343702016424529 9153455398757776512318397)
                    ·
                      refine ⟨3432545774534166192119399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9153455398757776512318397 3432545774534166192119399)
                      ·
                        rfl

theorem cell23_6684859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 2, 3].length) (baseStart_6684859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684859 prefixEnd_6684859 := by exact prefixLift 6684859
  have htrace : WordTrace (prefixWord ++ tailWord_6684859) baseStart_6684859 baseEnd_6684859 := by
    simpa [prefixWord, tailWord_6684859, baseEnd_6684859] using wordTrace_append hprefix tailTrace_6684859
  have hstable : (prefixWord ++ tailWord_6684859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684859).length < 2 ^ (prefixWord ++ tailWord_6684859).sum := by decide
  have hdescent : baseEnd_6684859 < baseStart_6684859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684860 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 2, 3, 2]
def baseStart_6684860 : Nat := 118140960795 + 6684860 * 2 ^ 59
def prefixEnd_6684860 : Nat := 4983230072969 + 3 ^ 40 * 6684860 * 2
def baseEnd_6684860 : Nat := 3432546288014820688206895

theorem tailTrace_6684860 : CollatzResearch.WordTrace tailWord_6684860 prefixEnd_6684860 3432546288014820688206895 := by
  unfold tailWord_6684860
  simp only [CollatzResearch.WordTrace]
  refine ⟨121908437280950689019534017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162544583041267585359378689 121908437280950689019534017)
  ·
    refine ⟨91431327960713016764650513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121908437280950689019534017 91431327960713016764650513)
    ·
      refine ⟨68573495970534762573487885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91431327960713016764650513 68573495970534762573487885)
      ·
        refine ⟨25715060988950535965057957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68573495970534762573487885 25715060988950535965057957)
        ·
          refine ⟨4821573935428225493448367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25715060988950535965057957 4821573935428225493448367)
          ·
            refine ⟨7232360903142338240172551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4821573935428225493448367 7232360903142338240172551)
            ·
              refine ⟨10848541354713507360258827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7232360903142338240172551 10848541354713507360258827)
              ·
                refine ⟨16272812032070261040388241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10848541354713507360258827 16272812032070261040388241)
                ·
                  refine ⟨12204609024052695780291181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16272812032070261040388241 12204609024052695780291181)
                  ·
                    refine ⟨4576728384019760917609193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12204609024052695780291181 4576728384019760917609193)
                    ·
                      refine ⟨3432546288014820688206895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4576728384019760917609193 3432546288014820688206895)
                      ·
                        rfl

theorem cell23_6684860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_6684860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684860 prefixEnd_6684860 := by exact prefixLift 6684860
  have htrace : WordTrace (prefixWord ++ tailWord_6684860) baseStart_6684860 baseEnd_6684860 := by
    simpa [prefixWord, tailWord_6684860, baseEnd_6684860] using wordTrace_append hprefix tailTrace_6684860
  have hstable : (prefixWord ++ tailWord_6684860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684860).length < 2 ^ (prefixWord ++ tailWord_6684860).sum := by decide
  have hdescent : baseEnd_6684860 < baseStart_6684860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684912 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 4]
def baseStart_6684912 : Nat := 118140960795 + 6684912 * 2 ^ 59
def prefixEnd_6684912 : Nat := 4983230072969 + 3 ^ 40 * 6684912 * 2
def baseEnd_6684912 : Nat := 3432572989008854484756655

theorem tailTrace_6684912 : CollatzResearch.WordTrace tailWord_6684912 prefixEnd_6684912 3432572989008854484756655 := by
  unfold tailWord_6684912
  simp only [CollatzResearch.WordTrace]
  refine ⟨121909385578856495459980495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162545847438475327279973993 121909385578856495459980495)
  ·
    refine ⟨182864078368284743189970743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121909385578856495459980495 182864078368284743189970743)
    ·
      refine ⟨274296117552427114784956115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182864078368284743189970743 274296117552427114784956115)
      ·
        refine ⟨411444176328640672177434173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274296117552427114784956115 411444176328640672177434173)
        ·
          refine ⟨154291566123240252066537815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411444176328640672177434173 154291566123240252066537815)
          ·
            refine ⟨231437349184860378099806723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154291566123240252066537815 231437349184860378099806723)
            ·
              refine ⟨347156023777290567149710085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231437349184860378099806723 347156023777290567149710085)
              ·
                refine ⟨65091754458241981340570641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347156023777290567149710085 65091754458241981340570641)
                ·
                  refine ⟨48818815843681486005427981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65091754458241981340570641 48818815843681486005427981)
                  ·
                    refine ⟨18307055941380557252035493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48818815843681486005427981 18307055941380557252035493)
                    ·
                      refine ⟨3432572989008854484756655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18307055941380557252035493 3432572989008854484756655)
                      ·
                        rfl

theorem cell23_6684912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_6684912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684912 prefixEnd_6684912 := by exact prefixLift 6684912
  have htrace : WordTrace (prefixWord ++ tailWord_6684912) baseStart_6684912 baseEnd_6684912 := by
    simpa [prefixWord, tailWord_6684912, baseEnd_6684912] using wordTrace_append hprefix tailTrace_6684912
  have hstable : (prefixWord ++ tailWord_6684912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684912).length < 2 ^ (prefixWord ++ tailWord_6684912).sum := by decide
  have hdescent : baseEnd_6684912 < baseStart_6684912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684957 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_6684957 : Nat := 118140960795 + 6684957 * 2 ^ 59
def prefixEnd_6684957 : Nat := 4983230072969 + 3 ^ 40 * 6684957 * 2
def baseEnd_6684957 : Nat := 3432596095638306808693949

theorem tailTrace_6684957 : CollatzResearch.WordTrace tailWord_6684957 prefixEnd_6684957 3432596095638306808693949 := by
  unfold tailWord_6684957
  simp only [CollatzResearch.WordTrace]
  refine ⟨243820412442549963605349125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162546941628366642403566083 243820412442549963605349125)
  ·
    refine ⟨45716327332978118176002961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243820412442549963605349125 45716327332978118176002961)
    ·
      refine ⟨34287245499733588632002221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45716327332978118176002961 34287245499733588632002221)
      ·
        refine ⟨12857717062400095737000833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34287245499733588632002221 12857717062400095737000833)
        ·
          refine ⟨9643287796800071802750625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12857717062400095737000833 9643287796800071802750625)
          ·
            refine ⟨7232465847600053852062969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9643287796800071802750625 7232465847600053852062969)
            ·
              refine ⟨5424349385700040389047227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7232465847600053852062969 5424349385700040389047227)
              ·
                refine ⟨8136524078550060583570841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5424349385700040389047227 8136524078550060583570841)
                ·
                  refine ⟨6102393058912545437678131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8136524078550060583570841 6102393058912545437678131)
                  ·
                    refine ⟨9153589588368818156517197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6102393058912545437678131 9153589588368818156517197)
                    ·
                      refine ⟨3432596095638306808693949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9153589588368818156517197 3432596095638306808693949)
                      ·
                        rfl

theorem cell23_6684957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_6684957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684957 prefixEnd_6684957 := by exact prefixLift 6684957
  have htrace : WordTrace (prefixWord ++ tailWord_6684957) baseStart_6684957 baseEnd_6684957 := by
    simpa [prefixWord, tailWord_6684957, baseEnd_6684957] using wordTrace_append hprefix tailTrace_6684957
  have hstable : (prefixWord ++ tailWord_6684957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684957).length < 2 ^ (prefixWord ++ tailWord_6684957).sum := by decide
  have hdescent : baseEnd_6684957 < baseStart_6684957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684963 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 2, 2, 2]
def baseStart_6684963 : Nat := 118140960795 + 6684963 * 2 ^ 59
def prefixEnd_6684963 : Nat := 4983230072969 + 3 ^ 40 * 6684963 * 2
def baseEnd_6684963 : Nat := 3432599176522233785218921

theorem tailTrace_6684963 : CollatzResearch.WordTrace tailWord_6684963 prefixEnd_6684963 3432599176522233785218921 := by
  unfold tailWord_6684963
  simp only [CollatzResearch.WordTrace]
  refine ⟨243820631280528226630067543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162547087520352151086711695 243820631280528226630067543)
  ·
    refine ⟨365730946920792339945101315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243820631280528226630067543 365730946920792339945101315)
    ·
      refine ⟨548596420381188509917651973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365730946920792339945101315 548596420381188509917651973)
      ·
        refine ⟨102861828821472845609559745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 548596420381188509917651973 102861828821472845609559745)
        ·
          refine ⟨77146371616104634207169809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102861828821472845609559745 77146371616104634207169809)
          ·
            refine ⟨57859778712078475655377357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77146371616104634207169809 57859778712078475655377357)
            ·
              refine ⟨21697417017029428370766509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57859778712078475655377357 21697417017029428370766509)
              ·
                refine ⟨8136531381386035639037441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21697417017029428370766509 8136531381386035639037441)
                ·
                  refine ⟨6102398536039526729278081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8136531381386035639037441 6102398536039526729278081)
                  ·
                    refine ⟨4576798902029645046958561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6102398536039526729278081 4576798902029645046958561)
                    ·
                      refine ⟨3432599176522233785218921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4576798902029645046958561 3432599176522233785218921)
                      ·
                        rfl

theorem cell23_6684963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_6684963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684963 prefixEnd_6684963 := by exact prefixLift 6684963
  have htrace : WordTrace (prefixWord ++ tailWord_6684963) baseStart_6684963 baseEnd_6684963 := by
    simpa [prefixWord, tailWord_6684963, baseEnd_6684963] using wordTrace_append hprefix tailTrace_6684963
  have hstable : (prefixWord ++ tailWord_6684963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684963).length < 2 ^ (prefixWord ++ tailWord_6684963).sum := by decide
  have hdescent : baseEnd_6684963 < baseStart_6684963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684967 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_6684967 : Nat := 118140960795 + 6684967 * 2 ^ 59
def prefixEnd_6684967 : Nat := 4983230072969 + 3 ^ 40 * 6684967 * 2
def baseEnd_6684967 : Nat := 3432601230444851769568903

theorem tailTrace_6684967 : CollatzResearch.WordTrace tailWord_6684967 prefixEnd_6684967 3432601230444851769568903 := by
  unfold tailWord_6684967
  simp only [CollatzResearch.WordTrace]
  refine ⟨243820777172513735313213155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162547184781675823542142103 243820777172513735313213155)
  ·
    refine ⟨365731165758770602969819733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243820777172513735313213155 365731165758770602969819733)
    ·
      refine ⟨4285912098735593003552575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 365731165758770602969819733 4285912098735593003552575)
      ·
        refine ⟨6428868148103389505328863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4285912098735593003552575 6428868148103389505328863)
        ·
          refine ⟨9643302222155084257993295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6428868148103389505328863 9643302222155084257993295)
          ·
            refine ⟨14464953333232626386989943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9643302222155084257993295 14464953333232626386989943)
            ·
              refine ⟨21697429999848939580484915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14464953333232626386989943 21697429999848939580484915)
              ·
                refine ⟨32546144999773409370727373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21697429999848939580484915 32546144999773409370727373)
                ·
                  refine ⟨12204804374915028514022765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32546144999773409370727373 12204804374915028514022765)
                  ·
                    refine ⟨4576801640593135692758537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12204804374915028514022765 4576801640593135692758537)
                    ·
                      refine ⟨3432601230444851769568903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4576801640593135692758537 3432601230444851769568903)
                      ·
                        rfl

theorem cell23_6684967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_6684967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684967 prefixEnd_6684967 := by exact prefixLift 6684967
  have htrace : WordTrace (prefixWord ++ tailWord_6684967) baseStart_6684967 baseEnd_6684967 := by
    simpa [prefixWord, tailWord_6684967, baseEnd_6684967] using wordTrace_append hprefix tailTrace_6684967
  have hstable : (prefixWord ++ tailWord_6684967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684967).length < 2 ^ (prefixWord ++ tailWord_6684967).sum := by decide
  have hdescent : baseEnd_6684967 < baseStart_6684967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6684999 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 2, 5]
def baseStart_6684999 : Nat := 118140960795 + 6684999 * 2 ^ 59
def prefixEnd_6684999 : Nat := 4983230072969 + 3 ^ 40 * 6684999 * 2
def baseEnd_6684999 : Nat := 1144205887275265214789585

theorem tailTrace_6684999 : CollatzResearch.WordTrace tailWord_6684999 prefixEnd_6684999 1144205887275265214789585 := by
  unfold tailWord_6684999
  simp only [CollatzResearch.WordTrace]
  refine ⟨243821944308397804778378051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162547962872265203185585367 243821944308397804778378051)
  ·
    refine ⟨365732916462596707167567077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243821944308397804778378051 365732916462596707167567077)
    ·
      refine ⟨68574921836736882593918827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365732916462596707167567077 68574921836736882593918827)
      ·
        refine ⟨102862382755105323890878241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68574921836736882593918827 102862382755105323890878241)
        ·
          refine ⟨77146787066328992918158681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102862382755105323890878241 77146787066328992918158681)
          ·
            refine ⟨57860090299746744688619011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77146787066328992918158681 57860090299746744688619011)
            ·
              refine ⟨86790135449620117032928517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57860090299746744688619011 86790135449620117032928517)
              ·
                refine ⟨16273150396803771943674097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86790135449620117032928517 16273150396803771943674097)
                ·
                  refine ⟨12204862797602828957755573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16273150396803771943674097 12204862797602828957755573)
                  ·
                    refine ⟨1144205887275265214789585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12204862797602828957755573 1144205887275265214789585)
                    ·
                      rfl

theorem cell23_6684999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_6684999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6684999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6684999 prefixEnd_6684999 := by exact prefixLift 6684999
  have htrace : WordTrace (prefixWord ++ tailWord_6684999) baseStart_6684999 baseEnd_6684999 := by
    simpa [prefixWord, tailWord_6684999, baseEnd_6684999] using wordTrace_append hprefix tailTrace_6684999
  have hstable : (prefixWord ++ tailWord_6684999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6684999).length < 2 ^ (prefixWord ++ tailWord_6684999).sum := by decide
  have hdescent : baseEnd_6684999 < baseStart_6684999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6684999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685009 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_6685009 : Nat := 118140960795 + 6685009 * 2 ^ 59
def prefixEnd_6685009 : Nat := 4983230072969 + 3 ^ 40 * 6685009 * 2
def baseEnd_6685009 : Nat := 3432622796632340605243709

theorem tailTrace_6685009 : CollatzResearch.WordTrace tailWord_6685009 prefixEnd_6685009 3432622796632340605243709 := by
  unfold tailWord_6685009
  simp only [CollatzResearch.WordTrace]
  refine ⟨243822309038361576486242081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162548206025574384324161387 243822309038361576486242081)
  ·
    refine ⟨182866731778771182364681561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243822309038361576486242081 182866731778771182364681561)
    ·
      refine ⟨137150048834078386773511171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182866731778771182364681561 137150048834078386773511171)
      ·
        refine ⟨205725073251117580160266757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137150048834078386773511171 205725073251117580160266757)
        ·
          refine ⟨38573451234584546280050017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205725073251117580160266757 38573451234584546280050017)
          ·
            refine ⟨28930088425938409710037513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38573451234584546280050017 28930088425938409710037513)
            ·
              refine ⟨21697566319453807282528135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28930088425938409710037513 21697566319453807282528135)
              ·
                refine ⟨32546349479180710923792203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21697566319453807282528135 32546349479180710923792203)
                ·
                  refine ⟨48819524218771066385688305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32546349479180710923792203 48819524218771066385688305)
                  ·
                    refine ⟨36614643164078299789266229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48819524218771066385688305 36614643164078299789266229)
                    ·
                      refine ⟨3432622796632340605243709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36614643164078299789266229 3432622796632340605243709)
                      ·
                        rfl

theorem cell23_6685009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_6685009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685009 prefixEnd_6685009 := by exact prefixLift 6685009
  have htrace : WordTrace (prefixWord ++ tailWord_6685009) baseStart_6685009 baseEnd_6685009 := by
    simpa [prefixWord, tailWord_6685009, baseEnd_6685009] using wordTrace_append hprefix tailTrace_6685009
  have hstable : (prefixWord ++ tailWord_6685009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685009).length < 2 ^ (prefixWord ++ tailWord_6685009).sum := by decide
  have hdescent : baseEnd_6685009 < baseStart_6685009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685036 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 4]
def baseStart_6685036 : Nat := 118140960795 + 6685036 * 2 ^ 59
def prefixEnd_6685036 : Nat := 4983230072969 + 3 ^ 40 * 6685036 * 2
def baseEnd_6685036 : Nat := 3432636660610011999606085

theorem tailTrace_6685036 : CollatzResearch.WordTrace tailWord_6685036 prefixEnd_6685036 3432636660610011999606085 := by
  unfold tailWord_6685036
  simp only [CollatzResearch.WordTrace]
  refine ⟨121911646904631880048737481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162548862539509173398316641 121911646904631880048737481)
  ·
    refine ⟨91433735178473910036553111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121911646904631880048737481 91433735178473910036553111)
    ·
      refine ⟨137150602767710865054829667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91433735178473910036553111 137150602767710865054829667)
      ·
        refine ⟨205725904151566297582244501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137150602767710865054829667 205725904151566297582244501)
        ·
          refine ⟨9643401757104670199167711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 205725904151566297582244501 9643401757104670199167711)
          ·
            refine ⟨14465102635657005298751567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9643401757104670199167711 14465102635657005298751567)
            ·
              refine ⟨21697653953485507948127351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14465102635657005298751567 21697653953485507948127351)
              ·
                refine ⟨32546480930228261922191027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21697653953485507948127351 32546480930228261922191027)
                ·
                  refine ⟨48819721395342392883286541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32546480930228261922191027 48819721395342392883286541)
                  ·
                    refine ⟨18307395523253397331232453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48819721395342392883286541 18307395523253397331232453)
                    ·
                      refine ⟨3432636660610011999606085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18307395523253397331232453 3432636660610011999606085)
                      ·
                        rfl

theorem cell23_6685036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_6685036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685036 prefixEnd_6685036 := by exact prefixLift 6685036
  have htrace : WordTrace (prefixWord ++ tailWord_6685036) baseStart_6685036 baseEnd_6685036 := by
    simpa [prefixWord, tailWord_6685036, baseEnd_6685036] using wordTrace_append hprefix tailTrace_6685036
  have hstable : (prefixWord ++ tailWord_6685036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685036).length < 2 ^ (prefixWord ++ tailWord_6685036).sum := by decide
  have hdescent : baseEnd_6685036 < baseStart_6685036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685063 : List Nat := [1, 1, 4, 2, 2, 1, 1, 6, 1, 4]
def baseStart_6685063 : Nat := 118140960795 + 6685063 * 2 ^ 59
def prefixEnd_6685063 : Nat := 4983230072969 + 3 ^ 40 * 6685063 * 2
def baseEnd_6685063 : Nat := 1144216841529227797989487

theorem tailTrace_6685063 : CollatzResearch.WordTrace tailWord_6685063 prefixEnd_6685063 1144216841529227797989487 := by
  unfold tailWord_6685063
  simp only [CollatzResearch.WordTrace]
  refine ⟨243824278580165943708707843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162549519053443962472471895 243824278580165943708707843)
  ·
    refine ⟨365736417870248915563061765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243824278580165943708707843 365736417870248915563061765)
    ·
      refine ⟨68575578350671671668074081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365736417870248915563061765 68575578350671671668074081)
      ·
        refine ⟨51431683763003753751055561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68575578350671671668074081 51431683763003753751055561)
        ·
          refine ⟨38573762822252815313291671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51431683763003753751055561 38573762822252815313291671)
          ·
            refine ⟨57860644233379222969937507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38573762822252815313291671 57860644233379222969937507)
            ·
              refine ⟨86790966350068834454906261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57860644233379222969937507 86790966350068834454906261)
              ·
                refine ⟨4068326547659476615073731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86790966350068834454906261 4068326547659476615073731)
                ·
                  refine ⟨6102489821489214922610597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068326547659476615073731 6102489821489214922610597)
                  ·
                    refine ⟨1144216841529227797989487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6102489821489214922610597 1144216841529227797989487)
                    ·
                      rfl

theorem cell23_6685063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_6685063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685063 prefixEnd_6685063 := by exact prefixLift 6685063
  have htrace : WordTrace (prefixWord ++ tailWord_6685063) baseStart_6685063 baseEnd_6685063 := by
    simpa [prefixWord, tailWord_6685063, baseEnd_6685063] using wordTrace_append hprefix tailTrace_6685063
  have hstable : (prefixWord ++ tailWord_6685063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685063).length < 2 ^ (prefixWord ++ tailWord_6685063).sum := by decide
  have hdescent : baseEnd_6685063 < baseStart_6685063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685106 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_6685106 : Nat := 118140960795 + 6685106 * 2 ^ 59
def prefixEnd_6685106 : Nat := 4983230072969 + 3 ^ 40 * 6685106 * 2
def baseEnd_6685106 : Nat := 1144224201418608908576921

theorem tailTrace_6685106 : CollatzResearch.WordTrace tailWord_6685106 prefixEnd_6685106 1144224201418608908576921 := by
  unfold tailWord_6685106
  simp only [CollatzResearch.WordTrace]
  refine ⟨60956461729752540513130793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162550564612673441368348781 60956461729752540513130793)
  ·
    refine ⟨45717346297314405384848095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60956461729752540513130793 45717346297314405384848095)
    ·
      refine ⟨68576019445971608077272143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45717346297314405384848095 68576019445971608077272143)
      ·
        refine ⟨102864029168957412115908215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68576019445971608077272143 102864029168957412115908215)
        ·
          refine ⟨154296043753436118173862323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102864029168957412115908215 154296043753436118173862323)
          ·
            refine ⟨231444065630154177260793485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154296043753436118173862323 231444065630154177260793485)
            ·
              refine ⟨86791524611307816472797557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231444065630154177260793485 86791524611307816472797557)
              ·
                refine ⟨8136705432310107794324771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86791524611307816472797557 8136705432310107794324771)
                ·
                  refine ⟨12205058148465161691487157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8136705432310107794324771 12205058148465161691487157)
                  ·
                    refine ⟨1144224201418608908576921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12205058148465161691487157 1144224201418608908576921)
                    ·
                      rfl

theorem cell23_6685106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_6685106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685106 prefixEnd_6685106 := by exact prefixLift 6685106
  have htrace : WordTrace (prefixWord ++ tailWord_6685106) baseStart_6685106 baseEnd_6685106 := by
    simpa [prefixWord, tailWord_6685106, baseEnd_6685106] using wordTrace_append hprefix tailTrace_6685106
  have hstable : (prefixWord ++ tailWord_6685106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685106).length < 2 ^ (prefixWord ++ tailWord_6685106).sum := by decide
  have hdescent : baseEnd_6685106 < baseStart_6685106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685113 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 4, 3, 2]
def baseStart_6685113 : Nat := 118140960795 + 6685113 * 2 ^ 59
def prefixEnd_6685113 : Nat := 4983230072969 + 3 ^ 40 * 6685113 * 2
def baseEnd_6685113 : Nat := 3432676198620408198343231

theorem tailTrace_6685113 : CollatzResearch.WordTrace tailWord_6685113 prefixEnd_6685113 3432676198620408198343231 := by
  unfold tailWord_6685113
  simp only [CollatzResearch.WordTrace]
  refine ⟨243826102229984802248027993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162550734819989868165351995 243826102229984802248027993)
  ·
    refine ⟨182869576672488601686020995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243826102229984802248027993 182869576672488601686020995)
    ·
      refine ⟨274304365008732902529031493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182869576672488601686020995 274304365008732902529031493)
      ·
        refine ⟨51432068439137419224193405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274304365008732902529031493 51432068439137419224193405)
        ·
          refine ⟨19287025664676532209072527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51432068439137419224193405 19287025664676532209072527)
          ·
            refine ⟨28930538497014798313608791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19287025664676532209072527 28930538497014798313608791)
            ·
              refine ⟨43395807745522197470413187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28930538497014798313608791 43395807745522197470413187)
              ·
                refine ⟨65093711618283296205619781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43395807745522197470413187 65093711618283296205619781)
                ·
                  refine ⟨12205070928428118038553709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65093711618283296205619781 12205070928428118038553709)
                  ·
                    refine ⟨4576901598160544264457641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12205070928428118038553709 4576901598160544264457641)
                    ·
                      refine ⟨3432676198620408198343231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4576901598160544264457641 3432676198620408198343231)
                      ·
                        rfl

theorem cell23_6685113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_6685113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685113 prefixEnd_6685113 := by exact prefixLift 6685113
  have htrace : WordTrace (prefixWord ++ tailWord_6685113) baseStart_6685113 baseEnd_6685113 := by
    simpa [prefixWord, tailWord_6685113, baseEnd_6685113] using wordTrace_append hprefix tailTrace_6685113
  have hstable : (prefixWord ++ tailWord_6685113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685113).length < 2 ^ (prefixWord ++ tailWord_6685113).sum := by decide
  have hdescent : baseEnd_6685113 < baseStart_6685113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685140 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_6685140 : Nat := 118140960795 + 6685140 * 2 ^ 59
def prefixEnd_6685140 : Nat := 4983230072969 + 3 ^ 40 * 6685140 * 2
def baseEnd_6685140 : Nat := 1144230020866026530901869

theorem tailTrace_6685140 : CollatzResearch.WordTrace tailWord_6685140 prefixEnd_6685140 1144230020866026530901869 := by
  unfold tailWord_6685140
  simp only [CollatzResearch.WordTrace]
  refine ⟨121913543500443492929630437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162551391333924657239507249 121913543500443492929630437)
  ·
    refine ⟨22858789406333154924305707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121913543500443492929630437 22858789406333154924305707)
    ·
      refine ⟨34288184109499732386458561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22858789406333154924305707 34288184109499732386458561)
      ·
        refine ⟨25716138082124799289843921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34288184109499732386458561 25716138082124799289843921)
        ·
          refine ⟨19287103561593599467382941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25716138082124799289843921 19287103561593599467382941)
          ·
            refine ⟨7232663835597599800268603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19287103561593599467382941 7232663835597599800268603)
            ·
              refine ⟨10848995753396399700402905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7232663835597599800268603 10848995753396399700402905)
              ·
                refine ⟨8136746815047299775302179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10848995753396399700402905 8136746815047299775302179)
                ·
                  refine ⟨12205120222570949662953269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8136746815047299775302179 12205120222570949662953269)
                  ·
                    refine ⟨1144230020866026530901869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12205120222570949662953269 1144230020866026530901869)
                    ·
                      rfl

theorem cell23_6685140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_6685140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685140 prefixEnd_6685140 := by exact prefixLift 6685140
  have htrace : WordTrace (prefixWord ++ tailWord_6685140) baseStart_6685140 baseEnd_6685140 := by
    simpa [prefixWord, tailWord_6685140, baseEnd_6685140] using wordTrace_append hprefix tailTrace_6685140
  have hstable : (prefixWord ++ tailWord_6685140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685140).length < 2 ^ (prefixWord ++ tailWord_6685140).sum := by decide
  have hdescent : baseEnd_6685140 < baseStart_6685140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685160 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_6685160 : Nat := 118140960795 + 6685160 * 2 ^ 59
def prefixEnd_6685160 : Nat := 4983230072969 + 3 ^ 40 * 6685160 * 2
def baseEnd_6685160 : Nat := 3432700332211169514455515

theorem tailTrace_6685160 : CollatzResearch.WordTrace tailWord_6685160 prefixEnd_6685160 3432700332211169514455515 := by
  unfold tailWord_6685160
  simp only [CollatzResearch.WordTrace]
  refine ⟨121913908230407264637494467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162551877640543019516659289 121913908230407264637494467)
  ·
    refine ⟨182870862345610896956241701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121913908230407264637494467 182870862345610896956241701)
    ·
      refine ⟨34288286689802043179295319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182870862345610896956241701 34288286689802043179295319)
      ·
        refine ⟨51432430034703064768942979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34288286689802043179295319 51432430034703064768942979)
        ·
          refine ⟨77148645052054597153414469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51432430034703064768942979 77148645052054597153414469)
          ·
            refine ⟨14465370947260236966265213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77148645052054597153414469 14465370947260236966265213)
            ·
              refine ⟨5424514105222588862349455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14465370947260236966265213 5424514105222588862349455)
              ·
                refine ⟨8136771157833883293524183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5424514105222588862349455 8136771157833883293524183)
                ·
                  refine ⟨12205156736750824940286275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8136771157833883293524183 12205156736750824940286275)
                  ·
                    refine ⟨18307735105126237410429413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12205156736750824940286275 18307735105126237410429413)
                    ·
                      refine ⟨3432700332211169514455515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18307735105126237410429413 3432700332211169514455515)
                      ·
                        rfl

theorem cell23_6685160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_6685160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685160 prefixEnd_6685160 := by exact prefixLift 6685160
  have htrace : WordTrace (prefixWord ++ tailWord_6685160) baseStart_6685160 baseEnd_6685160 := by
    simpa [prefixWord, tailWord_6685160, baseEnd_6685160] using wordTrace_append hprefix tailTrace_6685160
  have hstable : (prefixWord ++ tailWord_6685160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685160).length < 2 ^ (prefixWord ++ tailWord_6685160).sum := by decide
  have hdescent : baseEnd_6685160 < baseStart_6685160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685176 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 3, 3, 3]
def baseStart_6685176 : Nat := 118140960795 + 6685176 * 2 ^ 59
def prefixEnd_6685176 : Nat := 4983230072969 + 3 ^ 40 * 6685176 * 2
def baseEnd_6685176 : Nat := 3432708547901641451855441

theorem tailTrace_6685176 : CollatzResearch.WordTrace tailWord_6685176 prefixEnd_6685176 3432708547901641451855441 := by
  unfold tailWord_6685176
  simp only [CollatzResearch.WordTrace]
  refine ⟨121914200014378282003785691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162552266685837709338380921 121914200014378282003785691)
  ·
    refine ⟨182871300021567423005678537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121914200014378282003785691 182871300021567423005678537)
    ·
      refine ⟨137153475016175567254258903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182871300021567423005678537 137153475016175567254258903)
      ·
        refine ⟨205730212524263350881388355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137153475016175567254258903 205730212524263350881388355)
        ·
          refine ⟨308595318786395026322082533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205730212524263350881388355 308595318786395026322082533)
          ·
            refine ⟨57861622272449067435390475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308595318786395026322082533 57861622272449067435390475)
            ·
              refine ⟨86792433408673601153085713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57861622272449067435390475 86792433408673601153085713)
              ·
                refine ⟨65094325056505200864814285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86792433408673601153085713 65094325056505200864814285)
                ·
                  refine ⟨24410371896189450324305357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65094325056505200864814285 24410371896189450324305357)
                  ·
                    refine ⟨9153889461071043871614509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24410371896189450324305357 9153889461071043871614509)
                    ·
                      refine ⟨3432708547901641451855441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9153889461071043871614509 3432708547901641451855441)
                      ·
                        rfl

theorem cell23_6685176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_6685176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685176 prefixEnd_6685176 := by exact prefixLift 6685176
  have htrace : WordTrace (prefixWord ++ tailWord_6685176) baseStart_6685176 baseEnd_6685176 := by
    simpa [prefixWord, tailWord_6685176, baseEnd_6685176] using wordTrace_append hprefix tailTrace_6685176
  have hstable : (prefixWord ++ tailWord_6685176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685176).length < 2 ^ (prefixWord ++ tailWord_6685176).sum := by decide
  have hdescent : baseEnd_6685176 < baseStart_6685176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685197 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_6685197 : Nat := 118140960795 + 6685197 * 2 ^ 59
def prefixEnd_6685197 : Nat := 4983230072969 + 3 ^ 40 * 6685197 * 2
def baseEnd_6685197 : Nat := 3432719330995385869692845

theorem tailTrace_6685197 : CollatzResearch.WordTrace tailWord_6685197 prefixEnd_6685197 3432719330995385869692845 := by
  unfold tailWord_6685197
  simp only [CollatzResearch.WordTrace]
  refine ⟨243829165961680484594085845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162552777307786989729390563 243829165961680484594085845)
  ·
    refine ⟨5714746077226886357673887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 243829165961680484594085845 5714746077226886357673887)
    ·
      refine ⟨8572119115840329536510831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5714746077226886357673887 8572119115840329536510831)
      ·
        refine ⟨12858178673760494304766247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572119115840329536510831 12858178673760494304766247)
        ·
          refine ⟨19287268010640741457149371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12858178673760494304766247 19287268010640741457149371)
          ·
            refine ⟨28930902015961112185724057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19287268010640741457149371 28930902015961112185724057)
            ·
              refine ⟨21698176511970834139293043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28930902015961112185724057 21698176511970834139293043)
              ·
                refine ⟨32547264767956251208939565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21698176511970834139293043 32547264767956251208939565)
                ·
                  refine ⟨12205224287983594203352337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32547264767956251208939565 12205224287983594203352337)
                  ·
                    refine ⟨9153918215987695652514253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12205224287983594203352337 9153918215987695652514253)
                    ·
                      refine ⟨3432719330995385869692845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9153918215987695652514253 3432719330995385869692845)
                      ·
                        rfl

theorem cell23_6685197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_6685197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685197 prefixEnd_6685197 := by exact prefixLift 6685197
  have htrace : WordTrace (prefixWord ++ tailWord_6685197) baseStart_6685197 baseEnd_6685197 := by
    simpa [prefixWord, tailWord_6685197, baseEnd_6685197] using wordTrace_append hprefix tailTrace_6685197
  have hstable : (prefixWord ++ tailWord_6685197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685197).length < 2 ^ (prefixWord ++ tailWord_6685197).sum := by decide
  have hdescent : baseEnd_6685197 < baseStart_6685197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685199 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_6685199 : Nat := 118140960795 + 6685199 * 2 ^ 59
def prefixEnd_6685199 : Nat := 4983230072969 + 3 ^ 40 * 6685199 * 2
def baseEnd_6685199 : Nat := 3432720357956694861867835

theorem tailTrace_6685199 : CollatzResearch.WordTrace tailWord_6685199 prefixEnd_6685199 3432720357956694861867835 := by
  unfold tailWord_6685199
  simp only [CollatzResearch.WordTrace]
  refine ⟨243829238907673238935658651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162552825938448825957105767 243829238907673238935658651)
  ·
    refine ⟨365743858361509858403487977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243829238907673238935658651 365743858361509858403487977)
    ·
      refine ⟨274307893771132393802615983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365743858361509858403487977 274307893771132393802615983)
      ·
        refine ⟨411461840656698590703923975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274307893771132393802615983 411461840656698590703923975)
        ·
          refine ⟨617192760985047886055885963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411461840656698590703923975 617192760985047886055885963)
          ·
            refine ⟨925789141477571829083828945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617192760985047886055885963 925789141477571829083828945)
            ·
              refine ⟨694341856108178871812871709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925789141477571829083828945 694341856108178871812871709)
              ·
                refine ⟨260378196040567076929826891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 694341856108178871812871709 260378196040567076929826891)
                ·
                  refine ⟨390567294060850615394740337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260378196040567076929826891 390567294060850615394740337)
                  ·
                    refine ⟨292925470545637961546055253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 390567294060850615394740337 292925470545637961546055253)
                    ·
                      refine ⟨3432720357956694861867835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 292925470545637961546055253 3432720357956694861867835)
                      ·
                        rfl

theorem cell23_6685199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_6685199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685199 prefixEnd_6685199 := by exact prefixLift 6685199
  have htrace : WordTrace (prefixWord ++ tailWord_6685199) baseStart_6685199 baseEnd_6685199 := by
    simpa [prefixWord, tailWord_6685199, baseEnd_6685199] using wordTrace_append hprefix tailTrace_6685199
  have hstable : (prefixWord ++ tailWord_6685199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685199).length < 2 ^ (prefixWord ++ tailWord_6685199).sum := by decide
  have hdescent : baseEnd_6685199 < baseStart_6685199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685203 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 3, 3, 2]
def baseStart_6685203 : Nat := 118140960795 + 6685203 * 2 ^ 59
def prefixEnd_6685203 : Nat := 4983230072969 + 3 ^ 40 * 6685203 * 2
def baseEnd_6685203 : Nat := 3432722411879312846217817

theorem tailTrace_6685203 : CollatzResearch.WordTrace tailWord_6685203 prefixEnd_6685203 3432722411879312846217817 := by
  unfold tailWord_6685203
  simp only [CollatzResearch.WordTrace]
  refine ⟨243829384799658747618804263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162552923199772498412536175 243829384799658747618804263)
  ·
    refine ⟨365744077199488121428206395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243829384799658747618804263 365744077199488121428206395)
    ·
      refine ⟨548616115799232182142309593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365744077199488121428206395 548616115799232182142309593)
      ·
        refine ⟨411462086849424136606732195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548616115799232182142309593 411462086849424136606732195)
        ·
          refine ⟨617193130274136204910098293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411462086849424136606732195 617193130274136204910098293)
          ·
            refine ⟨57861855963200269210321715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 617193130274136204910098293 57861855963200269210321715)
            ·
              refine ⟨86792783944800403815482573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57861855963200269210321715 86792783944800403815482573)
              ·
                refine ⟨32547293979300151430805965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86792783944800403815482573 32547293979300151430805965)
                ·
                  refine ⟨12205235242237556786552237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32547293979300151430805965 12205235242237556786552237)
                  ·
                    refine ⟨4576963215839083794957089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12205235242237556786552237 4576963215839083794957089)
                    ·
                      refine ⟨3432722411879312846217817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4576963215839083794957089 3432722411879312846217817)
                      ·
                        rfl

theorem cell23_6685203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 3, 2].length) (baseStart_6685203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685203 prefixEnd_6685203 := by exact prefixLift 6685203
  have htrace : WordTrace (prefixWord ++ tailWord_6685203) baseStart_6685203 baseEnd_6685203 := by
    simpa [prefixWord, tailWord_6685203, baseEnd_6685203] using wordTrace_append hprefix tailTrace_6685203
  have hstable : (prefixWord ++ tailWord_6685203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685203).length < 2 ^ (prefixWord ++ tailWord_6685203).sum := by decide
  have hdescent : baseEnd_6685203 < baseStart_6685203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685233 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 3, 4, 2]
def baseStart_6685233 : Nat := 118140960795 + 6685233 * 2 ^ 59
def prefixEnd_6685233 : Nat := 4983230072969 + 3 ^ 40 * 6685233 * 2
def baseEnd_6685233 : Nat := 3432737816298947728842679

theorem tailTrace_6685233 : CollatzResearch.WordTrace tailWord_6685233 prefixEnd_6685233 3432737816298947728842679 := by
  unfold tailWord_6685233
  simp only [CollatzResearch.WordTrace]
  refine ⟨243830478989550062742396353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162553652659700041828264235 243830478989550062742396353)
  ·
    refine ⟨182872859242162547056797265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243830478989550062742396353 182872859242162547056797265)
    ·
      refine ⟨137154644431621910292597949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182872859242162547056797265 137154644431621910292597949)
      ·
        refine ⟨51432991661858216359724231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137154644431621910292597949 51432991661858216359724231)
        ·
          refine ⟨77149487492787324539586347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51432991661858216359724231 77149487492787324539586347)
          ·
            refine ⟨115724231239180986809379521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77149487492787324539586347 115724231239180986809379521)
            ·
              refine ⟨86793173429385740107034641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115724231239180986809379521 86793173429385740107034641)
              ·
                refine ⟨65094880072039305080275981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86793173429385740107034641 65094880072039305080275981)
                ·
                  refine ⟨24410580027014739405103493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65094880072039305080275981 24410580027014739405103493)
                  ·
                    refine ⟨4576983755065263638456905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24410580027014739405103493 4576983755065263638456905)
                    ·
                      refine ⟨3432737816298947728842679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4576983755065263638456905 3432737816298947728842679)
                      ·
                        rfl

theorem cell23_6685233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_6685233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685233 prefixEnd_6685233 := by exact prefixLift 6685233
  have htrace : WordTrace (prefixWord ++ tailWord_6685233) baseStart_6685233 baseEnd_6685233 := by
    simpa [prefixWord, tailWord_6685233, baseEnd_6685233] using wordTrace_append hprefix tailTrace_6685233
  have hstable : (prefixWord ++ tailWord_6685233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685233).length < 2 ^ (prefixWord ++ tailWord_6685233).sum := by decide
  have hdescent : baseEnd_6685233 < baseStart_6685233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685254 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_6685254 : Nat := 118140960795 + 6685254 * 2 ^ 59
def prefixEnd_6685254 : Nat := 4983230072969 + 3 ^ 40 * 6685254 * 2
def baseEnd_6685254 : Nat := 3432748599392692146680083

theorem tailTrace_6685254 : CollatzResearch.WordTrace tailWord_6685254 prefixEnd_6685254 3432748599392692146680083 := by
  unfold tailWord_6685254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619726403827311979028463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162554163281649322219273877 7619726403827311979028463)
  ·
    refine ⟨11429589605740967968542695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7619726403827311979028463 11429589605740967968542695)
    ·
      refine ⟨17144384408611451952814043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11429589605740967968542695 17144384408611451952814043)
      ·
        refine ⟨25716576612917177929221065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17144384408611451952814043 25716576612917177929221065)
        ·
          refine ⟨19287432459687883446915799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25716576612917177929221065 19287432459687883446915799)
          ·
            refine ⟨28931148689531825170373699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19287432459687883446915799 28931148689531825170373699)
            ·
              refine ⟨43396723034297737755560549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28931148689531825170373699 43396723034297737755560549)
              ·
                refine ⟨8136885568930825829167603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43396723034297737755560549 8136885568930825829167603)
                ·
                  refine ⟨12205328353396238743751405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8136885568930825829167603 12205328353396238743751405)
                  ·
                    refine ⟨4576998132523589528906777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12205328353396238743751405 4576998132523589528906777)
                    ·
                      refine ⟨3432748599392692146680083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4576998132523589528906777 3432748599392692146680083)
                      ·
                        rfl

theorem cell23_6685254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_6685254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685254 prefixEnd_6685254 := by exact prefixLift 6685254
  have htrace : WordTrace (prefixWord ++ tailWord_6685254) baseStart_6685254 baseEnd_6685254 := by
    simpa [prefixWord, tailWord_6685254, baseEnd_6685254] using wordTrace_append hprefix tailTrace_6685254
  have hstable : (prefixWord ++ tailWord_6685254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685254).length < 2 ^ (prefixWord ++ tailWord_6685254).sum := by decide
  have hdescent : baseEnd_6685254 < baseStart_6685254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685323 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 3, 6, 2]
def baseStart_6685323 : Nat := 118140960795 + 6685323 * 2 ^ 59
def prefixEnd_6685323 : Nat := 4983230072969 + 3 ^ 40 * 6685323 * 2
def baseEnd_6685323 : Nat := 3432784029557852376717265

theorem tailTrace_6685323 : CollatzResearch.WordTrace tailWord_6685323 prefixEnd_6685323 3432784029557852376717265 := by
  unfold tailWord_6685323
  simp only [CollatzResearch.WordTrace]
  refine ⟨243833761559224008113172623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162555841039482672075448415 243833761559224008113172623)
  ·
    refine ⟨365750642338836012169758935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243833761559224008113172623 365750642338836012169758935)
    ·
      refine ⟨548625963508254018254638403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365750642338836012169758935 548625963508254018254638403)
      ·
        refine ⟨822938945262381027381957605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548625963508254018254638403 822938945262381027381957605)
        ·
          refine ⟨154301052236696442634117051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 822938945262381027381957605 154301052236696442634117051)
          ·
            refine ⟨231451578355044663951175577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154301052236696442634117051 231451578355044663951175577)
            ·
              refine ⟨173588683766283497963381683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231451578355044663951175577 173588683766283497963381683)
              ·
                refine ⟨260383025649425246945072525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173588683766283497963381683 260383025649425246945072525)
                ·
                  refine ⟨97643634618534467604402197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260383025649425246945072525 97643634618534467604402197)
                  ·
                    refine ⟨4577045372743803168956353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97643634618534467604402197 4577045372743803168956353)
                    ·
                      refine ⟨3432784029557852376717265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577045372743803168956353 3432784029557852376717265)
                      ·
                        rfl

theorem cell23_6685323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 6, 2].length) (baseStart_6685323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685323 prefixEnd_6685323 := by exact prefixLift 6685323
  have htrace : WordTrace (prefixWord ++ tailWord_6685323) baseStart_6685323 baseEnd_6685323 := by
    simpa [prefixWord, tailWord_6685323, baseEnd_6685323] using wordTrace_append hprefix tailTrace_6685323
  have hstable : (prefixWord ++ tailWord_6685323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685323).length < 2 ^ (prefixWord ++ tailWord_6685323).sum := by decide
  have hdescent : baseEnd_6685323 < baseStart_6685323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685340 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_6685340 : Nat := 118140960795 + 6685340 * 2 ^ 59
def prefixEnd_6685340 : Nat := 4983230072969 + 3 ^ 40 * 6685340 * 2
def baseEnd_6685340 : Nat := 3432792758728978810204687

theorem tailTrace_6685340 : CollatzResearch.WordTrace tailWord_6685340 prefixEnd_6685340 3432792758728978810204687 := by
  unfold tailWord_6685340
  simp only [CollatzResearch.WordTrace]
  refine ⟨121917190800081210008270737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162556254400108280011027649 121917190800081210008270737)
  ·
    refine ⟨91437893100060907506203053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121917190800081210008270737 91437893100060907506203053)
    ·
      refine ⟨34289209912522840314826145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91437893100060907506203053 34289209912522840314826145)
      ·
        refine ⟨25716907434392130236119609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34289209912522840314826145 25716907434392130236119609)
        ·
          refine ⟨19287680575794097677089707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25716907434392130236119609 19287680575794097677089707)
          ·
            refine ⟨28931520863691146515634561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19287680575794097677089707 28931520863691146515634561)
            ·
              refine ⟨21698640647768359886725921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28931520863691146515634561 21698640647768359886725921)
              ·
                refine ⟨16273980485826269915044441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21698640647768359886725921 16273980485826269915044441)
                ·
                  refine ⟨12205485364369702436283331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16273980485826269915044441 12205485364369702436283331)
                  ·
                    refine ⟨18308228046554553654424997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12205485364369702436283331 18308228046554553654424997)
                    ·
                      refine ⟨3432792758728978810204687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18308228046554553654424997 3432792758728978810204687)
                      ·
                        rfl

theorem cell23_6685340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_6685340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685340 prefixEnd_6685340 := by exact prefixLift 6685340
  have htrace : WordTrace (prefixWord ++ tailWord_6685340) baseStart_6685340 baseEnd_6685340 := by
    simpa [prefixWord, tailWord_6685340, baseEnd_6685340] using wordTrace_append hprefix tailTrace_6685340
  have hstable : (prefixWord ++ tailWord_6685340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685340).length < 2 ^ (prefixWord ++ tailWord_6685340).sum := by decide
  have hdescent : baseEnd_6685340 < baseStart_6685340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685357 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_6685357 : Nat := 118140960795 + 6685357 * 2 ^ 59
def prefixEnd_6685357 : Nat := 4983230072969 + 3 ^ 40 * 6685357 * 2
def baseEnd_6685357 : Nat := 3432801487900105243692109

theorem tailTrace_6685357 : CollatzResearch.WordTrace tailWord_6685357 prefixEnd_6685357 3432801487900105243692109 := by
  unfold tailWord_6685357
  simp only [CollatzResearch.WordTrace]
  refine ⟨243835001641100831919910325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162556667760733887946606883 243835001641100831919910325)
  ·
    refine ⟨22859531403853202992491593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243835001641100831919910325 22859531403853202992491593)
    ·
      refine ⟨17144648552889902244368695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22859531403853202992491593 17144648552889902244368695)
      ·
        refine ⟨25716972829334853366553043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17144648552889902244368695 25716972829334853366553043)
        ·
          refine ⟨38575459244002280049829565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25716972829334853366553043 38575459244002280049829565)
          ·
            refine ⟨14465797216500855018686087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38575459244002280049829565 14465797216500855018686087)
            ·
              refine ⟨21698695824751282528029131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14465797216500855018686087 21698695824751282528029131)
              ·
                refine ⟨32548043737126923792043697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21698695824751282528029131 32548043737126923792043697)
                ·
                  refine ⟨24411032802845192844032773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32548043737126923792043697 24411032802845192844032773)
                  ·
                    refine ⟨4577068650533473658256145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24411032802845192844032773 4577068650533473658256145)
                    ·
                      refine ⟨3432801487900105243692109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577068650533473658256145 3432801487900105243692109)
                      ·
                        rfl

theorem cell23_6685357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_6685357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685357 prefixEnd_6685357 := by exact prefixLift 6685357
  have htrace : WordTrace (prefixWord ++ tailWord_6685357) baseStart_6685357 baseEnd_6685357 := by
    simpa [prefixWord, tailWord_6685357, baseEnd_6685357] using wordTrace_append hprefix tailTrace_6685357
  have hstable : (prefixWord ++ tailWord_6685357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685357).length < 2 ^ (prefixWord ++ tailWord_6685357).sum := by decide
  have hdescent : baseEnd_6685357 < baseStart_6685357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685363 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 6]
def baseStart_6685363 : Nat := 118140960795 + 6685363 * 2 ^ 59
def prefixEnd_6685363 : Nat := 4983230072969 + 3 ^ 40 * 6685363 * 2
def baseEnd_6685363 : Nat := 381422729864892468913009

theorem tailTrace_6685363 : CollatzResearch.WordTrace tailWord_6685363 prefixEnd_6685363 381422729864892468913009 := by
  unfold tailWord_6685363
  simp only [CollatzResearch.WordTrace]
  refine ⟨243835220479079094944628743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162556813652719396629752495 243835220479079094944628743)
  ·
    refine ⟨365752830718618642416943115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243835220479079094944628743 365752830718618642416943115)
    ·
      refine ⟨548629246077927963625414673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365752830718618642416943115 548629246077927963625414673)
      ·
        refine ⟨411471934558445972719061005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548629246077927963625414673 411471934558445972719061005)
        ·
          refine ⟨154301975459417239769647877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411471934558445972719061005 154301975459417239769647877)
          ·
            refine ⟨28931620398640732456808977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154301975459417239769647877 28931620398640732456808977)
            ·
              refine ⟨21698715298980549342606733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28931620398640732456808977 21698715298980549342606733)
              ·
                refine ⟨8137018237117706003477525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21698715298980549342606733 8137018237117706003477525)
                ·
                  refine ⟨381422729864892468913009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8137018237117706003477525 381422729864892468913009)
                  ·
                    rfl

theorem cell23_6685363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 6].length) (baseStart_6685363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685363 prefixEnd_6685363 := by exact prefixLift 6685363
  have htrace : WordTrace (prefixWord ++ tailWord_6685363) baseStart_6685363 baseEnd_6685363 := by
    simpa [prefixWord, tailWord_6685363, baseEnd_6685363] using wordTrace_append hprefix tailTrace_6685363
  have hstable : (prefixWord ++ tailWord_6685363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685363).length < 2 ^ (prefixWord ++ tailWord_6685363).sum := by decide
  have hdescent : baseEnd_6685363 < baseStart_6685363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685407 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 3, 1, 3]
def baseStart_6685407 : Nat := 118140960795 + 6685407 * 2 ^ 59
def prefixEnd_6685407 : Nat := 4983230072969 + 3 ^ 40 * 6685407 * 2
def baseEnd_6685407 : Nat := 3432827161932830048066879

theorem tailTrace_6685407 : CollatzResearch.WordTrace tailWord_6685407 prefixEnd_6685407 3432827161932830048066879 := by
  unfold tailWord_6685407
  simp only [CollatzResearch.WordTrace]
  refine ⟨243836825290919690459230475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162557883527279793639486983 243836825290919690459230475)
  ·
    refine ⟨365755237936379535688845713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243836825290919690459230475 365755237936379535688845713)
    ·
      refine ⟨274316428452284651766634285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365755237936379535688845713 274316428452284651766634285)
      ·
        refine ⟨102868660669606744412487857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274316428452284651766634285 102868660669606744412487857)
        ·
          refine ⟨77151495502205058309365893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102868660669606744412487857 77151495502205058309365893)
          ·
            refine ⟨14465905406663448433006105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77151495502205058309365893 14465905406663448433006105)
            ·
              refine ⟨10849429054997586324754579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14465905406663448433006105 10849429054997586324754579)
              ·
                refine ⟨16274143582496379487131869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10849429054997586324754579 16274143582496379487131869)
                ·
                  refine ⟨6102803843436142307674451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16274143582496379487131869 6102803843436142307674451)
                  ·
                    refine ⟨9154205765154213461511677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6102803843436142307674451 9154205765154213461511677)
                    ·
                      refine ⟨3432827161932830048066879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9154205765154213461511677 3432827161932830048066879)
                      ·
                        rfl

theorem cell23_6685407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_6685407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685407 prefixEnd_6685407 := by exact prefixLift 6685407
  have htrace : WordTrace (prefixWord ++ tailWord_6685407) baseStart_6685407 baseEnd_6685407 := by
    simpa [prefixWord, tailWord_6685407, baseEnd_6685407] using wordTrace_append hprefix tailTrace_6685407
  have hstable : (prefixWord ++ tailWord_6685407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685407).length < 2 ^ (prefixWord ++ tailWord_6685407).sum := by decide
  have hdescent : baseEnd_6685407 < baseStart_6685407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685433 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 2, 6, 3]
def baseStart_6685433 : Nat := 118140960795 + 6685433 * 2 ^ 59
def prefixEnd_6685433 : Nat := 4983230072969 + 3 ^ 40 * 6685433 * 2
def baseEnd_6685433 : Nat := 3432840512429846946341759

theorem tailTrace_6685433 : CollatzResearch.WordTrace tailWord_6685433 prefixEnd_6685433 3432840512429846946341759 := by
  unfold tailWord_6685433
  simp only [CollatzResearch.WordTrace]
  refine ⟨243837773588825496899676953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162558515725883664599784635 243837773588825496899676953)
  ·
    refine ⟨182878330191619122674757715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243837773588825496899676953 182878330191619122674757715)
    ·
      refine ⟨274317495287428684012136573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182878330191619122674757715 274317495287428684012136573)
      ·
        refine ⟨102869060732785756504551215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274317495287428684012136573 102869060732785756504551215)
        ·
          refine ⟨154303591099178634756826823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102869060732785756504551215 154303591099178634756826823)
          ·
            refine ⟨231455386648767952135240235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154303591099178634756826823 231455386648767952135240235)
            ·
              refine ⟨347183079973151928202860353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231455386648767952135240235 347183079973151928202860353)
              ·
                refine ⟨260387309979863946152145265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347183079973151928202860353 260387309979863946152145265)
                ·
                  refine ⟨195290482484897959614108949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260387309979863946152145265 195290482484897959614108949)
                  ·
                    refine ⟨9154241366479591856911357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 195290482484897959614108949 9154241366479591856911357)
                    ·
                      refine ⟨3432840512429846946341759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9154241366479591856911357 3432840512429846946341759)
                      ·
                        rfl

theorem cell23_6685433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_6685433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685433 prefixEnd_6685433 := by exact prefixLift 6685433
  have htrace : WordTrace (prefixWord ++ tailWord_6685433) baseStart_6685433 baseEnd_6685433 := by
    simpa [prefixWord, tailWord_6685433, baseEnd_6685433] using wordTrace_append hprefix tailTrace_6685433
  have hstable : (prefixWord ++ tailWord_6685433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685433).length < 2 ^ (prefixWord ++ tailWord_6685433).sum := by decide
  have hdescent : baseEnd_6685433 < baseStart_6685433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685443 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 4]
def baseStart_6685443 : Nat := 118140960795 + 6685443 * 2 ^ 59
def prefixEnd_6685443 : Nat := 4983230072969 + 3 ^ 40 * 6685443 * 2
def baseEnd_6685443 : Nat := 3432845647236391907216713

theorem tailTrace_6685443 : CollatzResearch.WordTrace tailWord_6685443 prefixEnd_6685443 3432845647236391907216713 := by
  unfold tailWord_6685443
  simp only [CollatzResearch.WordTrace]
  refine ⟨243838138318789268607540983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162558758879192845738360655 243838138318789268607540983)
  ·
    refine ⟨365757207478183902911311475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243838138318789268607540983 365757207478183902911311475)
    ·
      refine ⟨548635811217275854366967213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365757207478183902911311475 548635811217275854366967213)
      ·
        refine ⟨205738429206478445387612705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548635811217275854366967213 205738429206478445387612705)
        ·
          refine ⟨154303821904858834040709529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205738429206478445387612705 154303821904858834040709529)
          ·
            refine ⟨115727866428644125530532147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154303821904858834040709529 115727866428644125530532147)
            ·
              refine ⟨173591799642966188295798221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115727866428644125530532147 173591799642966188295798221)
              ·
                refine ⟨65096924866112320610924333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173591799642966188295798221 65096924866112320610924333)
                ·
                  refine ⟨24411346824792120229096625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65096924866112320610924333 24411346824792120229096625)
                  ·
                    refine ⟨18308510118594090171822469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24411346824792120229096625 18308510118594090171822469)
                    ·
                      refine ⟨3432845647236391907216713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18308510118594090171822469 3432845647236391907216713)
                      ·
                        rfl

theorem cell23_6685443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_6685443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685443 prefixEnd_6685443 := by exact prefixLift 6685443
  have htrace : WordTrace (prefixWord ++ tailWord_6685443) baseStart_6685443 baseEnd_6685443 := by
    simpa [prefixWord, tailWord_6685443, baseEnd_6685443] using wordTrace_append hprefix tailTrace_6685443
  have hstable : (prefixWord ++ tailWord_6685443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685443).length < 2 ^ (prefixWord ++ tailWord_6685443).sum := by decide
  have hdescent : baseEnd_6685443 < baseStart_6685443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685447 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_6685447 : Nat := 118140960795 + 6685447 * 2 ^ 59
def prefixEnd_6685447 : Nat := 4983230072969 + 3 ^ 40 * 6685447 * 2
def baseEnd_6685447 : Nat := 3432847701159009891566695

theorem tailTrace_6685447 : CollatzResearch.WordTrace tailWord_6685447 prefixEnd_6685447 3432847701159009891566695 := by
  unfold tailWord_6685447
  simp only [CollatzResearch.WordTrace]
  refine ⟨243838284210774777290686595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162558856140516518193791063 243838284210774777290686595)
  ·
    refine ⟨365757426316162165936029893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243838284210774777290686595 365757426316162165936029893)
    ·
      refine ⟨68579517434280406113005605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365757426316162165936029893 68579517434280406113005605)
      ·
        refine ⟨12858659518927576146188551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68579517434280406113005605 12858659518927576146188551)
        ·
          refine ⟨19287989278391364219282827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12858659518927576146188551 19287989278391364219282827)
          ·
            refine ⟨28931983917587046328924241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19287989278391364219282827 28931983917587046328924241)
            ·
              refine ⟨21698987938190284746693181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28931983917587046328924241 21698987938190284746693181)
              ·
                refine ⟨8137120476821356780009943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21698987938190284746693181 8137120476821356780009943)
                ·
                  refine ⟨12205680715232035170014915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8137120476821356780009943 12205680715232035170014915)
                  ·
                    refine ⟨18308521072848052755022373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12205680715232035170014915 18308521072848052755022373)
                    ·
                      refine ⟨3432847701159009891566695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18308521072848052755022373 3432847701159009891566695)
                      ·
                        rfl

theorem cell23_6685447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_6685447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685447 prefixEnd_6685447 := by exact prefixLift 6685447
  have htrace : WordTrace (prefixWord ++ tailWord_6685447) baseStart_6685447 baseEnd_6685447 := by
    simpa [prefixWord, tailWord_6685447, baseEnd_6685447] using wordTrace_append hprefix tailTrace_6685447
  have hstable : (prefixWord ++ tailWord_6685447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685447).length < 2 ^ (prefixWord ++ tailWord_6685447).sum := by decide
  have hdescent : baseEnd_6685447 < baseStart_6685447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685450 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_6685450 : Nat := 118140960795 + 6685450 * 2 ^ 59
def prefixEnd_6685450 : Nat := 4983230072969 + 3 ^ 40 * 6685450 * 2
def baseEnd_6685450 : Nat := 3432849241600973379829181

theorem tailTrace_6685450 : CollatzResearch.WordTrace tailWord_6685450 prefixEnd_6685450 3432849241600973379829181 := by
  unfold tailWord_6685450
  simp only [CollatzResearch.WordTrace]
  refine ⟨60959598407440977200761451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162558929086509272535363869 60959598407440977200761451)
  ·
    refine ⟨91439397611161465801142177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60959598407440977200761451 91439397611161465801142177)
    ·
      refine ⟨68579548208371099350856633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91439397611161465801142177 68579548208371099350856633)
      ·
        refine ⟨51434661156278324513142475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68579548208371099350856633 51434661156278324513142475)
        ·
          refine ⟨77151991734417486769713713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51434661156278324513142475 77151991734417486769713713)
          ·
            refine ⟨57863993800813115077285285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77151991734417486769713713 57863993800813115077285285)
            ·
              refine ⟨10849498837652459076990991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57863993800813115077285285 10849498837652459076990991)
              ·
                refine ⟨16274248256478688615486487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10849498837652459076990991 16274248256478688615486487)
                ·
                  refine ⟨24411372384718032923229731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16274248256478688615486487 24411372384718032923229731)
                  ·
                    refine ⟨36617058577077049384844597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24411372384718032923229731 36617058577077049384844597)
                    ·
                      refine ⟨3432849241600973379829181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36617058577077049384844597 3432849241600973379829181)
                      ·
                        rfl

theorem cell23_6685450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_6685450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685450 prefixEnd_6685450 := by exact prefixLift 6685450
  have htrace : WordTrace (prefixWord ++ tailWord_6685450) baseStart_6685450 baseEnd_6685450 := by
    simpa [prefixWord, tailWord_6685450, baseEnd_6685450] using wordTrace_append hprefix tailTrace_6685450
  have hstable : (prefixWord ++ tailWord_6685450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685450).length < 2 ^ (prefixWord ++ tailWord_6685450).sum := by decide
  have hdescent : baseEnd_6685450 < baseStart_6685450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685458 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_6685458 : Nat := 118140960795 + 6685458 * 2 ^ 59
def prefixEnd_6685458 : Nat := 4983230072969 + 3 ^ 40 * 6685458 * 2
def baseEnd_6685458 : Nat := 3432853349446209348529145

theorem tailTrace_6685458 : CollatzResearch.WordTrace tailWord_6685458 prefixEnd_6685458 3432853349446209348529145 := by
  unfold tailWord_6685458
  simp only [CollatzResearch.WordTrace]
  refine ⟨60959671353433731542334257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162559123609156617446224685 60959671353433731542334257)
  ·
    refine ⟨45719753515075298656750693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60959671353433731542334257 45719753515075298656750693)
    ·
      refine ⟨8572453784076618498140755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45719753515075298656750693 8572453784076618498140755)
      ·
        refine ⟨12858680676114927747211133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572453784076618498140755 12858680676114927747211133)
        ·
          refine ⟨4822005253543097905204175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12858680676114927747211133 4822005253543097905204175)
          ·
            refine ⟨7233007880314646857806263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822005253543097905204175 7233007880314646857806263)
            ·
              refine ⟨10849511820471970286709395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7233007880314646857806263 10849511820471970286709395)
              ·
                refine ⟨16274267730707955430064093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10849511820471970286709395 16274267730707955430064093)
                ·
                  refine ⟨6102850399015483286274035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16274267730707955430064093 6102850399015483286274035)
                  ·
                    refine ⟨9154275598523224929411053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6102850399015483286274035 9154275598523224929411053)
                    ·
                      refine ⟨3432853349446209348529145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9154275598523224929411053 3432853349446209348529145)
                      ·
                        rfl

theorem cell23_6685458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_6685458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685458 prefixEnd_6685458 := by exact prefixLift 6685458
  have htrace : WordTrace (prefixWord ++ tailWord_6685458) baseStart_6685458 baseEnd_6685458 := by
    simpa [prefixWord, tailWord_6685458, baseEnd_6685458] using wordTrace_append hprefix tailTrace_6685458
  have hstable : (prefixWord ++ tailWord_6685458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685458).length < 2 ^ (prefixWord ++ tailWord_6685458).sum := by decide
  have hdescent : baseEnd_6685458 < baseStart_6685458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685473 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6685473 : Nat := 118140960795 + 6685473 * 2 ^ 59
def prefixEnd_6685473 : Nat := 4983230072969 + 3 ^ 40 * 6685473 * 2
def baseEnd_6685473 : Nat := 3432861051656026789841575

theorem tailTrace_6685473 : CollatzResearch.WordTrace tailWord_6685473 prefixEnd_6685473 3432861051656026789841575 := by
  unfold tailWord_6685473
  simp only [CollatzResearch.WordTrace]
  refine ⟨243839232508680583731133073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162559488339120389154088715 243839232508680583731133073)
  ·
    refine ⟨182879424381510437798349805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243839232508680583731133073 182879424381510437798349805)
    ·
      refine ⟨68579784143066414174381177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182879424381510437798349805 68579784143066414174381177)
      ·
        refine ⟨51434838107299810630785883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68579784143066414174381177 51434838107299810630785883)
        ·
          refine ⟨77152257160949715946178825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51434838107299810630785883 77152257160949715946178825)
          ·
            refine ⟨57864192870712286959634119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77152257160949715946178825 57864192870712286959634119)
            ·
              refine ⟨86796289306068430439451179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57864192870712286959634119 86796289306068430439451179)
              ·
                refine ⟨130194433959102645659176769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86796289306068430439451179 130194433959102645659176769)
                ·
                  refine ⟨97645825469326984244382577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130194433959102645659176769 97645825469326984244382577)
                  ·
                    refine ⟨73234369101995238183286933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97645825469326984244382577 73234369101995238183286933)
                    ·
                      refine ⟨3432861051656026789841575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73234369101995238183286933 3432861051656026789841575)
                      ·
                        rfl

theorem cell23_6685473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6685473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685473 prefixEnd_6685473 := by exact prefixLift 6685473
  have htrace : WordTrace (prefixWord ++ tailWord_6685473) baseStart_6685473 baseEnd_6685473 := by
    simpa [prefixWord, tailWord_6685473, baseEnd_6685473] using wordTrace_append hprefix tailTrace_6685473
  have hstable : (prefixWord ++ tailWord_6685473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685473).length < 2 ^ (prefixWord ++ tailWord_6685473).sum := by decide
  have hdescent : baseEnd_6685473 < baseStart_6685473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685474 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_6685474 : Nat := 118140960795 + 6685474 * 2 ^ 59
def prefixEnd_6685474 : Nat := 4983230072969 + 3 ^ 40 * 6685474 * 2
def baseEnd_6685474 : Nat := 1144287188378893761976357

theorem tailTrace_6685474 : CollatzResearch.WordTrace tailWord_6685474 prefixEnd_6685474 1144287188378893761976357 := by
  unfold tailWord_6685474
  simp only [CollatzResearch.WordTrace]
  refine ⟨60959817245419240225479869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162559512654451307267946317 60959817245419240225479869)
  ·
    refine ⟨22859931467032215084554951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60959817245419240225479869 22859931467032215084554951)
    ·
      refine ⟨34289897200548322626832427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22859931467032215084554951 34289897200548322626832427)
      ·
        refine ⟨51434845800822483940248641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34289897200548322626832427 51434845800822483940248641)
        ·
          refine ⟨38576134350616862955186481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51434845800822483940248641 38576134350616862955186481)
          ·
            refine ⟨28932100762962647216389861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38576134350616862955186481 28932100762962647216389861)
            ·
              refine ⟨5424768893055496353073099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28932100762962647216389861 5424768893055496353073099)
              ·
                refine ⟨8137153339583244529609649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5424768893055496353073099 8137153339583244529609649)
                ·
                  refine ⟨6102865004687433397207237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8137153339583244529609649 6102865004687433397207237)
                  ·
                    refine ⟨1144287188378893761976357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6102865004687433397207237 1144287188378893761976357)
                    ·
                      rfl

theorem cell23_6685474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_6685474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685474 prefixEnd_6685474 := by exact prefixLift 6685474
  have htrace : WordTrace (prefixWord ++ tailWord_6685474) baseStart_6685474 baseEnd_6685474 := by
    simpa [prefixWord, tailWord_6685474, baseEnd_6685474] using wordTrace_append hprefix tailTrace_6685474
  have hstable : (prefixWord ++ tailWord_6685474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685474).length < 2 ^ (prefixWord ++ tailWord_6685474).sum := by decide
  have hdescent : baseEnd_6685474 < baseStart_6685474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685494 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_6685494 : Nat := 118140960795 + 6685494 * 2 ^ 59
def prefixEnd_6685494 : Nat := 4983230072969 + 3 ^ 40 * 6685494 * 2
def baseEnd_6685494 : Nat := 3432871834749771207678979

theorem tailTrace_6685494 : CollatzResearch.WordTrace tailWord_6685494 prefixEnd_6685494 3432871834749771207678979 := by
  unfold tailWord_6685494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15239999902600281519852971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162559998961069669545098357 15239999902600281519852971)
  ·
    refine ⟨22859999853900422279779457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15239999902600281519852971 22859999853900422279779457)
    ·
      refine ⟨17144999890425316709834593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22859999853900422279779457 17144999890425316709834593)
      ·
        refine ⟨12858749917818987532375945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17144999890425316709834593 12858749917818987532375945)
        ·
          refine ⟨9644062438364240649281959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12858749917818987532375945 9644062438364240649281959)
          ·
            refine ⟨14466093657546360973922939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9644062438364240649281959 14466093657546360973922939)
            ·
              refine ⟨21699140486319541460884409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14466093657546360973922939 21699140486319541460884409)
              ·
                refine ⟨16274355364739656095663307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21699140486319541460884409 16274355364739656095663307)
                ·
                  refine ⟨24411533047109484143494961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16274355364739656095663307 24411533047109484143494961)
                  ·
                    refine ⟨18308649785332113107621221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24411533047109484143494961 18308649785332113107621221)
                    ·
                      refine ⟨3432871834749771207678979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18308649785332113107621221 3432871834749771207678979)
                      ·
                        rfl

theorem cell23_6685494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_6685494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685494 prefixEnd_6685494 := by exact prefixLift 6685494
  have htrace : WordTrace (prefixWord ++ tailWord_6685494) baseStart_6685494 baseEnd_6685494 := by
    simpa [prefixWord, tailWord_6685494, baseEnd_6685494] using wordTrace_append hprefix tailTrace_6685494
  have hstable : (prefixWord ++ tailWord_6685494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685494).length < 2 ^ (prefixWord ++ tailWord_6685494).sum := by decide
  have hdescent : baseEnd_6685494 < baseStart_6685494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685501 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 1, 2, 3]
def baseStart_6685501 : Nat := 118140960795 + 6685501 * 2 ^ 59
def prefixEnd_6685501 : Nat := 4983230072969 + 3 ^ 40 * 6685501 * 2
def baseEnd_6685501 : Nat := 3432875429114352680291447

theorem tailTrace_6685501 : CollatzResearch.WordTrace tailWord_6685501 prefixEnd_6685501 3432875429114352680291447 := by
  unfold tailWord_6685501
  simp only [CollatzResearch.WordTrace]
  refine ⟨243840253752579144513152357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162560169168386096342101571 243840253752579144513152357)
  ·
    refine ⟨45720047578608589596216067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243840253752579144513152357 45720047578608589596216067)
    ·
      refine ⟨68580071367912884394324101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45720047578608589596216067 68580071367912884394324101)
      ·
        refine ⟨12858763381483665823935769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68580071367912884394324101 12858763381483665823935769)
        ·
          refine ⟨9644072536112749367951827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12858763381483665823935769 9644072536112749367951827)
          ·
            refine ⟨14466108804169124051927741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9644072536112749367951827 14466108804169124051927741)
            ·
              refine ⟨5424790801563421519472903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14466108804169124051927741 5424790801563421519472903)
              ·
                refine ⟨8137186202345132279209355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5424790801563421519472903 8137186202345132279209355)
                ·
                  refine ⟨12205779303517698418814033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8137186202345132279209355 12205779303517698418814033)
                  ·
                    refine ⟨9154334477638273814110525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12205779303517698418814033 9154334477638273814110525)
                    ·
                      refine ⟨3432875429114352680291447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9154334477638273814110525 3432875429114352680291447)
                      ·
                        rfl

theorem cell23_6685501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_6685501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685501 prefixEnd_6685501 := by exact prefixLift 6685501
  have htrace : WordTrace (prefixWord ++ tailWord_6685501) baseStart_6685501 baseEnd_6685501 := by
    simpa [prefixWord, tailWord_6685501, baseEnd_6685501] using wordTrace_append hprefix tailTrace_6685501
  have hstable : (prefixWord ++ tailWord_6685501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685501).length < 2 ^ (prefixWord ++ tailWord_6685501).sum := by decide
  have hdescent : baseEnd_6685501 < baseStart_6685501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685523 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 5]
def baseStart_6685523 : Nat := 118140960795 + 6685523 * 2 ^ 59
def prefixEnd_6685523 : Nat := 4983230072969 + 3 ^ 40 * 6685523 * 2
def baseEnd_6685523 : Nat := 3432886725688751594216345

theorem tailTrace_6685523 : CollatzResearch.WordTrace tailWord_6685523 prefixEnd_6685523 3432886725688751594216345 := by
  unfold tailWord_6685523
  simp only [CollatzResearch.WordTrace]
  refine ⟨243841056158499442270453223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162560704105666294846968815 243841056158499442270453223)
  ·
    refine ⟨365761584237749163405679835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243841056158499442270453223 365761584237749163405679835)
    ·
      refine ⟨548642376356623745108519753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365761584237749163405679835 548642376356623745108519753)
      ·
        refine ⟨411481782267467808831389815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548642376356623745108519753 411481782267467808831389815)
        ·
          refine ⟨617222673401201713247084723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411481782267467808831389815 617222673401201713247084723)
          ·
            refine ⟨925834010101802569870627085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617222673401201713247084723 925834010101802569870627085)
            ·
              refine ⟨347187753788175963701485157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925834010101802569870627085 347187753788175963701485157)
              ·
                refine ⟨65097703835282993194028467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347187753788175963701485157 65097703835282993194028467)
                ·
                  refine ⟨97646555752924489791042701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65097703835282993194028467 97646555752924489791042701)
                  ·
                    refine ⟨36617458407346683671641013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97646555752924489791042701 36617458407346683671641013)
                    ·
                      refine ⟨3432886725688751594216345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36617458407346683671641013 3432886725688751594216345)
                      ·
                        rfl

theorem cell23_6685523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_6685523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685523 prefixEnd_6685523 := by exact prefixLift 6685523
  have htrace : WordTrace (prefixWord ++ tailWord_6685523) baseStart_6685523 baseEnd_6685523 := by
    simpa [prefixWord, tailWord_6685523, baseEnd_6685523] using wordTrace_append hprefix tailTrace_6685523
  have hstable : (prefixWord ++ tailWord_6685523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685523).length < 2 ^ (prefixWord ++ tailWord_6685523).sum := by decide
  have hdescent : baseEnd_6685523 < baseStart_6685523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685530 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_6685530 : Nat := 118140960795 + 6685530 * 2 ^ 59
def prefixEnd_6685530 : Nat := 4983230072969 + 3 ^ 40 * 6685530 * 2
def baseEnd_6685530 : Nat := 1144296773351111022276271

theorem tailTrace_6685530 : CollatzResearch.WordTrace tailWord_6685530 prefixEnd_6685530 1144296773351111022276271 := by
  unfold tailWord_6685530
  simp only [CollatzResearch.WordTrace]
  refine ⟨60960327867368520616489511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162560874312982721643972029 60960327867368520616489511)
  ·
    refine ⟨91440491801052780924734267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60960327867368520616489511 91440491801052780924734267)
    ·
      refine ⟨137160737701579171387101401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91440491801052780924734267 137160737701579171387101401)
      ·
        refine ⟨102870553276184378540326051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137160737701579171387101401 102870553276184378540326051)
        ·
          refine ⟨154305829914276567810489077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102870553276184378540326051 154305829914276567810489077)
          ·
            refine ⟨14466171554463428232233351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154305829914276567810489077 14466171554463428232233351)
            ·
              refine ⟨21699257331695142348350027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14466171554463428232233351 21699257331695142348350027)
              ·
                refine ⟨32548885997542713522525041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21699257331695142348350027 32548885997542713522525041)
                ·
                  refine ⟨24411664498157035141893781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32548885997542713522525041 24411664498157035141893781)
                  ·
                    refine ⟨1144296773351111022276271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24411664498157035141893781 1144296773351111022276271)
                    ·
                      rfl

theorem cell23_6685530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_6685530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685530 prefixEnd_6685530 := by exact prefixLift 6685530
  have htrace : WordTrace (prefixWord ++ tailWord_6685530) baseStart_6685530 baseEnd_6685530 := by
    simpa [prefixWord, tailWord_6685530, baseEnd_6685530] using wordTrace_append hprefix tailTrace_6685530
  have hstable : (prefixWord ++ tailWord_6685530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685530).length < 2 ^ (prefixWord ++ tailWord_6685530).sum := by decide
  have hdescent : baseEnd_6685530 < baseStart_6685530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685558 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_6685558 : Nat := 118140960795 + 6685558 * 2 ^ 59
def prefixEnd_6685558 : Nat := 4983230072969 + 3 ^ 40 * 6685558 * 2
def baseEnd_6685558 : Nat := 3432904697511658957278685

theorem tailTrace_6685558 : CollatzResearch.WordTrace tailWord_6685558 prefixEnd_6685558 3432904697511658957278685 := by
  unfold tailWord_6685558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15240145794585790202998583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162561555142248428831984885 15240145794585790202998583)
  ·
    refine ⟨22860218691878685304497875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15240145794585790202998583 22860218691878685304497875)
    ·
      refine ⟨34290328037818027956746813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22860218691878685304497875 34290328037818027956746813)
      ·
        refine ⟨12858873014181760483780055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34290328037818027956746813 12858873014181760483780055)
        ·
          refine ⟨19288309521272640725670083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12858873014181760483780055 19288309521272640725670083)
          ·
            refine ⟨28932464281908961088505125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19288309521272640725670083 28932464281908961088505125)
            ·
              refine ⟨5424837052857930204094711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28932464281908961088505125 5424837052857930204094711)
              ·
                refine ⟨8137255579286895306142067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5424837052857930204094711 8137255579286895306142067)
                ·
                  refine ⟨12205883368930342959213101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8137255579286895306142067 12205883368930342959213101)
                  ·
                    refine ⟨4577206263348878609704913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12205883368930342959213101 4577206263348878609704913)
                    ·
                      refine ⟨3432904697511658957278685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577206263348878609704913 3432904697511658957278685)
                      ·
                        rfl

theorem cell23_6685558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_6685558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685558 prefixEnd_6685558 := by exact prefixLift 6685558
  have htrace : WordTrace (prefixWord ++ tailWord_6685558) baseStart_6685558 baseEnd_6685558 := by
    simpa [prefixWord, tailWord_6685558, baseEnd_6685558] using wordTrace_append hprefix tailTrace_6685558
  have hstable : (prefixWord ++ tailWord_6685558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685558).length < 2 ^ (prefixWord ++ tailWord_6685558).sum := by decide
  have hdescent : baseEnd_6685558 < baseStart_6685558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685577 : List Nat := [1, 2, 1, 1, 5, 2, 2, 4, 5]
def baseStart_6685577 : Nat := 118140960795 + 6685577 * 2 ^ 59
def prefixEnd_6685577 : Nat := 4983230072969 + 3 ^ 40 * 6685577 * 2
def baseEnd_6685577 : Nat := 381434939293788264771233

theorem tailTrace_6685577 : CollatzResearch.WordTrace tailWord_6685577 prefixEnd_6685577 381434939293788264771233 := by
  unfold tailWord_6685577
  simp only [CollatzResearch.WordTrace]
  refine ⟨243843025700303809492918985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162562017133535872995279323 243843025700303809492918985)
  ·
    refine ⟨182882269275227857119689239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243843025700303809492918985 182882269275227857119689239)
    ·
      refine ⟨274323403912841785679533859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182882269275227857119689239 274323403912841785679533859)
      ·
        refine ⟨411485105869262678519300789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274323403912841785679533859 411485105869262678519300789)
        ·
          refine ⟨38576728675243376111184449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 411485105869262678519300789 38576728675243376111184449)
          ·
            refine ⟨28932546506432532083388337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38576728675243376111184449 28932546506432532083388337)
            ·
              refine ⟨21699409879824399062541253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28932546506432532083388337 21699409879824399062541253)
              ·
                refine ⟨4068639352467074824226485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21699409879824399062541253 4068639352467074824226485)
                ·
                  refine ⟨381434939293788264771233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4068639352467074824226485 381434939293788264771233)
                  ·
                    rfl

theorem cell23_6685577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 5].length) (baseStart_6685577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685577 prefixEnd_6685577 := by exact prefixLift 6685577
  have htrace : WordTrace (prefixWord ++ tailWord_6685577) baseStart_6685577 baseEnd_6685577 := by
    simpa [prefixWord, tailWord_6685577, baseEnd_6685577] using wordTrace_append hprefix tailTrace_6685577
  have hstable : (prefixWord ++ tailWord_6685577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685577).length < 2 ^ (prefixWord ++ tailWord_6685577).sum := by decide
  have hdescent : baseEnd_6685577 < baseStart_6685577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685588 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_6685588 : Nat := 118140960795 + 6685588 * 2 ^ 59
def prefixEnd_6685588 : Nat := 4983230072969 + 3 ^ 40 * 6685588 * 2
def baseEnd_6685588 : Nat := 3432920101931293839903547

theorem tailTrace_6685588 : CollatzResearch.WordTrace tailWord_6685588 prefixEnd_6685588 3432920101931293839903547 := by
  unfold tailWord_6685588
  simp only [CollatzResearch.WordTrace]
  refine ⟨121921713451631979185784709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162562284602175972247712945 121921713451631979185784709)
  ·
    refine ⟨22860321272180996097334633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121921713451631979185784709 22860321272180996097334633)
    ·
      refine ⟨17145240954135747073000975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22860321272180996097334633 17145240954135747073000975)
      ·
        refine ⟨25717861431203620609501463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17145240954135747073000975 25717861431203620609501463)
        ·
          refine ⟨38576792146805430914252195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25717861431203620609501463 38576792146805430914252195)
          ·
            refine ⟨57865188220208146371378293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38576792146805430914252195 57865188220208146371378293)
            ·
              refine ⟨5424861395644513722316715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57865188220208146371378293 5424861395644513722316715)
              ·
                refine ⟨8137292093466770583475073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5424861395644513722316715 8137292093466770583475073)
                ·
                  refine ⟨6102969070100077937606305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8137292093466770583475073 6102969070100077937606305)
                  ·
                    refine ⟨4577226802575058453204729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6102969070100077937606305 4577226802575058453204729)
                    ·
                      refine ⟨3432920101931293839903547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577226802575058453204729 3432920101931293839903547)
                      ·
                        rfl

theorem cell23_6685588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_6685588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685588 prefixEnd_6685588 := by exact prefixLift 6685588
  have htrace : WordTrace (prefixWord ++ tailWord_6685588) baseStart_6685588 baseEnd_6685588 := by
    simpa [prefixWord, tailWord_6685588, baseEnd_6685588] using wordTrace_append hprefix tailTrace_6685588
  have hstable : (prefixWord ++ tailWord_6685588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685588).length < 2 ^ (prefixWord ++ tailWord_6685588).sum := by decide
  have hdescent : baseEnd_6685588 < baseStart_6685588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685690 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_6685690 : Nat := 118140960795 + 6685690 * 2 ^ 59
def prefixEnd_6685690 : Nat := 4983230072969 + 3 ^ 40 * 6685690 * 2
def baseEnd_6685690 : Nat := 3432972476958052440828077

theorem tailTrace_6685690 : CollatzResearch.WordTrace tailWord_6685690 prefixEnd_6685690 3432972476958052440828077 := by
  unfold tailWord_6685690
  simp only [CollatzResearch.WordTrace]
  refine ⟨60961786787223607447945631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162564764765929619861188349 60961786787223607447945631)
  ·
    refine ⟨91442680180835411171918447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60961786787223607447945631 91442680180835411171918447)
    ·
      refine ⟨137164020271253116757877671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91442680180835411171918447 137164020271253116757877671)
      ·
        refine ⟨205746030406879675136816507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137164020271253116757877671 205746030406879675136816507)
        ·
          refine ⟨308619045610319512705224761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205746030406879675136816507 308619045610319512705224761)
          ·
            refine ⟨231464284207739634528918571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308619045610319512705224761 231464284207739634528918571)
            ·
              refine ⟨347196426311609451793377857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231464284207739634528918571 347196426311609451793377857)
              ·
                refine ⟨260397319733707088845033393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347196426311609451793377857 260397319733707088845033393)
                ·
                  refine ⟨195297989800280316633775045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260397319733707088845033393 195297989800280316633775045)
                  ·
                    refine ⟨36618373087552559368832821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195297989800280316633775045 36618373087552559368832821)
                    ·
                      refine ⟨3432972476958052440828077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36618373087552559368832821 3432972476958052440828077)
                      ·
                        rfl

theorem cell23_6685690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_6685690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685690 prefixEnd_6685690 := by exact prefixLift 6685690
  have htrace : WordTrace (prefixWord ++ tailWord_6685690) baseStart_6685690 baseEnd_6685690 := by
    simpa [prefixWord, tailWord_6685690, baseEnd_6685690] using wordTrace_append hprefix tailTrace_6685690
  have hstable : (prefixWord ++ tailWord_6685690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685690).length < 2 ^ (prefixWord ++ tailWord_6685690).sum := by decide
  have hdescent : baseEnd_6685690 < baseStart_6685690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685697 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 3, 5]
def baseStart_6685697 : Nat := 118140960795 + 6685697 * 2 ^ 59
def prefixEnd_6685697 : Nat := 4983230072969 + 3 ^ 40 * 6685697 * 2
def baseEnd_6685697 : Nat := 1144325357107544637813515

theorem tailTrace_6685697 : CollatzResearch.WordTrace tailWord_6685697 prefixEnd_6685697 1144325357107544637813515 := by
  unfold tailWord_6685697
  simp only [CollatzResearch.WordTrace]
  refine ⟨243847402459869069987287345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162564934973246046658191563 243847402459869069987287345)
  ·
    refine ⟨182885551844901802490465509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243847402459869069987287345 182885551844901802490465509)
    ·
      refine ⟨34291040970919087966962283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182885551844901802490465509 34291040970919087966962283)
      ·
        refine ⟨51436561456378631950443425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34291040970919087966962283 51436561456378631950443425)
        ·
          refine ⟨38577421092283973962832569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51436561456378631950443425 38577421092283973962832569)
          ·
            refine ⟨28933065819212980472124427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38577421092283973962832569 28933065819212980472124427)
            ·
              refine ⟨43399598728819470708186641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28933065819212980472124427 43399598728819470708186641)
              ·
                refine ⟨32549699046614603031139981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43399598728819470708186641 32549699046614603031139981)
                ·
                  refine ⟨12206137142480476136677493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32549699046614603031139981 12206137142480476136677493)
                  ·
                    refine ⟨1144325357107544637813515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12206137142480476136677493 1144325357107544637813515)
                    ·
                      rfl

theorem cell23_6685697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_6685697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685697 prefixEnd_6685697 := by exact prefixLift 6685697
  have htrace : WordTrace (prefixWord ++ tailWord_6685697) baseStart_6685697 baseEnd_6685697 := by
    simpa [prefixWord, tailWord_6685697, baseEnd_6685697] using wordTrace_append hprefix tailTrace_6685697
  have hstable : (prefixWord ++ tailWord_6685697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685697).length < 2 ^ (prefixWord ++ tailWord_6685697).sum := by decide
  have hdescent : baseEnd_6685697 < baseStart_6685697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685727 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 1, 6]
def baseStart_6685727 : Nat := 118140960795 + 6685727 * 2 ^ 59
def prefixEnd_6685727 : Nat := 4983230072969 + 3 ^ 40 * 6685727 * 2
def baseEnd_6685727 : Nat := 1144330491914089598688469

theorem tailTrace_6685727 : CollatzResearch.WordTrace tailWord_6685727 prefixEnd_6685727 1144330491914089598688469 := by
  unfold tailWord_6685727
  simp only [CollatzResearch.WordTrace]
  refine ⟨243848496649760385110879435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162565664433173590073919623 243848496649760385110879435)
  ·
    refine ⟨365772744974640577666319153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243848496649760385110879435 365772744974640577666319153)
    ·
      refine ⟨274329558730980433249739365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365772744974640577666319153 274329558730980433249739365)
      ·
        refine ⟨51436792262058831234326131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274329558730980433249739365 51436792262058831234326131)
        ·
          refine ⟨77155188393088246851489197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51436792262058831234326131 77155188393088246851489197)
          ·
            refine ⟨28933195647408092569308449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77155188393088246851489197 28933195647408092569308449)
            ·
              refine ⟨21699896735556069426981337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28933195647408092569308449 21699896735556069426981337)
              ·
                refine ⟨16274922551667052070236003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21699896735556069426981337 16274922551667052070236003)
                ·
                  refine ⟨24412383827500578105354005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16274922551667052070236003 24412383827500578105354005)
                  ·
                    refine ⟨1144330491914089598688469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24412383827500578105354005 1144330491914089598688469)
                    ·
                      rfl

theorem cell23_6685727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_6685727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685727 prefixEnd_6685727 := by exact prefixLift 6685727
  have htrace : WordTrace (prefixWord ++ tailWord_6685727) baseStart_6685727 baseEnd_6685727 := by
    simpa [prefixWord, tailWord_6685727, baseEnd_6685727] using wordTrace_append hprefix tailTrace_6685727
  have hstable : (prefixWord ++ tailWord_6685727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685727).length < 2 ^ (prefixWord ++ tailWord_6685727).sum := by decide
  have hdescent : baseEnd_6685727 < baseStart_6685727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685731 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 1, 5]
def baseStart_6685731 : Nat := 118140960795 + 6685731 * 2 ^ 59
def prefixEnd_6685731 : Nat := 4983230072969 + 3 ^ 40 * 6685731 * 2
def baseEnd_6685731 : Nat := 1144331176554962260138463

theorem tailTrace_6685731 : CollatzResearch.WordTrace tailWord_6685731 prefixEnd_6685731 1144331176554962260138463 := by
  unfold tailWord_6685731
  simp only [CollatzResearch.WordTrace]
  refine ⟨243848642541745893794025047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162565761694497262529350031 243848642541745893794025047)
  ·
    refine ⟨365772963812618840691037571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243848642541745893794025047 365772963812618840691037571)
    ·
      refine ⟨548659445718928261036556357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365772963812618840691037571 548659445718928261036556357)
      ·
        refine ⟨102873646072299048944354317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 548659445718928261036556357 102873646072299048944354317)
        ·
          refine ⟨38577617277112143354132869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102873646072299048944354317 38577617277112143354132869)
          ·
            refine ⟨7233303239458526878899913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38577617277112143354132869 7233303239458526878899913)
            ·
              refine ⟨5424977429593895159174935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7233303239458526878899913 5424977429593895159174935)
              ·
                refine ⟨8137466144390842738762403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5424977429593895159174935 8137466144390842738762403)
                ·
                  refine ⟨12206199216586264108143605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8137466144390842738762403 12206199216586264108143605)
                  ·
                    refine ⟨1144331176554962260138463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12206199216586264108143605 1144331176554962260138463)
                    ·
                      rfl

theorem cell23_6685731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 5].length) (baseStart_6685731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685731 prefixEnd_6685731 := by exact prefixLift 6685731
  have htrace : WordTrace (prefixWord ++ tailWord_6685731) baseStart_6685731 baseEnd_6685731 := by
    simpa [prefixWord, tailWord_6685731, baseEnd_6685731] using wordTrace_append hprefix tailTrace_6685731
  have hstable : (prefixWord ++ tailWord_6685731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685731).length < 2 ^ (prefixWord ++ tailWord_6685731).sum := by decide
  have hdescent : baseEnd_6685731 < baseStart_6685731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685740 : List Nat := [2, 2, 1, 1, 1, 2, 14]
def baseStart_6685740 : Nat := 118140960795 + 6685740 * 2 ^ 59
def prefixEnd_6685740 : Nat := 4983230072969 + 3 ^ 40 * 6685740 * 2
def baseEnd_6685740 : Nat := 42382693222108361051887

theorem tailTrace_6685740 : CollatzResearch.WordTrace tailWord_6685740 prefixEnd_6685740 42382693222108361051887 := by
  unfold tailWord_6685740
  simp only [CollatzResearch.WordTrace]
  refine ⟨121924485399356644165551337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162565980532475525554068449 121924485399356644165551337)
  ·
    refine ⟨91443364049517483124163503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121924485399356644165551337 91443364049517483124163503)
    ·
      refine ⟨137165046074276224686245255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91443364049517483124163503 137165046074276224686245255)
      ·
        refine ⟨205747569111414337029367883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137165046074276224686245255 205747569111414337029367883)
        ·
          refine ⟨308621353667121505544051825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205747569111414337029367883 308621353667121505544051825)
          ·
            refine ⟨231466015250341129158038869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308621353667121505544051825 231466015250341129158038869)
            ·
              refine ⟨42382693222108361051887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 231466015250341129158038869 42382693222108361051887)
              ·
                rfl

theorem cell23_6685740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 14].length) (baseStart_6685740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685740 prefixEnd_6685740 := by exact prefixLift 6685740
  have htrace : WordTrace (prefixWord ++ tailWord_6685740) baseStart_6685740 baseEnd_6685740 := by
    simpa [prefixWord, tailWord_6685740, baseEnd_6685740] using wordTrace_append hprefix tailTrace_6685740
  have hstable : (prefixWord ++ tailWord_6685740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685740).length < 2 ^ (prefixWord ++ tailWord_6685740).sum := by decide
  have hdescent : baseEnd_6685740 < baseStart_6685740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685761 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 1, 6]
def baseStart_6685761 : Nat := 118140960795 + 6685761 * 2 ^ 59
def prefixEnd_6685761 : Nat := 4983230072969 + 3 ^ 40 * 6685761 * 2
def baseEnd_6685761 : Nat := 1144336311361507221013417

theorem tailTrace_6685761 : CollatzResearch.WordTrace tailWord_6685761 prefixEnd_6685761 1144336311361507221013417 := by
  unfold tailWord_6685761
  simp only [CollatzResearch.WordTrace]
  refine ⟨243849736731637208917617137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162566491154424805945078091 243849736731637208917617137)
  ·
    refine ⟨182887302548727906688212853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243849736731637208917617137 182887302548727906688212853)
    ·
      refine ⟨17145684613943241252019955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182887302548727906688212853 17145684613943241252019955)
      ·
        refine ⟨25718526920914861878029933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17145684613943241252019955 25718526920914861878029933)
        ·
          refine ⟨9644447595343073204261225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25718526920914861878029933 9644447595343073204261225)
          ·
            refine ⟨7233335696507304903195919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9644447595343073204261225 7233335696507304903195919)
            ·
              refine ⟨10850003544760957354793879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7233335696507304903195919 10850003544760957354793879)
              ·
                refine ⟨16275005317141436032190819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10850003544760957354793879 16275005317141436032190819)
                ·
                  refine ⟨24412507975712154048286229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16275005317141436032190819 24412507975712154048286229)
                  ·
                    refine ⟨1144336311361507221013417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24412507975712154048286229 1144336311361507221013417)
                    ·
                      rfl

theorem cell23_6685761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_6685761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685761 prefixEnd_6685761 := by exact prefixLift 6685761
  have htrace : WordTrace (prefixWord ++ tailWord_6685761) baseStart_6685761 baseEnd_6685761 := by
    simpa [prefixWord, tailWord_6685761, baseEnd_6685761] using wordTrace_append hprefix tailTrace_6685761
  have hstable : (prefixWord ++ tailWord_6685761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685761).length < 2 ^ (prefixWord ++ tailWord_6685761).sum := by decide
  have hdescent : baseEnd_6685761 < baseStart_6685761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685784 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 6, 1, 3]
def baseStart_6685784 : Nat := 118140960795 + 6685784 * 2 ^ 59
def prefixEnd_6685784 : Nat := 4983230072969 + 3 ^ 40 * 6685784 * 2
def baseEnd_6685784 : Nat := 3433020744139575073052645

theorem tailTrace_6685784 : CollatzResearch.WordTrace tailWord_6685784 prefixEnd_6685784 3433020744139575073052645 := by
  unfold tailWord_6685784
  simp only [CollatzResearch.WordTrace]
  refine ⟨121925287805276941922852203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162567050407035922563802937 121925287805276941922852203)
  ·
    refine ⟨182887931707915412884278305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121925287805276941922852203 182887931707915412884278305)
    ·
      refine ⟨137165948780936559663208729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182887931707915412884278305 137165948780936559663208729)
      ·
        refine ⟨102874461585702419747406547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137165948780936559663208729 102874461585702419747406547)
        ·
          refine ⟨154311692378553629621109821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102874461585702419747406547 154311692378553629621109821)
          ·
            refine ⟨57866884641957611107916183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154311692378553629621109821 57866884641957611107916183)
            ·
              refine ⟨86800326962936416661874275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57866884641957611107916183 86800326962936416661874275)
              ·
                refine ⟨130200490444404624992811413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86800326962936416661874275 130200490444404624992811413)
                ·
                  refine ⟨6103147989581466796538035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130200490444404624992811413 6103147989581466796538035)
                  ·
                    refine ⟨9154721984372200194807053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6103147989581466796538035 9154721984372200194807053)
                    ·
                      refine ⟨3433020744139575073052645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9154721984372200194807053 3433020744139575073052645)
                      ·
                        rfl

theorem cell23_6685784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_6685784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685784 prefixEnd_6685784 := by exact prefixLift 6685784
  have htrace : WordTrace (prefixWord ++ tailWord_6685784) baseStart_6685784 baseEnd_6685784 := by
    simpa [prefixWord, tailWord_6685784, baseEnd_6685784] using wordTrace_append hprefix tailTrace_6685784
  have hstable : (prefixWord ++ tailWord_6685784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685784).length < 2 ^ (prefixWord ++ tailWord_6685784).sum := by decide
  have hdescent : baseEnd_6685784 < baseStart_6685784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685797 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_6685797 : Nat := 118140960795 + 6685797 * 2 ^ 59
def prefixEnd_6685797 : Nat := 4983230072969 + 3 ^ 40 * 6685797 * 2
def baseEnd_6685797 : Nat := 3433027419388083522190085

theorem tailTrace_6685797 : CollatzResearch.WordTrace tailWord_6685797 prefixEnd_6685797 3433027419388083522190085 := by
  unfold tailWord_6685797
  simp only [CollatzResearch.WordTrace]
  refine ⟨243851049759506787065927645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162567366506337858043951763 243851049759506787065927645)
  ·
    refine ⟨91444143659815045149722867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243851049759506787065927645 91444143659815045149722867)
    ·
      refine ⟨137166215489722567724584301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91444143659815045149722867 137166215489722567724584301)
      ·
        refine ⟨51437330808645962896719113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137166215489722567724584301 51437330808645962896719113)
        ·
          refine ⟨38577998106484472172539335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51437330808645962896719113 38577998106484472172539335)
          ·
            refine ⟨57866997159726708258809003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38577998106484472172539335 57866997159726708258809003)
            ·
              refine ⟨86800495739590062388213505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57866997159726708258809003 86800495739590062388213505)
              ·
                refine ⟨65100371804692546791160129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86800495739590062388213505 65100371804692546791160129)
                ·
                  refine ⟨48825278853519410093370097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65100371804692546791160129 48825278853519410093370097)
                  ·
                    refine ⟨36618959140139557570027573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48825278853519410093370097 36618959140139557570027573)
                    ·
                      refine ⟨3433027419388083522190085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36618959140139557570027573 3433027419388083522190085)
                      ·
                        rfl

theorem cell23_6685797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_6685797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685797 prefixEnd_6685797 := by exact prefixLift 6685797
  have htrace : WordTrace (prefixWord ++ tailWord_6685797) baseStart_6685797 baseEnd_6685797 := by
    simpa [prefixWord, tailWord_6685797, baseEnd_6685797] using wordTrace_append hprefix tailTrace_6685797
  have hstable : (prefixWord ++ tailWord_6685797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685797).length < 2 ^ (prefixWord ++ tailWord_6685797).sum := by decide
  have hdescent : baseEnd_6685797 < baseStart_6685797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685802 : List Nat := [3, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_6685802 : Nat := 118140960795 + 6685802 * 2 ^ 59
def prefixEnd_6685802 : Nat := 4983230072969 + 3 ^ 40 * 6685802 * 2
def baseEnd_6685802 : Nat := 3433029986791356002627563

theorem tailTrace_6685802 : CollatzResearch.WordTrace tailWord_6685802 prefixEnd_6685802 3433029986791356002627563 := by
  unfold tailWord_6685802
  simp only [CollatzResearch.WordTrace]
  refine ⟨60962808031122168229964915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162567488082992448613239773 60962808031122168229964915)
  ·
    refine ⟨91444212046683252344947373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60962808031122168229964915 91444212046683252344947373)
    ·
      refine ⟨34291579517506219629355265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91444212046683252344947373 34291579517506219629355265)
      ·
        refine ⟨25718684638129664722016449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34291579517506219629355265 25718684638129664722016449)
        ·
          refine ⟨19289013478597248541512337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25718684638129664722016449 19289013478597248541512337)
          ·
            refine ⟨14466760108947936406134253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19289013478597248541512337 14466760108947936406134253)
            ·
              refine ⟨5425035040855476152300345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14466760108947936406134253 5425035040855476152300345)
              ·
                refine ⟨4068776280641607114225259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5425035040855476152300345 4068776280641607114225259)
                ·
                  refine ⟨6103164420962410671337889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068776280641607114225259 6103164420962410671337889)
                  ·
                    refine ⟨4577373315721808003503417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6103164420962410671337889 4577373315721808003503417)
                    ·
                      refine ⟨3433029986791356002627563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577373315721808003503417 3433029986791356002627563)
                      ·
                        rfl

theorem cell23_6685802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_6685802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685802 prefixEnd_6685802 := by exact prefixLift 6685802
  have htrace : WordTrace (prefixWord ++ tailWord_6685802) baseStart_6685802 baseEnd_6685802 := by
    simpa [prefixWord, tailWord_6685802, baseEnd_6685802] using wordTrace_append hprefix tailTrace_6685802
  have hstable : (prefixWord ++ tailWord_6685802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685802).length < 2 ^ (prefixWord ++ tailWord_6685802).sum := by decide
  have hdescent : baseEnd_6685802 < baseStart_6685802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685807 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 4]
def baseStart_6685807 : Nat := 118140960795 + 6685807 * 2 ^ 59
def prefixEnd_6685807 : Nat := 4983230072969 + 3 ^ 40 * 6685807 * 2
def baseEnd_6685807 : Nat := 3433032554194628483065039

theorem tailTrace_6685807 : CollatzResearch.WordTrace tailWord_6685807 prefixEnd_6685807 3433032554194628483065039 := by
  unfold tailWord_6685807
  simp only [CollatzResearch.WordTrace]
  refine ⟨243851414489470558773791675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162567609659647039182527783 243851414489470558773791675)
  ·
    refine ⟨365777121734205838160687513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243851414489470558773791675 365777121734205838160687513)
    ·
      refine ⟨274332841300654378620515635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365777121734205838160687513 274332841300654378620515635)
      ·
        refine ⟨411499261950981567930773453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274332841300654378620515635 411499261950981567930773453)
        ·
          refine ⟨154312223231618087974040045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411499261950981567930773453 154312223231618087974040045)
          ·
            refine ⟨57867083711856782990265017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154312223231618087974040045 57867083711856782990265017)
            ·
              refine ⟨43400312783892587242698763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57867083711856782990265017 43400312783892587242698763)
              ·
                refine ⟨65100469175838880864048145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43400312783892587242698763 65100469175838880864048145)
                ·
                  refine ⟨48825351881879160648036109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65100469175838880864048145 48825351881879160648036109)
                  ·
                    refine ⟨18309506955704685243013541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48825351881879160648036109 18309506955704685243013541)
                    ·
                      refine ⟨3433032554194628483065039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18309506955704685243013541 3433032554194628483065039)
                      ·
                        rfl

theorem cell23_6685807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_6685807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685807 prefixEnd_6685807 := by exact prefixLift 6685807
  have htrace : WordTrace (prefixWord ++ tailWord_6685807) baseStart_6685807 baseEnd_6685807 := by
    simpa [prefixWord, tailWord_6685807, baseEnd_6685807] using wordTrace_append hprefix tailTrace_6685807
  have hstable : (prefixWord ++ tailWord_6685807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685807).length < 2 ^ (prefixWord ++ tailWord_6685807).sum := by decide
  have hdescent : baseEnd_6685807 < baseStart_6685807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685827 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 5]
def baseStart_6685827 : Nat := 118140960795 + 6685827 * 2 ^ 59
def prefixEnd_6685827 : Nat := 4983230072969 + 3 ^ 40 * 6685827 * 2
def baseEnd_6685827 : Nat := 3433042823807718404814947

theorem tailTrace_6685827 : CollatzResearch.WordTrace tailWord_6685827 prefixEnd_6685827 3433042823807718404814947 := by
  unfold tailWord_6685827
  simp only [CollatzResearch.WordTrace]
  refine ⟨243852143949398102189519735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162568095966265401459679823 243852143949398102189519735)
  ·
    refine ⟨365778215924097153284279603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243852143949398102189519735 365778215924097153284279603)
    ·
      refine ⟨548667323886145729926419405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365778215924097153284279603 548667323886145729926419405)
      ·
        refine ⟨205750246457304648722407277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548667323886145729926419405 205750246457304648722407277)
        ·
          refine ⟨77156342421489243270902729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205750246457304648722407277 77156342421489243270902729)
          ·
            refine ⟨57867256816116932453177047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77156342421489243270902729 57867256816116932453177047)
            ·
              refine ⟨86800885224175398679765571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57867256816116932453177047 86800885224175398679765571)
              ·
                refine ⟨130201327836263098019648357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86800885224175398679765571 130201327836263098019648357)
                ·
                  refine ⟨24412748969299330878684067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130201327836263098019648357 24412748969299330878684067)
                  ·
                    refine ⟨36619123453948996318026101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24412748969299330878684067 36619123453948996318026101)
                    ·
                      refine ⟨3433042823807718404814947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36619123453948996318026101 3433042823807718404814947)
                      ·
                        rfl

theorem cell23_6685827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_6685827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685827 prefixEnd_6685827 := by exact prefixLift 6685827
  have htrace : WordTrace (prefixWord ++ tailWord_6685827) baseStart_6685827 baseEnd_6685827 := by
    simpa [prefixWord, tailWord_6685827, baseEnd_6685827] using wordTrace_append hprefix tailTrace_6685827
  have hstable : (prefixWord ++ tailWord_6685827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685827).length < 2 ^ (prefixWord ++ tailWord_6685827).sum := by decide
  have hdescent : baseEnd_6685827 < baseStart_6685827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685828 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_6685828 : Nat := 118140960795 + 6685828 * 2 ^ 59
def prefixEnd_6685828 : Nat := 4983230072969 + 3 ^ 40 * 6685828 * 2
def baseEnd_6685828 : Nat := 3433043337288372900902443

theorem tailTrace_6685828 : CollatzResearch.WordTrace tailWord_6685828 prefixEnd_6685828 3433043337288372900902443 := by
  unfold tailWord_6685828
  simp only [CollatzResearch.WordTrace]
  refine ⟨121926090211197239680153069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162568120281596319573537425 121926090211197239680153069)
  ·
    refine ⟨45722283829198964880057401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121926090211197239680153069 45722283829198964880057401)
    ·
      refine ⟨34291712871899223660043051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45722283829198964880057401 34291712871899223660043051)
      ·
        refine ⟨51437569307848835490064577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34291712871899223660043051 51437569307848835490064577)
        ·
          refine ⟨38578176980886626617548433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51437569307848835490064577 38578176980886626617548433)
          ·
            refine ⟨28933632735664969963161325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38578176980886626617548433 28933632735664969963161325)
            ·
              refine ⟨10850112275874363736185497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28933632735664969963161325 10850112275874363736185497)
              ·
                refine ⟨8137584206905772802139123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10850112275874363736185497 8137584206905772802139123)
                ·
                  refine ⟨12206376310358659203208685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8137584206905772802139123 12206376310358659203208685)
                  ·
                    refine ⟨4577391116384497201203257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12206376310358659203208685 4577391116384497201203257)
                    ·
                      refine ⟨3433043337288372900902443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577391116384497201203257 3433043337288372900902443)
                      ·
                        rfl

theorem cell23_6685828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_6685828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685828 prefixEnd_6685828 := by exact prefixLift 6685828
  have htrace : WordTrace (prefixWord ++ tailWord_6685828) baseStart_6685828 baseEnd_6685828 := by
    simpa [prefixWord, tailWord_6685828, baseEnd_6685828] using wordTrace_append hprefix tailTrace_6685828
  have hstable : (prefixWord ++ tailWord_6685828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685828).length < 2 ^ (prefixWord ++ tailWord_6685828).sum := by decide
  have hdescent : baseEnd_6685828 < baseStart_6685828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685874 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_6685874 : Nat := 118140960795 + 6685874 * 2 ^ 59
def prefixEnd_6685874 : Nat := 4983230072969 + 3 ^ 40 * 6685874 * 2
def baseEnd_6685874 : Nat := 3433066957398479720927231

theorem tailTrace_6685874 : CollatzResearch.WordTrace tailWord_6685874 prefixEnd_6685874 3433066957398479720927231 := by
  unfold tailWord_6685874
  simp only [CollatzResearch.WordTrace]
  refine ⟨60963464545056957304120169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162569238786818552810987117 60963464545056957304120169)
  ·
    refine ⟨45722598408792717978090127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60963464545056957304120169 45722598408792717978090127)
    ·
      refine ⟨68583897613189076967135191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45722598408792717978090127 68583897613189076967135191)
      ·
        refine ⟨102875846419783615450702787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68583897613189076967135191 102875846419783615450702787)
        ·
          refine ⟨154313769629675423176054181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102875846419783615450702787 154313769629675423176054181)
          ·
            refine ⟨28933831805564141845510159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154313769629675423176054181 28933831805564141845510159)
            ·
              refine ⟨43400747708346212768265239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28933831805564141845510159 43400747708346212768265239)
              ·
                refine ⟨65101121562519319152397859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43400747708346212768265239 65101121562519319152397859)
                ·
                  refine ⟨97651682343778978728596789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65101121562519319152397859 97651682343778978728596789)
                  ·
                    refine ⟨9154845219729279255805949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97651682343778978728596789 9154845219729279255805949)
                    ·
                      refine ⟨3433066957398479720927231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9154845219729279255805949 3433066957398479720927231)
                      ·
                        rfl

theorem cell23_6685874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_6685874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685874 prefixEnd_6685874 := by exact prefixLift 6685874
  have htrace : WordTrace (prefixWord ++ tailWord_6685874) baseStart_6685874 baseEnd_6685874 := by
    simpa [prefixWord, tailWord_6685874, baseEnd_6685874] using wordTrace_append hprefix tailTrace_6685874
  have hstable : (prefixWord ++ tailWord_6685874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685874).length < 2 ^ (prefixWord ++ tailWord_6685874).sum := by decide
  have hdescent : baseEnd_6685874 < baseStart_6685874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685887 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_6685887 : Nat := 118140960795 + 6685887 * 2 ^ 59
def prefixEnd_6685887 : Nat := 4983230072969 + 3 ^ 40 * 6685887 * 2
def baseEnd_6685887 : Nat := 3433073632646988170064671

theorem tailTrace_6685887 : CollatzResearch.WordTrace tailWord_6685887 prefixEnd_6685887 3433073632646988170064671 := by
  unfold tailWord_6685887
  simp only [CollatzResearch.WordTrace]
  refine ⟨243854332329180732436703915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162569554886120488291135943 243854332329180732436703915)
  ·
    refine ⟨365781498493771098655055873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243854332329180732436703915 365781498493771098655055873)
    ·
      refine ⟨274336123870328323991291905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365781498493771098655055873 274336123870328323991291905)
      ·
        refine ⟨205752092902746242993468929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274336123870328323991291905 205752092902746242993468929)
        ·
          refine ⟨154314069677059682245101697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205752092902746242993468929 154314069677059682245101697)
          ·
            refine ⟨115735552257794761683826273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154314069677059682245101697 115735552257794761683826273)
            ·
              refine ⟨86801664193346071262869705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115735552257794761683826273 86801664193346071262869705)
              ·
                refine ⟨65101248145009553447152279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86801664193346071262869705 65101248145009553447152279)
                ·
                  refine ⟨97651872217514330170728419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65101248145009553447152279 97651872217514330170728419)
                  ·
                    refine ⟨146477808326271495256092629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97651872217514330170728419 146477808326271495256092629)
                    ·
                      refine ⟨3433073632646988170064671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146477808326271495256092629 3433073632646988170064671)
                      ·
                        rfl

theorem cell23_6685887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_6685887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685887 prefixEnd_6685887 := by exact prefixLift 6685887
  have htrace : WordTrace (prefixWord ++ tailWord_6685887) baseStart_6685887 baseEnd_6685887 := by
    simpa [prefixWord, tailWord_6685887, baseEnd_6685887] using wordTrace_append hprefix tailTrace_6685887
  have hstable : (prefixWord ++ tailWord_6685887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685887).length < 2 ^ (prefixWord ++ tailWord_6685887).sum := by decide
  have hdescent : baseEnd_6685887 < baseStart_6685887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685914 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_6685914 : Nat := 118140960795 + 6685914 * 2 ^ 59
def prefixEnd_6685914 : Nat := 4983230072969 + 3 ^ 40 * 6685914 * 2
def baseEnd_6685914 : Nat := 3433087496624659564427047

theorem tailTrace_6685914 : CollatzResearch.WordTrace tailWord_6685914 prefixEnd_6685914 3433087496624659564427047 := by
  unfold tailWord_6685914
  simp only [CollatzResearch.WordTrace]
  refine ⟨60963829275020729011984199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162570211400055277365291197 60963829275020729011984199)
  ·
    refine ⟨91445743912531093517976299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60963829275020729011984199 91445743912531093517976299)
    ·
      refine ⟨137168615868796640276964449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91445743912531093517976299 137168615868796640276964449)
      ·
        refine ⟨102876461901597480207723337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137168615868796640276964449 102876461901597480207723337)
        ·
          refine ⟨77157346426198110155792503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102876461901597480207723337 77157346426198110155792503)
          ·
            refine ⟨115736019639297165233688755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77157346426198110155792503 115736019639297165233688755)
            ·
              refine ⟨173604029458945747850533133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115736019639297165233688755 173604029458945747850533133)
              ·
                refine ⟨65101511047104655443949925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173604029458945747850533133 65101511047104655443949925)
                ·
                  refine ⟨12206533321332122895740611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65101511047104655443949925 12206533321332122895740611)
                  ·
                    refine ⟨18309799981998184343610917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12206533321332122895740611 18309799981998184343610917)
                    ·
                      refine ⟨3433087496624659564427047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18309799981998184343610917 3433087496624659564427047)
                      ·
                        rfl

theorem cell23_6685914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_6685914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685914 prefixEnd_6685914 := by exact prefixLift 6685914
  have htrace : WordTrace (prefixWord ++ tailWord_6685914) baseStart_6685914 baseEnd_6685914 := by
    simpa [prefixWord, tailWord_6685914, baseEnd_6685914] using wordTrace_append hprefix tailTrace_6685914
  have hstable : (prefixWord ++ tailWord_6685914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685914).length < 2 ^ (prefixWord ++ tailWord_6685914).sum := by decide
  have hdescent : baseEnd_6685914 < baseStart_6685914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685931 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 2, 4, 2]
def baseStart_6685931 : Nat := 118140960795 + 6685931 * 2 ^ 59
def prefixEnd_6685931 : Nat := 4983230072969 + 3 ^ 40 * 6685931 * 2
def baseEnd_6685931 : Nat := 3433096225795785997914469

theorem tailTrace_6685931 : CollatzResearch.WordTrace tailWord_6685931 prefixEnd_6685931 3433096225795785997914469 := by
  unfold tailWord_6685931
  simp only [CollatzResearch.WordTrace]
  refine ⟨243855937141021327951305647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162570624760680885300870431 243855937141021327951305647)
  ·
    refine ⟨365783905711531991926958471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243855937141021327951305647 365783905711531991926958471)
    ·
      refine ⟨548675858567297987890437707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365783905711531991926958471 548675858567297987890437707)
      ·
        refine ⟨823013787850946981835656561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548675858567297987890437707 823013787850946981835656561)
        ·
          refine ⟨617260340888210236376742421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823013787850946981835656561 617260340888210236376742421)
          ·
            refine ⟨28934078479134854830159801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 617260340888210236376742421 28934078479134854830159801)
            ·
              refine ⟨21700558859351141122619851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28934078479134854830159801 21700558859351141122619851)
              ·
                refine ⟨32550838289026711683929777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21700558859351141122619851 32550838289026711683929777)
                ·
                  refine ⟨24413128716770033762947333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32550838289026711683929777 24413128716770033762947333)
                  ·
                    refine ⟨4577461634394381330552625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24413128716770033762947333 4577461634394381330552625)
                    ·
                      refine ⟨3433096225795785997914469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577461634394381330552625 3433096225795785997914469)
                      ·
                        rfl

theorem cell23_6685931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 4, 2].length) (baseStart_6685931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685931 prefixEnd_6685931 := by exact prefixLift 6685931
  have htrace : WordTrace (prefixWord ++ tailWord_6685931) baseStart_6685931 baseEnd_6685931 := by
    simpa [prefixWord, tailWord_6685931, baseEnd_6685931] using wordTrace_append hprefix tailTrace_6685931
  have hstable : (prefixWord ++ tailWord_6685931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685931).length < 2 ^ (prefixWord ++ tailWord_6685931).sum := by decide
  have hdescent : baseEnd_6685931 < baseStart_6685931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685947 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 9]
def baseStart_6685947 : Nat := 118140960795 + 6685947 * 2 ^ 59
def prefixEnd_6685947 : Nat := 4983230072969 + 3 ^ 40 * 6685947 * 2
def baseEnd_6685947 : Nat := 3433104441486257935314395

theorem tailTrace_6685947 : CollatzResearch.WordTrace tailWord_6685947 prefixEnd_6685947 3433104441486257935314395 := by
  unfold tailWord_6685947
  simp only [CollatzResearch.WordTrace]
  refine ⟨243856520708963362683888095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162571013805975575122592063 243856520708963362683888095)
  ·
    refine ⟨365784781063445044025832143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243856520708963362683888095 365784781063445044025832143)
    ·
      refine ⟨548677171595167566038748215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365784781063445044025832143 548677171595167566038748215)
      ·
        refine ⟨823015757392751349058122323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548677171595167566038748215 823015757392751349058122323)
        ·
          refine ⟨1234523636089127023587183485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823015757392751349058122323 1234523636089127023587183485)
          ·
            refine ⟨462946363533422633845193807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1234523636089127023587183485 462946363533422633845193807)
            ·
              refine ⟨694419545300133950767790711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462946363533422633845193807 694419545300133950767790711)
              ·
                refine ⟨1041629317950200926151686067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694419545300133950767790711 1041629317950200926151686067)
                ·
                  refine ⟨1562443976925301389227529101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041629317950200926151686067 1562443976925301389227529101)
                  ·
                    refine ⟨585916491346988020960323413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562443976925301389227529101 585916491346988020960323413)
                    ·
                      refine ⟨3433104441486257935314395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 585916491346988020960323413 3433104441486257935314395)
                      ·
                        rfl

theorem cell23_6685947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_6685947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685947 prefixEnd_6685947 := by exact prefixLift 6685947
  have htrace : WordTrace (prefixWord ++ tailWord_6685947) baseStart_6685947 baseEnd_6685947 := by
    simpa [prefixWord, tailWord_6685947, baseEnd_6685947] using wordTrace_append hprefix tailTrace_6685947
  have hstable : (prefixWord ++ tailWord_6685947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685947).length < 2 ^ (prefixWord ++ tailWord_6685947).sum := by decide
  have hdescent : baseEnd_6685947 < baseStart_6685947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685975 : List Nat := [1, 1, 3, 4, 1, 1, 5, 2, 1, 4]
def baseStart_6685975 : Nat := 118140960795 + 6685975 * 2 ^ 59
def prefixEnd_6685975 : Nat := 4983230072969 + 3 ^ 40 * 6685975 * 2
def baseEnd_6685975 : Nat := 1144372939648194608588089

theorem tailTrace_6685975 : CollatzResearch.WordTrace tailWord_6685975 prefixEnd_6685975 1144372939648194608588089 := by
  unfold tailWord_6685975
  simp only [CollatzResearch.WordTrace]
  refine ⟨243857541952861923465907379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162571694635241282310604919 243857541952861923465907379)
  ·
    refine ⟨365786312929292885198861069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243857541952861923465907379 365786312929292885198861069)
    ·
      refine ⟨137169867348484831949572901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365786312929292885198861069 137169867348484831949572901)
      ·
        refine ⟨25719350127840905990544919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137169867348484831949572901 25719350127840905990544919)
        ·
          refine ⟨38579025191761358985817379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25719350127840905990544919 38579025191761358985817379)
          ·
            refine ⟨57868537787642038478726069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38579025191761358985817379 57868537787642038478726069)
            ·
              refine ⟨5425175417591441107380569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57868537787642038478726069 5425175417591441107380569)
              ·
                refine ⟨4068881563193580830535427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5425175417591441107380569 4068881563193580830535427)
                ·
                  refine ⟨6103322344790371245803141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068881563193580830535427 6103322344790371245803141)
                  ·
                    refine ⟨1144372939648194608588089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6103322344790371245803141 1144372939648194608588089)
                    ·
                      rfl

theorem cell23_6685975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_6685975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6685975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6685975 prefixEnd_6685975 := by exact prefixLift 6685975
  have htrace : WordTrace (prefixWord ++ tailWord_6685975) baseStart_6685975 baseEnd_6685975 := by
    simpa [prefixWord, tailWord_6685975, baseEnd_6685975] using wordTrace_append hprefix tailTrace_6685975
  have hstable : (prefixWord ++ tailWord_6685975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685975).length < 2 ^ (prefixWord ++ tailWord_6685975).sum := by decide
  have hdescent : baseEnd_6685975 < baseStart_6685975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686001 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 3, 5]
def baseStart_6686001 : Nat := 118140960795 + 6686001 * 2 ^ 59
def prefixEnd_6686001 : Nat := 4983230072969 + 3 ^ 40 * 6686001 * 2
def baseEnd_6686001 : Nat := 1144377389813866908013049

theorem tailTrace_6686001 : CollatzResearch.WordTrace tailWord_6686001 prefixEnd_6686001 1144377389813866908013049 := by
  unfold tailWord_6686001
  simp only [CollatzResearch.WordTrace]
  refine ⟨243858490250767729906353857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162572326833845153270902571 243858490250767729906353857)
  ·
    refine ⟨182893867688075797429765393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243858490250767729906353857 182893867688075797429765393)
    ·
      refine ⟨137170400766056848072324045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182893867688075797429765393 137170400766056848072324045)
      ·
        refine ⟨51438900287271318027121517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137170400766056848072324045 51438900287271318027121517)
        ·
          refine ⟨19289587607726744260170569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51438900287271318027121517 19289587607726744260170569)
          ·
            refine ⟨14467190705795058195127927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19289587607726744260170569 14467190705795058195127927)
            ·
              refine ⟨21700786058692587292691891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14467190705795058195127927 21700786058692587292691891)
              ·
                refine ⟨32551179088038880939037837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21700786058692587292691891 32551179088038880939037837)
                ·
                  refine ⟨12206692158014580352139189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32551179088038880939037837 12206692158014580352139189)
                  ·
                    refine ⟨1144377389813866908013049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12206692158014580352139189 1144377389813866908013049)
                    ·
                      rfl

theorem cell23_6686001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_6686001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686001 prefixEnd_6686001 := by exact prefixLift 6686001
  have htrace : WordTrace (prefixWord ++ tailWord_6686001) baseStart_6686001 baseEnd_6686001 := by
    simpa [prefixWord, tailWord_6686001, baseEnd_6686001] using wordTrace_append hprefix tailTrace_6686001
  have hstable : (prefixWord ++ tailWord_6686001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686001).length < 2 ^ (prefixWord ++ tailWord_6686001).sum := by decide
  have hdescent : baseEnd_6686001 < baseStart_6686001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686021 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 4]
def baseStart_6686021 : Nat := 118140960795 + 6686021 * 2 ^ 59
def prefixEnd_6686021 : Nat := 4983230072969 + 3 ^ 40 * 6686021 * 2
def baseEnd_6686021 : Nat := 3433142439054690645789055

theorem tailTrace_6686021 : CollatzResearch.WordTrace tailWord_6686021 prefixEnd_6686021 3433142439054690645789055 := by
  unfold tailWord_6686021
  simp only [CollatzResearch.WordTrace]
  refine ⟨243859219710695273322081917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162572813140463515548054611 243859219710695273322081917)
  ·
    refine ⟨91447207391510727495780719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243859219710695273322081917 91447207391510727495780719)
    ·
      refine ⟨137170811087266091243671079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91447207391510727495780719 137170811087266091243671079)
      ·
        refine ⟨205756216630899136865506619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137170811087266091243671079 205756216630899136865506619)
        ·
          refine ⟨308634324946348705298259929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205756216630899136865506619 308634324946348705298259929)
          ·
            refine ⟨231475743709761528973694947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308634324946348705298259929 231475743709761528973694947)
            ·
              refine ⟨347213615564642293460542421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231475743709761528973694947 347213615564642293460542421)
              ·
                refine ⟨8137819114796303752981463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 347213615564642293460542421 8137819114796303752981463)
                ·
                  refine ⟨12206728672194455629472195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8137819114796303752981463 12206728672194455629472195)
                  ·
                    refine ⟨18310093008291683444208293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12206728672194455629472195 18310093008291683444208293)
                    ·
                      refine ⟨3433142439054690645789055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18310093008291683444208293 3433142439054690645789055)
                      ·
                        rfl

theorem cell23_6686021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_6686021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686021 prefixEnd_6686021 := by exact prefixLift 6686021
  have htrace : WordTrace (prefixWord ++ tailWord_6686021) baseStart_6686021 baseEnd_6686021 := by
    simpa [prefixWord, tailWord_6686021, baseEnd_6686021] using wordTrace_append hprefix tailTrace_6686021
  have hstable : (prefixWord ++ tailWord_6686021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686021).length < 2 ^ (prefixWord ++ tailWord_6686021).sum := by decide
  have hdescent : baseEnd_6686021 < baseStart_6686021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686022 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_6686022 : Nat := 118140960795 + 6686022 * 2 ^ 59
def prefixEnd_6686022 : Nat := 4983230072969 + 3 ^ 40 * 6686022 * 2
def baseEnd_6686022 : Nat := 381460328059482793541839

theorem tailTrace_6686022 : CollatzResearch.WordTrace tailWord_6686022 prefixEnd_6686022 381460328059482793541839 := by
  unfold tailWord_6686022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7620601755740364077902135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162572837455794433661912213 7620601755740364077902135)
  ·
    refine ⟨11430902633610546116853203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7620601755740364077902135 11430902633610546116853203)
    ·
      refine ⟨17146353950415819175279805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11430902633610546116853203 17146353950415819175279805)
      ·
        refine ⟨6429882731405932190729927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17146353950415819175279805 6429882731405932190729927)
        ·
          refine ⟨9644824097108898286094891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6429882731405932190729927 9644824097108898286094891)
          ·
            refine ⟨14467236145663347429142337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9644824097108898286094891 14467236145663347429142337)
            ·
              refine ⟨10850427109247510571856753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14467236145663347429142337 10850427109247510571856753)
              ·
                refine ⟨8137820331935632928892565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10850427109247510571856753 8137820331935632928892565)
                ·
                  refine ⟨381460328059482793541839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8137820331935632928892565 381460328059482793541839)
                  ·
                    rfl

theorem cell23_6686022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_6686022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686022 prefixEnd_6686022 := by exact prefixLift 6686022
  have htrace : WordTrace (prefixWord ++ tailWord_6686022) baseStart_6686022 baseEnd_6686022 := by
    simpa [prefixWord, tailWord_6686022, baseEnd_6686022] using wordTrace_append hprefix tailTrace_6686022
  have hstable : (prefixWord ++ tailWord_6686022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686022).length < 2 ^ (prefixWord ++ tailWord_6686022).sum := by decide
  have hdescent : baseEnd_6686022 < baseStart_6686022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686041 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 3, 2, 3]
def baseStart_6686041 : Nat := 118140960795 + 6686041 * 2 ^ 59
def prefixEnd_6686041 : Nat := 4983230072969 + 3 ^ 40 * 6686041 * 2
def baseEnd_6686041 : Nat := 3433152708667780567538963

theorem tailTrace_6686041 : CollatzResearch.WordTrace tailWord_6686041 prefixEnd_6686041 3433152708667780567538963 := by
  unfold tailWord_6686041
  simp only [CollatzResearch.WordTrace]
  refine ⟨243859949170622816737809977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162573299447081877825206651 243859949170622816737809977)
  ·
    refine ⟨182894961877967112553357483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243859949170622816737809977 182894961877967112553357483)
    ·
      refine ⟨274342442816950668830036225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182894961877967112553357483 274342442816950668830036225)
      ·
        refine ⟨205756832112713001622527169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274342442816950668830036225 205756832112713001622527169)
        ·
          refine ⟨154317624084534751216895377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205756832112713001622527169 154317624084534751216895377)
          ·
            refine ⟨115738218063401063412671533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154317624084534751216895377 115738218063401063412671533)
            ·
              refine ⟨43401831773775398779751825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115738218063401063412671533 43401831773775398779751825)
              ·
                refine ⟨32551373830331549084813869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43401831773775398779751825 32551373830331549084813869)
                ·
                  refine ⟨12206765186374330906805201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32551373830331549084813869 12206765186374330906805201)
                  ·
                    refine ⟨9155073889780748180103901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12206765186374330906805201 9155073889780748180103901)
                    ·
                      refine ⟨3433152708667780567538963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9155073889780748180103901 3433152708667780567538963)
                      ·
                        rfl

theorem cell23_6686041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_6686041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686041 prefixEnd_6686041 := by exact prefixLift 6686041
  have htrace : WordTrace (prefixWord ++ tailWord_6686041) baseStart_6686041 baseEnd_6686041 := by
    simpa [prefixWord, tailWord_6686041, baseEnd_6686041] using wordTrace_append hprefix tailTrace_6686041
  have hstable : (prefixWord ++ tailWord_6686041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686041).length < 2 ^ (prefixWord ++ tailWord_6686041).sum := by decide
  have hdescent : baseEnd_6686041 < baseStart_6686041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686048 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 2, 4]
def baseStart_6686048 : Nat := 118140960795 + 6686048 * 2 ^ 59
def prefixEnd_6686048 : Nat := 4983230072969 + 3 ^ 40 * 6686048 * 2
def baseEnd_6686048 : Nat := 1144385434344120680050477

theorem tailTrace_6686048 : CollatzResearch.WordTrace tailWord_6686048 prefixEnd_6686048 1144385434344120680050477 := by
  unfold tailWord_6686048
  simp only [CollatzResearch.WordTrace]
  refine ⟨121930102240798728466657399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162573469654398304622209865 121930102240798728466657399)
  ·
    refine ⟨182895153361198092699986099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121930102240798728466657399 182895153361198092699986099)
    ·
      refine ⟨274342730041797139049979149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182895153361198092699986099 274342730041797139049979149)
      ·
        refine ⟨102878523765673927143742181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274342730041797139049979149 102878523765673927143742181)
        ·
          refine ⟨19289723206063861339451659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102878523765673927143742181 19289723206063861339451659)
          ·
            refine ⟨28934584809095792009177489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19289723206063861339451659 28934584809095792009177489)
            ·
              refine ⟨21700938606821844006883117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28934584809095792009177489 21700938606821844006883117)
              ·
                refine ⟨8137851977558191502581169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21700938606821844006883117 8137851977558191502581169)
                ·
                  refine ⟨6103388983168643626935877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8137851977558191502581169 6103388983168643626935877)
                  ·
                    refine ⟨1144385434344120680050477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6103388983168643626935877 1144385434344120680050477)
                    ·
                      rfl

theorem cell23_6686048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 2, 4].length) (baseStart_6686048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686048 prefixEnd_6686048 := by exact prefixLift 6686048
  have htrace : WordTrace (prefixWord ++ tailWord_6686048) baseStart_6686048 baseEnd_6686048 := by
    simpa [prefixWord, tailWord_6686048, baseEnd_6686048] using wordTrace_append hprefix tailTrace_6686048
  have hstable : (prefixWord ++ tailWord_6686048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686048).length < 2 ^ (prefixWord ++ tailWord_6686048).sum := by decide
  have hdescent : baseEnd_6686048 < baseStart_6686048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686051 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 4]
def baseStart_6686051 : Nat := 118140960795 + 6686051 * 2 ^ 59
def prefixEnd_6686051 : Nat := 4983230072969 + 3 ^ 40 * 6686051 * 2
def baseEnd_6686051 : Nat := 3433157843474325528413917

theorem tailTrace_6686051 : CollatzResearch.WordTrace tailWord_6686051 prefixEnd_6686051 3433157843474325528413917 := by
  unfold tailWord_6686051
  simp only [CollatzResearch.WordTrace]
  refine ⟨243860313900586588445674007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162573542600391058963782671 243860313900586588445674007)
  ·
    refine ⟨365790470850879882668511011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243860313900586588445674007 365790470850879882668511011)
    ·
      refine ⟨548685706276319824002766517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365790470850879882668511011 548685706276319824002766517)
      ·
        refine ⟨51439284963404983500259361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 548685706276319824002766517 51439284963404983500259361)
        ·
          refine ⟨38579463722553737625194521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51439284963404983500259361 38579463722553737625194521)
          ·
            refine ⟨28934597791915303218895891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38579463722553737625194521 28934597791915303218895891)
            ·
              refine ⟨43401896687872954828343837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28934597791915303218895891 43401896687872954828343837)
              ·
                refine ⟨16275711257952358060628939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43401896687872954828343837 16275711257952358060628939)
                ·
                  refine ⟨24413566886928537090943409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16275711257952358060628939 24413566886928537090943409)
                  ·
                    refine ⟨18310175165196402818207557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24413566886928537090943409 18310175165196402818207557)
                    ·
                      refine ⟨3433157843474325528413917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18310175165196402818207557 3433157843474325528413917)
                      ·
                        rfl

theorem cell23_6686051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_6686051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686051 prefixEnd_6686051 := by exact prefixLift 6686051
  have htrace : WordTrace (prefixWord ++ tailWord_6686051) baseStart_6686051 baseEnd_6686051 := by
    simpa [prefixWord, tailWord_6686051, baseEnd_6686051] using wordTrace_append hprefix tailTrace_6686051
  have hstable : (prefixWord ++ tailWord_6686051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686051).length < 2 ^ (prefixWord ++ tailWord_6686051).sum := by decide
  have hdescent : baseEnd_6686051 < baseStart_6686051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686071 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 3]
def baseStart_6686071 : Nat := 118140960795 + 6686071 * 2 ^ 59
def prefixEnd_6686071 : Nat := 4983230072969 + 3 ^ 40 * 6686071 * 2
def baseEnd_6686071 : Nat := 3433168113087415450163825

theorem tailTrace_6686071 : CollatzResearch.WordTrace tailWord_6686071 prefixEnd_6686071 3433168113087415450163825 := by
  unfold tailWord_6686071
  simp only [CollatzResearch.WordTrace]
  refine ⟨243861043360514131861402067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162574028907009421240934711 243861043360514131861402067)
  ·
    refine ⟨365791565040771197792103101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243861043360514131861402067 365791565040771197792103101)
    ·
      refine ⟨137171836890289199172038663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365791565040771197792103101 137171836890289199172038663)
      ·
        refine ⟨205757755335433798758057995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137171836890289199172038663 205757755335433798758057995)
        ·
          refine ⟨308636633003150698137086993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205757755335433798758057995 308636633003150698137086993)
          ·
            refine ⟨231477474752363023602815245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308636633003150698137086993 231477474752363023602815245)
            ·
              refine ⟨86804053032136133851055717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231477474752363023602815245 86804053032136133851055717)
              ·
                refine ⟨16275759943525525097072947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86804053032136133851055717 16275759943525525097072947)
                ·
                  refine ⟨24413639915288287645609421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16275759943525525097072947 24413639915288287645609421)
                  ·
                    refine ⟨9155114968233107867103533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24413639915288287645609421 9155114968233107867103533)
                    ·
                      refine ⟨3433168113087415450163825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9155114968233107867103533 3433168113087415450163825)
                      ·
                        rfl

theorem cell23_6686071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_6686071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686071 prefixEnd_6686071 := by exact prefixLift 6686071
  have htrace : WordTrace (prefixWord ++ tailWord_6686071) baseStart_6686071 baseEnd_6686071 := by
    simpa [prefixWord, tailWord_6686071, baseEnd_6686071] using wordTrace_append hprefix tailTrace_6686071
  have hstable : (prefixWord ++ tailWord_6686071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686071).length < 2 ^ (prefixWord ++ tailWord_6686071).sum := by decide
  have hdescent : baseEnd_6686071 < baseStart_6686071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686074 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_6686074 : Nat := 118140960795 + 6686074 * 2 ^ 59
def prefixEnd_6686074 : Nat := 4983230072969 + 3 ^ 40 * 6686074 * 2
def baseEnd_6686074 : Nat := 1144389884509792979475437

theorem tailTrace_6686074 : CollatzResearch.WordTrace tailWord_6686074 prefixEnd_6686074 1144389884509792979475437 := by
  unfold tailWord_6686074
  simp only [CollatzResearch.WordTrace]
  refine ⟨60965288194875815843440319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162574101853002175582507517 60965288194875815843440319)
  ·
    refine ⟨91447932292313723765160479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60965288194875815843440319 91447932292313723765160479)
    ·
      refine ⟨137171898438470585647740719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91447932292313723765160479 137171898438470585647740719)
      ·
        refine ⟨205757847657705878471611079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137171898438470585647740719 205757847657705878471611079)
        ·
          refine ⟨308636771486558817707416619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205757847657705878471611079 308636771486558817707416619)
          ·
            refine ⟨462955157229838226561124929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308636771486558817707416619 462955157229838226561124929)
            ·
              refine ⟨347216367922378669920843697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462955157229838226561124929 347216367922378669920843697)
              ·
                refine ⟨260412275941784002440632773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347216367922378669920843697 260412275941784002440632773)
                ·
                  refine ⟨48827301739084500457618645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260412275941784002440632773 48827301739084500457618645)
                  ·
                    refine ⟨1144389884509792979475437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48827301739084500457618645 1144389884509792979475437)
                    ·
                      rfl

theorem cell23_6686074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_6686074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686074 prefixEnd_6686074 := by exact prefixLift 6686074
  have htrace : WordTrace (prefixWord ++ tailWord_6686074) baseStart_6686074 baseEnd_6686074 := by
    simpa [prefixWord, tailWord_6686074, baseEnd_6686074] using wordTrace_append hprefix tailTrace_6686074
  have hstable : (prefixWord ++ tailWord_6686074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686074).length < 2 ^ (prefixWord ++ tailWord_6686074).sum := by decide
  have hdescent : baseEnd_6686074 < baseStart_6686074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686082 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_6686082 : Nat := 118140960795 + 6686082 * 2 ^ 59
def prefixEnd_6686082 : Nat := 4983230072969 + 3 ^ 40 * 6686082 * 2
def baseEnd_6686082 : Nat := 1144391253791538302375425

theorem tailTrace_6686082 : CollatzResearch.WordTrace tailWord_6686082 prefixEnd_6686082 1144391253791538302375425 := by
  unfold tailWord_6686082
  simp only [CollatzResearch.WordTrace]
  refine ⟨60965361140868570185013125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162574296375649520493368333 60965361140868570185013125)
  ·
    refine ⟨11431005213912856909689961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60965361140868570185013125 11431005213912856909689961)
    ·
      refine ⟨8573253910434642682267471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11431005213912856909689961 8573253910434642682267471)
      ·
        refine ⟨12859880865651964023401207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8573253910434642682267471 12859880865651964023401207)
        ·
          refine ⟨19289821298477946035101811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12859880865651964023401207 19289821298477946035101811)
          ·
            refine ⟨28934731947716919052652717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19289821298477946035101811 28934731947716919052652717)
            ·
              refine ⟨10850524480393844644744769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28934731947716919052652717 10850524480393844644744769)
              ·
                refine ⟨8137893360295383483558577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10850524480393844644744769 8137893360295383483558577)
                ·
                  refine ⟨6103420020221537612668933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8137893360295383483558577 6103420020221537612668933)
                  ·
                    refine ⟨1144391253791538302375425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6103420020221537612668933 1144391253791538302375425)
                    ·
                      rfl

theorem cell23_6686082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_6686082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686082 prefixEnd_6686082 := by exact prefixLift 6686082
  have htrace : WordTrace (prefixWord ++ tailWord_6686082) baseStart_6686082 baseEnd_6686082 := by
    simpa [prefixWord, tailWord_6686082, baseEnd_6686082] using wordTrace_append hprefix tailTrace_6686082
  have hstable : (prefixWord ++ tailWord_6686082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686082).length < 2 ^ (prefixWord ++ tailWord_6686082).sum := by decide
  have hdescent : baseEnd_6686082 < baseStart_6686082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686115 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 1, 3, 2]
def baseStart_6686115 : Nat := 118140960795 + 6686115 * 2 ^ 59
def prefixEnd_6686115 : Nat := 4983230072969 + 3 ^ 40 * 6686115 * 2
def baseEnd_6686115 : Nat := 3433190706236213278013623

theorem tailTrace_6686115 : CollatzResearch.WordTrace tailWord_6686115 prefixEnd_6686115 3433190706236213278013623 := by
  unfold tailWord_6686115
  simp only [CollatzResearch.WordTrace]
  refine ⟨243862648172354727376003799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162575098781569818250669199 243862648172354727376003799)
  ·
    refine ⟨365793972258532091064005699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243862648172354727376003799 365793972258532091064005699)
    ·
      refine ⟨548690958387798136596008549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365793972258532091064005699 548690958387798136596008549)
      ·
        refine ⟨102879554697712150611751603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 548690958387798136596008549 102879554697712150611751603)
        ·
          refine ⟨154319332046568225917627405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102879554697712150611751603 154319332046568225917627405)
          ·
            refine ⟨57869749517463084719110277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154319332046568225917627405 57869749517463084719110277)
            ·
              refine ⟨10850578034524328384833177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57869749517463084719110277 10850578034524328384833177)
              ·
                refine ⟨8137933525893246288624883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10850578034524328384833177 8137933525893246288624883)
                ·
                  refine ⟨12206900288839869432937325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8137933525893246288624883 12206900288839869432937325)
                  ·
                    refine ⟨4577587608314951037351497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12206900288839869432937325 4577587608314951037351497)
                    ·
                      refine ⟨3433190706236213278013623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577587608314951037351497 3433190706236213278013623)
                      ·
                        rfl

theorem cell23_6686115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_6686115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686115 prefixEnd_6686115 := by exact prefixLift 6686115
  have htrace : WordTrace (prefixWord ++ tailWord_6686115) baseStart_6686115 baseEnd_6686115 := by
    simpa [prefixWord, tailWord_6686115, baseEnd_6686115] using wordTrace_append hprefix tailTrace_6686115
  have hstable : (prefixWord ++ tailWord_6686115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686115).length < 2 ^ (prefixWord ++ tailWord_6686115).sum := by decide
  have hdescent : baseEnd_6686115 < baseStart_6686115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686191 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 5]
def baseStart_6686191 : Nat := 118140960795 + 6686191 * 2 ^ 59
def prefixEnd_6686191 : Nat := 4983230072969 + 3 ^ 40 * 6686191 * 2
def baseEnd_6686191 : Nat := 3433229730765954980663273

theorem tailTrace_6686191 : CollatzResearch.WordTrace tailWord_6686191 prefixEnd_6686191 3433229730765954980663273 := by
  unfold tailWord_6686191
  simp only [CollatzResearch.WordTrace]
  refine ⟨243865420120079392355770427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162576946746719594903846951 243865420120079392355770427)
  ·
    refine ⟨365798130180119088533655641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243865420120079392355770427 365798130180119088533655641)
    ·
      refine ⟨274348597635089316400241731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365798130180119088533655641 274348597635089316400241731)
      ·
        refine ⟨411522896452633974600362597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274348597635089316400241731 411522896452633974600362597)
        ·
          refine ⟨77160543084868870237567987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 411522896452633974600362597 77160543084868870237567987)
          ·
            refine ⟨115740814627303305356351981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77160543084868870237567987 115740814627303305356351981)
            ·
              refine ⟨43402805485238739508631993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115740814627303305356351981 43402805485238739508631993)
              ·
                refine ⟨32552104113929054631473995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43402805485238739508631993 32552104113929054631473995)
                ·
                  refine ⟨48828156170893581947210993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32552104113929054631473995 48828156170893581947210993)
                  ·
                    refine ⟨36621117128170186460408245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48828156170893581947210993 36621117128170186460408245)
                    ·
                      refine ⟨3433229730765954980663273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36621117128170186460408245 3433229730765954980663273)
                      ·
                        rfl

theorem cell23_6686191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_6686191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686191 prefixEnd_6686191 := by exact prefixLift 6686191
  have htrace : WordTrace (prefixWord ++ tailWord_6686191) baseStart_6686191 baseEnd_6686191 := by
    simpa [prefixWord, tailWord_6686191, baseEnd_6686191] using wordTrace_append hprefix tailTrace_6686191
  have hstable : (prefixWord ++ tailWord_6686191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686191).length < 2 ^ (prefixWord ++ tailWord_6686191).sum := by decide
  have hdescent : baseEnd_6686191 < baseStart_6686191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686201 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 4]
def baseStart_6686201 : Nat := 118140960795 + 6686201 * 2 ^ 59
def prefixEnd_6686201 : Nat := 4983230072969 + 3 ^ 40 * 6686201 * 2
def baseEnd_6686201 : Nat := 3433234865572499941538227

theorem tailTrace_6686201 : CollatzResearch.WordTrace tailWord_6686201 prefixEnd_6686201 3433234865572499941538227 := by
  unfold tailWord_6686201
  simp only [CollatzResearch.WordTrace]
  refine ⟨243865784850043164063634457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162577189900028776042422971 243865784850043164063634457)
  ·
    refine ⟨182899338637532373047725843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243865784850043164063634457 182899338637532373047725843)
    ·
      refine ⟨274349007956298559571588765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182899338637532373047725843 274349007956298559571588765)
      ·
        refine ⟨102880877983611959839345787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274349007956298559571588765 102880877983611959839345787)
        ·
          refine ⟨154321316975417939759018681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102880877983611959839345787 154321316975417939759018681)
          ·
            refine ⟨115740987731563454819264011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154321316975417939759018681 115740987731563454819264011)
            ·
              refine ⟨173611481597345182228896017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115740987731563454819264011 173611481597345182228896017)
              ·
                refine ⟨130208611198008886671672013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173611481597345182228896017 130208611198008886671672013)
                ·
                  refine ⟨48828229199253332501877005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130208611198008886671672013 48828229199253332501877005)
                  ·
                    refine ⟨18310585949719999688203877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48828229199253332501877005 18310585949719999688203877)
                    ·
                      refine ⟨3433234865572499941538227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18310585949719999688203877 3433234865572499941538227)
                      ·
                        rfl

theorem cell23_6686201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_6686201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686201 prefixEnd_6686201 := by exact prefixLift 6686201
  have htrace : WordTrace (prefixWord ++ tailWord_6686201) baseStart_6686201 baseEnd_6686201 := by
    simpa [prefixWord, tailWord_6686201, baseEnd_6686201] using wordTrace_append hprefix tailTrace_6686201
  have hstable : (prefixWord ++ tailWord_6686201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686201).length < 2 ^ (prefixWord ++ tailWord_6686201).sum := by decide
  have hdescent : baseEnd_6686201 < baseStart_6686201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686232 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 2, 5]
def baseStart_6686232 : Nat := 118140960795 + 6686232 * 2 ^ 59
def prefixEnd_6686232 : Nat := 4983230072969 + 3 ^ 40 * 6686232 * 2
def baseEnd_6686232 : Nat := 1144416927824263106750195

theorem tailTrace_6686232 : CollatzResearch.WordTrace tailWord_6686232 prefixEnd_6686232 1144416927824263106750195 := by
  unfold tailWord_6686232
  simp only [CollatzResearch.WordTrace]
  refine ⟨121933457756465428179006475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162577943675287237572008633 121933457756465428179006475)
  ·
    refine ⟨182900186634698142268509713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121933457756465428179006475 182900186634698142268509713)
    ·
      refine ⟨137175139976023606701382285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182900186634698142268509713 137175139976023606701382285)
      ·
        refine ⟨51440677491008852513018357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137175139976023606701382285 51440677491008852513018357)
        ·
          refine ⟨4822563514782079923095471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51440677491008852513018357 4822563514782079923095471)
          ·
            refine ⟨7233845272173119884643207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822563514782079923095471 7233845272173119884643207)
            ·
              refine ⟨10850767908259679826964811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7233845272173119884643207 10850767908259679826964811)
              ·
                refine ⟨16276151862389519740447217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10850767908259679826964811 16276151862389519740447217)
                ·
                  refine ⟨12207113896792139805335413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16276151862389519740447217 12207113896792139805335413)
                  ·
                    refine ⟨1144416927824263106750195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12207113896792139805335413 1144416927824263106750195)
                    ·
                      rfl

theorem cell23_6686232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_6686232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686232 prefixEnd_6686232 := by exact prefixLift 6686232
  have htrace : WordTrace (prefixWord ++ tailWord_6686232) baseStart_6686232 baseEnd_6686232 := by
    simpa [prefixWord, tailWord_6686232, baseEnd_6686232] using wordTrace_append hprefix tailTrace_6686232
  have hstable : (prefixWord ++ tailWord_6686232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686232).length < 2 ^ (prefixWord ++ tailWord_6686232).sum := by decide
  have hdescent : baseEnd_6686232 < baseStart_6686232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686281 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_6686281 : Nat := 118140960795 + 6686281 * 2 ^ 59
def prefixEnd_6686281 : Nat := 4983230072969 + 3 ^ 40 * 6686281 * 2
def baseEnd_6686281 : Nat := 3433275944024859628537859

theorem tailTrace_6686281 : CollatzResearch.WordTrace tailWord_6686281 prefixEnd_6686281 3433275944024859628537859 := by
  unfold tailWord_6686281
  simp only [CollatzResearch.WordTrace]
  refine ⟨243868702689753337726546697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162579135126502225151031131 243868702689753337726546697)
  ·
    refine ⟨182901527017315003294910023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243868702689753337726546697 182901527017315003294910023)
    ·
      refine ⟨274352290525972504942365035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182901527017315003294910023 274352290525972504942365035)
      ·
        refine ⟨411528435788958757413547553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274352290525972504942365035 411528435788958757413547553)
        ·
          refine ⟨308646326841719068060160665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411528435788958757413547553 308646326841719068060160665)
          ·
            refine ⟨231484745131289301045120499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308646326841719068060160665 231484745131289301045120499)
            ·
              refine ⟨347227117696933951567680749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231484745131289301045120499 347227117696933951567680749)
              ·
                refine ⟨130210169136350231837880281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347227117696933951567680749 130210169136350231837880281)
                ·
                  refine ⟨97657626852262673878410211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130210169136350231837880281 97657626852262673878410211)
                  ·
                    refine ⟨146486440278394010817615317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97657626852262673878410211 146486440278394010817615317)
                    ·
                      refine ⟨3433275944024859628537859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146486440278394010817615317 3433275944024859628537859)
                      ·
                        rfl

theorem cell23_6686281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_6686281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686281 prefixEnd_6686281 := by exact prefixLift 6686281
  have htrace : WordTrace (prefixWord ++ tailWord_6686281) baseStart_6686281 baseEnd_6686281 := by
    simpa [prefixWord, tailWord_6686281, baseEnd_6686281] using wordTrace_append hprefix tailTrace_6686281
  have hstable : (prefixWord ++ tailWord_6686281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686281).length < 2 ^ (prefixWord ++ tailWord_6686281).sum := by decide
  have hdescent : baseEnd_6686281 < baseStart_6686281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686295 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 1, 5, 2]
def baseStart_6686295 : Nat := 118140960795 + 6686295 * 2 ^ 59
def prefixEnd_6686295 : Nat := 4983230072969 + 3 ^ 40 * 6686295 * 2
def baseEnd_6686295 : Nat := 3433283132754022573762795

theorem tailTrace_6686295 : CollatzResearch.WordTrace tailWord_6686295 prefixEnd_6686295 3433283132754022573762795 := by
  unfold tailWord_6686295
  simp only [CollatzResearch.WordTrace]
  refine ⟨243869213311702618117556339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162579475541135078745037559 243869213311702618117556339)
  ·
    refine ⟨365803819967553927176334509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243869213311702618117556339 365803819967553927176334509)
    ·
      refine ⟨137176432487832722691125441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365803819967553927176334509 137176432487832722691125441)
      ·
        refine ⟨102882324365874542018344081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137176432487832722691125441 102882324365874542018344081)
        ·
          refine ⟨77161743274405906513758061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102882324365874542018344081 77161743274405906513758061)
          ·
            refine ⟨28935653727902214942659273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77161743274405906513758061 28935653727902214942659273)
            ·
              refine ⟨21701740295926661206994455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28935653727902214942659273 21701740295926661206994455)
              ·
                refine ⟨32552610443889991810491683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21701740295926661206994455 32552610443889991810491683)
                ·
                  refine ⟨48828915665834987715737525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32552610443889991810491683 48828915665834987715737525)
                  ·
                    refine ⟨4577710843672030098350393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48828915665834987715737525 4577710843672030098350393)
                    ·
                      refine ⟨3433283132754022573762795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577710843672030098350393 3433283132754022573762795)
                      ·
                        rfl

theorem cell23_6686295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_6686295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686295 prefixEnd_6686295 := by exact prefixLift 6686295
  have htrace : WordTrace (prefixWord ++ tailWord_6686295) baseStart_6686295 baseEnd_6686295 := by
    simpa [prefixWord, tailWord_6686295, baseEnd_6686295] using wordTrace_append hprefix tailTrace_6686295
  have hstable : (prefixWord ++ tailWord_6686295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686295).length < 2 ^ (prefixWord ++ tailWord_6686295).sum := by decide
  have hdescent : baseEnd_6686295 < baseStart_6686295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686312 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6686312 : Nat := 118140960795 + 6686312 * 2 ^ 59
def prefixEnd_6686312 : Nat := 4983230072969 + 3 ^ 40 * 6686312 * 2
def baseEnd_6686312 : Nat := 3433291861925149007250217

theorem tailTrace_6686312 : CollatzResearch.WordTrace tailWord_6686312 prefixEnd_6686312 3433291861925149007250217 := by
  unfold tailWord_6686312
  simp only [CollatzResearch.WordTrace]
  refine ⟨121934916676320515010462595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162579888901760686680616793 121934916676320515010462595)
  ·
    refine ⟨182902375014480772515693893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121934916676320515010462595 182902375014480772515693893)
    ·
      refine ⟨34294195315215144846692605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182902375014480772515693893 34294195315215144846692605)
      ·
        refine ⟨12860323243205679317509727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34294195315215144846692605 12860323243205679317509727)
        ·
          refine ⟨19290484864808518976264591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12860323243205679317509727 19290484864808518976264591)
          ·
            refine ⟨28935727297212778464396887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19290484864808518976264591 28935727297212778464396887)
            ·
              refine ⟨43403590945819167696595331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28935727297212778464396887 43403590945819167696595331)
              ·
                refine ⟨65105386418728751544892997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43403590945819167696595331 65105386418728751544892997)
                ·
                  refine ⟨12207259953511640914667437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65105386418728751544892997 12207259953511640914667437)
                  ·
                    refine ⟨4577722482566865343000289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12207259953511640914667437 4577722482566865343000289)
                    ·
                      refine ⟨3433291861925149007250217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577722482566865343000289 3433291861925149007250217)
                      ·
                        rfl

theorem cell23_6686312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6686312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686312 prefixEnd_6686312 := by exact prefixLift 6686312
  have htrace : WordTrace (prefixWord ++ tailWord_6686312) baseStart_6686312 baseEnd_6686312 := by
    simpa [prefixWord, tailWord_6686312, baseEnd_6686312] using wordTrace_append hprefix tailTrace_6686312
  have hstable : (prefixWord ++ tailWord_6686312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686312).length < 2 ^ (prefixWord ++ tailWord_6686312).sum := by decide
  have hdescent : baseEnd_6686312 < baseStart_6686312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686370 : List Nat := [3, 3, 1, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_6686370 : Nat := 118140960795 + 6686370 * 2 ^ 59
def prefixEnd_6686370 : Nat := 4983230072969 + 3 ^ 40 * 6686370 * 2
def baseEnd_6686370 : Nat := 3433321643803109780324951

theorem tailTrace_6686370 : CollatzResearch.WordTrace tailWord_6686370 prefixEnd_6686370 3433321643803109780324951 := by
  unfold tailWord_6686370
  simp only [CollatzResearch.WordTrace]
  refine ⟨60967987196607726481634141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162581299190953937284357709 60967987196607726481634141)
  ·
    refine ⟨22862995198727897430612803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60967987196607726481634141 22862995198727897430612803)
    ·
      refine ⟨34294492798091846145919205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22862995198727897430612803 34294492798091846145919205)
      ·
        refine ⟨6430217399642221152359851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34294492798091846145919205 6430217399642221152359851)
        ·
          refine ⟨9645326099463331728539777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6430217399642221152359851 9645326099463331728539777)
          ·
            refine ⟨7233994574597498796404833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9645326099463331728539777 7233994574597498796404833)
            ·
              refine ⟨5425495930948124097303625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7233994574597498796404833 5425495930948124097303625)
              ·
                refine ⟨4069121948211093072977719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5425495930948124097303625 4069121948211093072977719)
                ·
                  refine ⟨6103682922316639609466579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069121948211093072977719 6103682922316639609466579)
                  ·
                    refine ⟨9155524383474959414199869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6103682922316639609466579 9155524383474959414199869)
                    ·
                      refine ⟨3433321643803109780324951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9155524383474959414199869 3433321643803109780324951)
                      ·
                        rfl

theorem cell23_6686370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_6686370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686370 prefixEnd_6686370 := by exact prefixLift 6686370
  have htrace : WordTrace (prefixWord ++ tailWord_6686370) baseStart_6686370 baseEnd_6686370 := by
    simpa [prefixWord, tailWord_6686370, baseEnd_6686370] using wordTrace_append hprefix tailTrace_6686370
  have hstable : (prefixWord ++ tailWord_6686370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686370).length < 2 ^ (prefixWord ++ tailWord_6686370).sum := by decide
  have hdescent : baseEnd_6686370 < baseStart_6686370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686408 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 1, 8]
def baseStart_6686408 : Nat := 118140960795 + 6686408 * 2 ^ 59
def prefixEnd_6686408 : Nat := 4983230072969 + 3 ^ 40 * 6686408 * 2
def baseEnd_6686408 : Nat := 1144447052022660210549925

theorem tailTrace_6686408 : CollatzResearch.WordTrace tailWord_6686408 prefixEnd_6686408 1144447052022660210549925 := by
  unfold tailWord_6686408
  simp only [CollatzResearch.WordTrace]
  refine ⟨121936667380146619208209939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162582223173528825610946585 121936667380146619208209939)
  ·
    refine ⟨182905001070219928812314909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121936667380146619208209939 182905001070219928812314909)
    ·
      refine ⟨68589375401332473304618091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182905001070219928812314909 68589375401332473304618091)
      ·
        refine ⟨102884063101998709956927137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68589375401332473304618091 102884063101998709956927137)
        ·
          refine ⟨77163047326499032467695353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102884063101998709956927137 77163047326499032467695353)
          ·
            refine ⟨57872285494874274350771515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77163047326499032467695353 57872285494874274350771515)
            ·
              refine ⟨86808428242311411526157273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57872285494874274350771515 86808428242311411526157273)
              ·
                refine ⟨65106321181733558644617955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86808428242311411526157273 65106321181733558644617955)
                ·
                  refine ⟨97659481772600337966926933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65106321181733558644617955 97659481772600337966926933)
                  ·
                    refine ⟨1144447052022660210549925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97659481772600337966926933 1144447052022660210549925)
                    ·
                      rfl

theorem cell23_6686408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_6686408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686408 prefixEnd_6686408 := by exact prefixLift 6686408
  have htrace : WordTrace (prefixWord ++ tailWord_6686408) baseStart_6686408 baseEnd_6686408 := by
    simpa [prefixWord, tailWord_6686408, baseEnd_6686408] using wordTrace_append hprefix tailTrace_6686408
  have hstable : (prefixWord ++ tailWord_6686408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686408).length < 2 ^ (prefixWord ++ tailWord_6686408).sum := by decide
  have hdescent : baseEnd_6686408 < baseStart_6686408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686413 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_6686413 : Nat := 118140960795 + 6686413 * 2 ^ 59
def prefixEnd_6686413 : Nat := 4983230072969 + 3 ^ 40 * 6686413 * 2
def baseEnd_6686413 : Nat := 3433343723471253112087253

theorem tailTrace_6686413 : CollatzResearch.WordTrace tailWord_6686413 prefixEnd_6686413 3433343723471253112087253 := by
  unfold tailWord_6686413
  simp only [CollatzResearch.WordTrace]
  refine ⟨243873517125275124270351893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162582344750183416180234595 243873517125275124270351893)
  ·
    refine ⟨11431571115247271450172745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 243873517125275124270351893 11431571115247271450172745)
    ·
      refine ⟨8573678336435453587629559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11431571115247271450172745 8573678336435453587629559)
      ·
        refine ⟨12860517504653180381444339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8573678336435453587629559 12860517504653180381444339)
        ·
          refine ⟨19290776256979770572166509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12860517504653180381444339 19290776256979770572166509)
          ·
            refine ⟨7234041096367413964562441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19290776256979770572166509 7234041096367413964562441)
            ·
              refine ⟨5425530822275560473421831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7234041096367413964562441 5425530822275560473421831)
              ·
                refine ⟨8138296233413340710132747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425530822275560473421831 8138296233413340710132747)
                ·
                  refine ⟨12207444350120011065199121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8138296233413340710132747 12207444350120011065199121)
                  ·
                    refine ⟨9155583262590008298899341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12207444350120011065199121 9155583262590008298899341)
                    ·
                      refine ⟨3433343723471253112087253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9155583262590008298899341 3433343723471253112087253)
                      ·
                        rfl

theorem cell23_6686413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_6686413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686413 prefixEnd_6686413 := by exact prefixLift 6686413
  have htrace : WordTrace (prefixWord ++ tailWord_6686413) baseStart_6686413 baseEnd_6686413 := by
    simpa [prefixWord, tailWord_6686413, baseEnd_6686413] using wordTrace_append hprefix tailTrace_6686413
  have hstable : (prefixWord ++ tailWord_6686413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686413).length < 2 ^ (prefixWord ++ tailWord_6686413).sum := by decide
  have hdescent : baseEnd_6686413 < baseStart_6686413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686449 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 1, 4, 2]
def baseStart_6686449 : Nat := 118140960795 + 6686449 * 2 ^ 59
def prefixEnd_6686449 : Nat := 4983230072969 + 3 ^ 40 * 6686449 * 2
def baseEnd_6686449 : Nat := 3433362208774814971237087

theorem tailTrace_6686449 : CollatzResearch.WordTrace tailWord_6686449 prefixEnd_6686449 3433362208774814971237087 := by
  unfold tailWord_6686449
  simp only [CollatzResearch.WordTrace]
  refine ⟨243874830153144702418662401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162583220102096468279108267 243874830153144702418662401)
  ·
    refine ⟨182906122614858526813996801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243874830153144702418662401 182906122614858526813996801)
    ·
      refine ⟨137179591961143895110497601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182906122614858526813996801 137179591961143895110497601)
      ·
        refine ⟨102884693970857921332873201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137179591961143895110497601 102884693970857921332873201)
        ·
          refine ⟨77163520478143440999654901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102884693970857921332873201 77163520478143440999654901)
          ·
            refine ⟨7234080044825947593717647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77163520478143440999654901 7234080044825947593717647)
            ·
              refine ⟨10851120067238921390576471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7234080044825947593717647 10851120067238921390576471)
              ·
                refine ⟨16276680100858382085864707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10851120067238921390576471 16276680100858382085864707)
                ·
                  refine ⟨24415020151287573128797061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16276680100858382085864707 24415020151287573128797061)
                  ·
                    refine ⟨4577816278366419961649449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24415020151287573128797061 4577816278366419961649449)
                    ·
                      refine ⟨3433362208774814971237087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577816278366419961649449 3433362208774814971237087)
                      ·
                        rfl

theorem cell23_6686449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_6686449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686449 prefixEnd_6686449 := by exact prefixLift 6686449
  have htrace : WordTrace (prefixWord ++ tailWord_6686449) baseStart_6686449 baseEnd_6686449 := by
    simpa [prefixWord, tailWord_6686449, baseEnd_6686449] using wordTrace_append hprefix tailTrace_6686449
  have hstable : (prefixWord ++ tailWord_6686449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686449).length < 2 ^ (prefixWord ++ tailWord_6686449).sum := by decide
  have hdescent : baseEnd_6686449 < baseStart_6686449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686465 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_6686465 : Nat := 118140960795 + 6686465 * 2 ^ 59
def prefixEnd_6686465 : Nat := 4983230072969 + 3 ^ 40 * 6686465 * 2
def baseEnd_6686465 : Nat := 3433370424465286908637013

theorem tailTrace_6686465 : CollatzResearch.WordTrace tailWord_6686465 prefixEnd_6686465 3433370424465286908637013 := by
  unfold tailWord_6686465
  simp only [CollatzResearch.WordTrace]
  refine ⟨243875413721086737151244849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162583609147391158100829899 243875413721086737151244849)
  ·
    refine ⟨182906560290815052863433637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243875413721086737151244849 182906560290815052863433637)
    ·
      refine ⟨34294980054527822411893807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182906560290815052863433637 34294980054527822411893807)
      ·
        refine ⟨51442470081791733617840711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34294980054527822411893807 51442470081791733617840711)
        ·
          refine ⟨77163705122687600426761067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51442470081791733617840711 77163705122687600426761067)
          ·
            refine ⟨115745557684031400640141601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77163705122687600426761067 115745557684031400640141601)
            ·
              refine ⟨86809168263023550480106201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115745557684031400640141601 86809168263023550480106201)
              ·
                refine ⟨65106876197267662860079651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86809168263023550480106201 65106876197267662860079651)
                ·
                  refine ⟨97660314295901494290119477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65106876197267662860079651 97660314295901494290119477)
                  ·
                    refine ⟨9155654465240765089698701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97660314295901494290119477 9155654465240765089698701)
                    ·
                      refine ⟨3433370424465286908637013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9155654465240765089698701 3433370424465286908637013)
                      ·
                        rfl

theorem cell23_6686465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_6686465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686465 prefixEnd_6686465 := by exact prefixLift 6686465
  have htrace : WordTrace (prefixWord ++ tailWord_6686465) baseStart_6686465 baseEnd_6686465 := by
    simpa [prefixWord, tailWord_6686465, baseEnd_6686465] using wordTrace_append hprefix tailTrace_6686465
  have hstable : (prefixWord ++ tailWord_6686465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686465).length < 2 ^ (prefixWord ++ tailWord_6686465).sum := by decide
  have hdescent : baseEnd_6686465 < baseStart_6686465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686485 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_6686485 : Nat := 118140960795 + 6686485 * 2 ^ 59
def prefixEnd_6686485 : Nat := 4983230072969 + 3 ^ 40 * 6686485 * 2
def baseEnd_6686485 : Nat := 1144460231359458943462307

theorem tailTrace_6686485 : CollatzResearch.WordTrace tailWord_6686485 prefixEnd_6686485 1144460231359458943462307 := by
  unfold tailWord_6686485
  simp only [CollatzResearch.WordTrace]
  refine ⟨243876143181014280566972909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162584095454009520377981939 243876143181014280566972909)
  ·
    refine ⟨91453553692880355212614841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243876143181014280566972909 91453553692880355212614841)
    ·
      refine ⟨68590165269660266409461131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91453553692880355212614841 68590165269660266409461131)
      ·
        refine ⟨102885247904490399614191697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68590165269660266409461131 102885247904490399614191697)
        ·
          refine ⟨77163935928367799710643773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102885247904490399614191697 77163935928367799710643773)
          ·
            refine ⟨28936475973137924891491415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77163935928367799710643773 28936475973137924891491415)
            ·
              refine ⟨43404713959706887337237123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28936475973137924891491415 43404713959706887337237123)
              ·
                refine ⟨65107070939560331005855685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43404713959706887337237123 65107070939560331005855685)
                ·
                  refine ⟨12207575801167562063597941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65107070939560331005855685 12207575801167562063597941)
                  ·
                    refine ⟨1144460231359458943462307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12207575801167562063597941 1144460231359458943462307)
                    ·
                      rfl

theorem cell23_6686485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_6686485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686485 prefixEnd_6686485 := by exact prefixLift 6686485
  have htrace : WordTrace (prefixWord ++ tailWord_6686485) baseStart_6686485 baseEnd_6686485 := by
    simpa [prefixWord, tailWord_6686485, baseEnd_6686485] using wordTrace_append hprefix tailTrace_6686485
  have hstable : (prefixWord ++ tailWord_6686485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686485).length < 2 ^ (prefixWord ++ tailWord_6686485).sum := by decide
  have hdescent : baseEnd_6686485 < baseStart_6686485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686492 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_6686492 : Nat := 118140960795 + 6686492 * 2 ^ 59
def prefixEnd_6686492 : Nat := 4983230072969 + 3 ^ 40 * 6686492 * 2
def baseEnd_6686492 : Nat := 3433384288442958302999389

theorem tailTrace_6686492 : CollatzResearch.WordTrace tailWord_6686492 prefixEnd_6686492 3433384288442958302999389 := by
  unfold tailWord_6686492
  simp only [CollatzResearch.WordTrace]
  refine ⟨121938199245994460381238865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162584265661325947174985153 121938199245994460381238865)
  ·
    refine ⟨91453649434495845285929149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121938199245994460381238865 91453649434495845285929149)
    ·
      refine ⟨34295118537935941982223431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91453649434495845285929149 34295118537935941982223431)
      ·
        refine ⟨51442677806903912973335147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34295118537935941982223431 51442677806903912973335147)
        ·
          refine ⟨77164016710355869460002721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51442677806903912973335147 77164016710355869460002721)
          ·
            refine ⟨57873012532766902095002041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77164016710355869460002721 57873012532766902095002041)
            ·
              refine ⟨43404759399575176571251531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57873012532766902095002041 43404759399575176571251531)
              ·
                refine ⟨65107139099362764856877297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43404759399575176571251531 65107139099362764856877297)
                ·
                  refine ⟨48830354324522073642657973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65107139099362764856877297 48830354324522073642657973)
                  ·
                    refine ⟨4577845717923944403999185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48830354324522073642657973 4577845717923944403999185)
                    ·
                      refine ⟨3433384288442958302999389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577845717923944403999185 3433384288442958302999389)
                      ·
                        rfl

theorem cell23_6686492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_6686492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686492 prefixEnd_6686492 := by exact prefixLift 6686492
  have htrace : WordTrace (prefixWord ++ tailWord_6686492) baseStart_6686492 baseEnd_6686492 := by
    simpa [prefixWord, tailWord_6686492, baseEnd_6686492] using wordTrace_append hprefix tailTrace_6686492
  have hstable : (prefixWord ++ tailWord_6686492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686492).length < 2 ^ (prefixWord ++ tailWord_6686492).sum := by decide
  have hdescent : baseEnd_6686492 < baseStart_6686492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686495 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 5]
def baseStart_6686495 : Nat := 118140960795 + 6686495 * 2 ^ 59
def prefixEnd_6686495 : Nat := 4983230072969 + 3 ^ 40 * 6686495 * 2
def baseEnd_6686495 : Nat := 3433385828884921791261875

theorem tailTrace_6686495 : CollatzResearch.WordTrace tailWord_6686495 prefixEnd_6686495 3433385828884921791261875 := by
  unfold tailWord_6686495
  simp only [CollatzResearch.WordTrace]
  refine ⟨243876507910978052274836939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162584338607318701516557959 243876507910978052274836939)
  ·
    refine ⟨365814761866467078412255409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243876507910978052274836939 365814761866467078412255409)
    ·
      refine ⟨274361071399850308809191557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365814761866467078412255409 274361071399850308809191557)
      ·
        refine ⟨51442700887471932901723417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274361071399850308809191557 51442700887471932901723417)
        ·
          refine ⟨38582025665603949676292563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51442700887471932901723417 38582025665603949676292563)
          ·
            refine ⟨57873038498405924514438845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38582025665603949676292563 57873038498405924514438845)
            ·
              refine ⟨21702389436902221692914567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57873038498405924514438845 21702389436902221692914567)
              ·
                refine ⟨32553584155353332539371851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21702389436902221692914567 32553584155353332539371851)
                ·
                  refine ⟨48830376233029998809057777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32553584155353332539371851 48830376233029998809057777)
                  ·
                    refine ⟨36622782174772499106793333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48830376233029998809057777 36622782174772499106793333)
                    ·
                      refine ⟨3433385828884921791261875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36622782174772499106793333 3433385828884921791261875)
                      ·
                        rfl

theorem cell23_6686495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_6686495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686495 prefixEnd_6686495 := by exact prefixLift 6686495
  have htrace : WordTrace (prefixWord ++ tailWord_6686495) baseStart_6686495 baseEnd_6686495 := by
    simpa [prefixWord, tailWord_6686495, baseEnd_6686495] using wordTrace_append hprefix tailTrace_6686495
  have hstable : (prefixWord ++ tailWord_6686495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686495).length < 2 ^ (prefixWord ++ tailWord_6686495).sum := by decide
  have hdescent : baseEnd_6686495 < baseStart_6686495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686522 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_6686522 : Nat := 118140960795 + 6686522 * 2 ^ 59
def prefixEnd_6686522 : Nat := 4983230072969 + 3 ^ 40 * 6686522 * 2
def baseEnd_6686522 : Nat := 3433399692862593185624251

theorem tailTrace_6686522 : CollatzResearch.WordTrace tailWord_6686522 prefixEnd_6686522 3433399692862593185624251 := by
  unfold tailWord_6686522
  simp only [CollatzResearch.WordTrace]
  refine ⟨60969373170470058971517455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162584995121253490590713213 60969373170470058971517455)
  ·
    refine ⟨91454059755705088457276183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60969373170470058971517455 91454059755705088457276183)
    ·
      refine ⟨137181089633557632685914275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91454059755705088457276183 137181089633557632685914275)
      ·
        refine ⟨205771634450336449028871413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137181089633557632685914275 205771634450336449028871413)
        ·
          refine ⟨19291090729719042096456695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205771634450336449028871413 19291090729719042096456695)
          ·
            refine ⟨28936636094578563144685043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19291090729719042096456695 28936636094578563144685043)
            ·
              refine ⟨43404954141867844717027565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28936636094578563144685043 43404954141867844717027565)
              ·
                refine ⟨16276857803200441768885337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43404954141867844717027565 16276857803200441768885337)
                ·
                  refine ⟨12207643352400331326664003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16276857803200441768885337 12207643352400331326664003)
                  ·
                    refine ⟨18311465028600496989996005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12207643352400331326664003 18311465028600496989996005)
                    ·
                      refine ⟨3433399692862593185624251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18311465028600496989996005 3433399692862593185624251)
                      ·
                        rfl

theorem cell23_6686522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_6686522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686522 prefixEnd_6686522 := by exact prefixLift 6686522
  have htrace : WordTrace (prefixWord ++ tailWord_6686522) baseStart_6686522 baseEnd_6686522 := by
    simpa [prefixWord, tailWord_6686522, baseEnd_6686522] using wordTrace_append hprefix tailTrace_6686522
  have hstable : (prefixWord ++ tailWord_6686522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686522).length < 2 ^ (prefixWord ++ tailWord_6686522).sum := by decide
  have hdescent : baseEnd_6686522 < baseStart_6686522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686556 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_6686556 : Nat := 118140960795 + 6686556 * 2 ^ 59
def prefixEnd_6686556 : Nat := 4983230072969 + 3 ^ 40 * 6686556 * 2
def baseEnd_6686556 : Nat := 3433417151204846052599095

theorem tailTrace_6686556 : CollatzResearch.WordTrace tailWord_6686556 prefixEnd_6686556 3433417151204846052599095 := by
  unfold tailWord_6686556
  simp only [CollatzResearch.WordTrace]
  refine ⟨121939366381878529846403761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162585821842504706461871681 121939366381878529846403761)
  ·
    refine ⟨91454524786408897384802821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121939366381878529846403761 91454524786408897384802821)
    ·
      refine ⟨17147723397451668259650529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91454524786408897384802821 17147723397451668259650529)
      ·
        refine ⟨12860792548088751194737897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17147723397451668259650529 12860792548088751194737897)
        ·
          refine ⟨9645594411066563396053423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12860792548088751194737897 9645594411066563396053423)
          ·
            refine ⟨14468391616599845094080135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9645594411066563396053423 14468391616599845094080135)
            ·
              refine ⟨21702587424899767641120203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14468391616599845094080135 21702587424899767641120203)
              ·
                refine ⟨32553881137349651461680305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21702587424899767641120203 32553881137349651461680305)
                ·
                  refine ⟨24415410853012238596260229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32553881137349651461680305 24415410853012238596260229)
                  ·
                    refine ⟨4577889534939794736798793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24415410853012238596260229 4577889534939794736798793)
                    ·
                      refine ⟨3433417151204846052599095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4577889534939794736798793 3433417151204846052599095)
                      ·
                        rfl

theorem cell23_6686556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_6686556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686556 prefixEnd_6686556 := by exact prefixLift 6686556
  have htrace : WordTrace (prefixWord ++ tailWord_6686556) baseStart_6686556 baseEnd_6686556 := by
    simpa [prefixWord, tailWord_6686556, baseEnd_6686556] using wordTrace_append hprefix tailTrace_6686556
  have hstable : (prefixWord ++ tailWord_6686556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686556).length < 2 ^ (prefixWord ++ tailWord_6686556).sum := by decide
  have hdescent : baseEnd_6686556 < baseStart_6686556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686592 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 1, 5]
def baseStart_6686592 : Nat := 118140960795 + 6686592 * 2 ^ 59
def prefixEnd_6686592 : Nat := 4983230072969 + 3 ^ 40 * 6686592 * 2
def baseEnd_6686592 : Nat := 1144478545502802637249643

theorem tailTrace_6686592 : CollatzResearch.WordTrace tailWord_6686592 prefixEnd_6686592 1144478545502802637249643 := by
  unfold tailWord_6686592
  simp only [CollatzResearch.WordTrace]
  refine ⟨121940022895813318920559015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162586697194417758560745353 121940022895813318920559015)
  ·
    refine ⟨182910034343719978380838523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121940022895813318920559015 182910034343719978380838523)
    ·
      refine ⟨274365051515579967571257785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182910034343719978380838523 274365051515579967571257785)
      ·
        refine ⟨205773788636684975678443339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274365051515579967571257785 205773788636684975678443339)
        ·
          refine ⟨308660682955027463517665009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205773788636684975678443339 308660682955027463517665009)
          ·
            refine ⟨231495512216270597638248757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308660682955027463517665009 231495512216270597638248757)
            ·
              refine ⟨21702704270275368528585821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231495512216270597638248757 21702704270275368528585821)
              ·
                refine ⟨8138514101353263198219683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21702704270275368528585821 8138514101353263198219683)
                ·
                  refine ⟨12207771152029894797329525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8138514101353263198219683 12207771152029894797329525)
                  ·
                    refine ⟨1144478545502802637249643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12207771152029894797329525 1144478545502802637249643)
                    ·
                      rfl

theorem cell23_6686592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 5].length) (baseStart_6686592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686592 prefixEnd_6686592 := by exact prefixLift 6686592
  have htrace : WordTrace (prefixWord ++ tailWord_6686592) baseStart_6686592 baseEnd_6686592 := by
    simpa [prefixWord, tailWord_6686592, baseEnd_6686592] using wordTrace_append hprefix tailTrace_6686592
  have hstable : (prefixWord ++ tailWord_6686592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686592).length < 2 ^ (prefixWord ++ tailWord_6686592).sum := by decide
  have hdescent : baseEnd_6686592 < baseStart_6686592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686626 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_6686626 : Nat := 118140960795 + 6686626 * 2 ^ 59
def prefixEnd_6686626 : Nat := 4983230072969 + 3 ^ 40 * 6686626 * 2
def baseEnd_6686626 : Nat := 1144484364950220259574591

theorem tailTrace_6686626 : CollatzResearch.WordTrace tailWord_6686626 prefixEnd_6686626 1144484364950220259574591 := by
  unfold tailWord_6686626
  simp only [CollatzResearch.WordTrace]
  refine ⟨60970321468375865411963933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162587523915668974431903821 60970321468375865411963933)
  ·
    refine ⟨22863870550640949529486475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60970321468375865411963933 22863870550640949529486475)
    ·
      refine ⟨34295805825961424294229713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22863870550640949529486475 34295805825961424294229713)
      ·
        refine ⟨25721854369471068220672285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34295805825961424294229713 25721854369471068220672285)
        ·
          refine ⟨9645695388551650582752107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25721854369471068220672285 9645695388551650582752107)
          ·
            refine ⟨14468543082827475874128161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9645695388551650582752107 14468543082827475874128161)
            ·
              refine ⟨10851407312120606905596121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14468543082827475874128161 10851407312120606905596121)
              ·
                refine ⟨8138555484090455179197091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10851407312120606905596121 8138555484090455179197091)
                ·
                  refine ⟨12207833226135682768795637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8138555484090455179197091 12207833226135682768795637)
                  ·
                    refine ⟨1144484364950220259574591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12207833226135682768795637 1144484364950220259574591)
                    ·
                      rfl

theorem cell23_6686626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_6686626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686626 prefixEnd_6686626 := by exact prefixLift 6686626
  have htrace : WordTrace (prefixWord ++ tailWord_6686626) baseStart_6686626 baseEnd_6686626 := by
    simpa [prefixWord, tailWord_6686626, baseEnd_6686626] using wordTrace_append hprefix tailTrace_6686626
  have hstable : (prefixWord ++ tailWord_6686626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686626).length < 2 ^ (prefixWord ++ tailWord_6686626).sum := by decide
  have hdescent : baseEnd_6686626 < baseStart_6686626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686642 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_6686642 : Nat := 118140960795 + 6686642 * 2 ^ 59
def prefixEnd_6686642 : Nat := 4983230072969 + 3 ^ 40 * 6686642 * 2
def baseEnd_6686642 : Nat := 3433461310541132716123699

theorem tailTrace_6686642 : CollatzResearch.WordTrace tailWord_6686642 prefixEnd_6686642 3433461310541132716123699 := by
  unfold tailWord_6686642
  simp only [CollatzResearch.WordTrace]
  refine ⟨60970467360361374095109545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162587912960963664253625453 60970467360361374095109545)
  ·
    refine ⟨45727850520271030571332159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60970467360361374095109545 45727850520271030571332159)
    ·
      refine ⟨68591775780406545856998239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45727850520271030571332159 68591775780406545856998239)
      ·
        refine ⟨102887663670609818785497359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68591775780406545856998239 102887663670609818785497359)
        ·
          refine ⟨154331495505914728178246039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102887663670609818785497359 154331495505914728178246039)
          ·
            refine ⟨231497243258872092267369059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154331495505914728178246039 231497243258872092267369059)
            ·
              refine ⟨347245864888308138401053589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231497243258872092267369059 347245864888308138401053589)
              ·
                refine ⟨16277149916639443987549387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 347245864888308138401053589 16277149916639443987549387)
                ·
                  refine ⟨24415724874959165981324081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16277149916639443987549387 24415724874959165981324081)
                  ·
                    refine ⟨18311793656219374485993061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24415724874959165981324081 18311793656219374485993061)
                    ·
                      refine ⟨3433461310541132716123699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18311793656219374485993061 3433461310541132716123699)
                      ·
                        rfl

theorem cell23_6686642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_6686642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686642 prefixEnd_6686642 := by exact prefixLift 6686642
  have htrace : WordTrace (prefixWord ++ tailWord_6686642) baseStart_6686642 baseEnd_6686642 := by
    simpa [prefixWord, tailWord_6686642, baseEnd_6686642] using wordTrace_append hprefix tailTrace_6686642
  have hstable : (prefixWord ++ tailWord_6686642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686642).length < 2 ^ (prefixWord ++ tailWord_6686642).sum := by decide
  have hdescent : baseEnd_6686642 < baseStart_6686642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686649 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 1, 2, 3]
def baseStart_6686649 : Nat := 118140960795 + 6686649 * 2 ^ 59
def prefixEnd_6686649 : Nat := 4983230072969 + 3 ^ 40 * 6686649 * 2
def baseEnd_6686649 : Nat := 3433464904905714188736167

theorem tailTrace_6686649 : CollatzResearch.WordTrace tailWord_6686649 prefixEnd_6686649 3433464904905714188736167 := by
  unfold tailWord_6686649
  simp only [CollatzResearch.WordTrace]
  refine ⟨243882124752420136575943001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162588083168280091050628667 243882124752420136575943001)
  ·
    refine ⟨182911593564315102431957251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243882124752420136575943001 182911593564315102431957251)
    ·
      refine ⟨274367390346472653647935877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182911593564315102431957251 274367390346472653647935877)
      ·
        refine ⟨51443885689963622558987977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274367390346472653647935877 51443885689963622558987977)
        ·
          refine ⟨38582914267472716919240983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51443885689963622558987977 38582914267472716919240983)
          ·
            refine ⟨57874371401209075378861475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38582914267472716919240983 57874371401209075378861475)
            ·
              refine ⟨86811557101813613068292213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57874371401209075378861475 86811557101813613068292213)
              ·
                refine ⟨8138583478295026225152395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86811557101813613068292213 8138583478295026225152395)
                ·
                  refine ⟨12207875217442539337728593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8138583478295026225152395 12207875217442539337728593)
                  ·
                    refine ⟨9155906413081904503296445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12207875217442539337728593 9155906413081904503296445)
                    ·
                      refine ⟨3433464904905714188736167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9155906413081904503296445 3433464904905714188736167)
                      ·
                        rfl

theorem cell23_6686649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_6686649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686649 prefixEnd_6686649 := by exact prefixLift 6686649
  have htrace : WordTrace (prefixWord ++ tailWord_6686649) baseStart_6686649 baseEnd_6686649 := by
    simpa [prefixWord, tailWord_6686649, baseEnd_6686649] using wordTrace_append hprefix tailTrace_6686649
  have hstable : (prefixWord ++ tailWord_6686649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686649).length < 2 ^ (prefixWord ++ tailWord_6686649).sum := by decide
  have hdescent : baseEnd_6686649 < baseStart_6686649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686665 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 1, 9]
def baseStart_6686665 : Nat := 118140960795 + 6686665 * 2 ^ 59
def prefixEnd_6686665 : Nat := 4983230072969 + 3 ^ 40 * 6686665 * 2
def baseEnd_6686665 : Nat := 1144491040198728708712031

theorem tailTrace_6686665 : CollatzResearch.WordTrace tailWord_6686665 prefixEnd_6686665 1144491040198728708712031 := by
  unfold tailWord_6686665
  simp only [CollatzResearch.WordTrace]
  refine ⟨243882708320362171308525449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162588472213574780872350299 243882708320362171308525449)
  ·
    refine ⟨182912031240271628481394087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243882708320362171308525449 182912031240271628481394087)
    ·
      refine ⟨274368046860407442722091131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182912031240271628481394087 274368046860407442722091131)
      ·
        refine ⟨411552070290611164083136697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274368046860407442722091131 411552070290611164083136697)
        ·
          refine ⟨308664052717958373062352523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411552070290611164083136697 308664052717958373062352523)
          ·
            refine ⟨462996079076937559593528785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308664052717958373062352523 462996079076937559593528785)
            ·
              refine ⟨347247059307703169695146589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462996079076937559593528785 347247059307703169695146589)
              ·
                refine ⟨130217647240388688635679971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347247059307703169695146589 130217647240388688635679971)
                ·
                  refine ⟨195326470860583032953519957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130217647240388688635679971 195326470860583032953519957)
                  ·
                    refine ⟨1144491040198728708712031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 195326470860583032953519957 1144491040198728708712031)
                    ·
                      rfl

theorem cell23_6686665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_6686665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686665 prefixEnd_6686665 := by exact prefixLift 6686665
  have htrace : WordTrace (prefixWord ++ tailWord_6686665) baseStart_6686665 baseEnd_6686665 := by
    simpa [prefixWord, tailWord_6686665, baseEnd_6686665] using wordTrace_append hprefix tailTrace_6686665
  have hstable : (prefixWord ++ tailWord_6686665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686665).length < 2 ^ (prefixWord ++ tailWord_6686665).sum := by decide
  have hdescent : baseEnd_6686665 < baseStart_6686665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686769 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 2, 3, 3]
def baseStart_6686769 : Nat := 118140960795 + 6686769 * 2 ^ 59
def prefixEnd_6686769 : Nat := 4983230072969 + 3 ^ 40 * 6686769 * 2
def baseEnd_6686769 : Nat := 3433526522584253719235615

theorem tailTrace_6686769 : CollatzResearch.WordTrace tailWord_6686769 prefixEnd_6686769 3433526522584253719235615 := by
  unfold tailWord_6686769
  simp only [CollatzResearch.WordTrace]
  refine ⟨243886501511985397070311361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162591001007990264713540907 243886501511985397070311361)
  ·
    refine ⟨182914876133989047802733521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243886501511985397070311361 182914876133989047802733521)
    ·
      refine ⟨137186157100491785852050141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182914876133989047802733521 137186157100491785852050141)
      ·
        refine ⟨51444808912684419694518803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137186157100491785852050141 51444808912684419694518803)
        ·
          refine ⟨77167213369026629541778205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51444808912684419694518803 77167213369026629541778205)
          ·
            refine ⟨28937705013384986078166827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77167213369026629541778205 28937705013384986078166827)
            ·
              refine ⟨43406557520077479117250241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28937705013384986078166827 43406557520077479117250241)
              ·
                refine ⟨32554918140058109337937681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43406557520077479117250241 32554918140058109337937681)
                ·
                  refine ⟨24416188605043582003453261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32554918140058109337937681 24416188605043582003453261)
                  ·
                    refine ⟨9156070726891343251294973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24416188605043582003453261 9156070726891343251294973)
                    ·
                      refine ⟨3433526522584253719235615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9156070726891343251294973 3433526522584253719235615)
                      ·
                        rfl

theorem cell23_6686769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_6686769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686769 prefixEnd_6686769 := by exact prefixLift 6686769
  have htrace : WordTrace (prefixWord ++ tailWord_6686769) baseStart_6686769 baseEnd_6686769 := by
    simpa [prefixWord, tailWord_6686769, baseEnd_6686769] using wordTrace_append hprefix tailTrace_6686769
  have hstable : (prefixWord ++ tailWord_6686769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686769).length < 2 ^ (prefixWord ++ tailWord_6686769).sum := by decide
  have hdescent : baseEnd_6686769 < baseStart_6686769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686770 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2]
def baseStart_6686770 : Nat := 118140960795 + 6686770 * 2 ^ 59
def prefixEnd_6686770 : Nat := 4983230072969 + 3 ^ 40 * 6686770 * 2
def baseEnd_6686770 : Nat := 3433527036064908215323111

theorem tailTrace_6686770 : CollatzResearch.WordTrace tailWord_6686770 prefixEnd_6686770 3433527036064908215323111 := by
  unfold tailWord_6686770
  simp only [CollatzResearch.WordTrace]
  refine ⟨60971634496245443560274441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162591025323321182827398509 60971634496245443560274441)
  ·
    refine ⟨45728725872184082670205831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60971634496245443560274441 45728725872184082670205831)
    ·
      refine ⟨68593088808276124005308747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45728725872184082670205831 68593088808276124005308747)
      ·
        refine ⟨102889633212414186007963121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68593088808276124005308747 102889633212414186007963121)
        ·
          refine ⟨77167224909310639505972341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102889633212414186007963121 77167224909310639505972341)
          ·
            refine ⟨7234427335247872453684907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77167224909310639505972341 7234427335247872453684907)
            ·
              refine ⟨10851641002871808680527361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7234427335247872453684907 10851641002871808680527361)
              ·
                refine ⟨8138730752153856510395521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10851641002871808680527361 8138730752153856510395521)
                ·
                  refine ⟨6104048064115392382796641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8138730752153856510395521 6104048064115392382796641)
                  ·
                    refine ⟨4578036048086544287097481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6104048064115392382796641 4578036048086544287097481)
                    ·
                      refine ⟨3433527036064908215323111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578036048086544287097481 3433527036064908215323111)
                      ·
                        rfl

theorem cell23_6686770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_6686770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686770 prefixEnd_6686770 := by exact prefixLift 6686770
  have htrace : WordTrace (prefixWord ++ tailWord_6686770) baseStart_6686770 baseEnd_6686770 := by
    simpa [prefixWord, tailWord_6686770, baseEnd_6686770] using wordTrace_append hprefix tailTrace_6686770
  have hstable : (prefixWord ++ tailWord_6686770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686770).length < 2 ^ (prefixWord ++ tailWord_6686770).sum := by decide
  have hdescent : baseEnd_6686770 < baseStart_6686770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686809 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 4]
def baseStart_6686809 : Nat := 118140960795 + 6686809 * 2 ^ 59
def prefixEnd_6686809 : Nat := 4983230072969 + 3 ^ 40 * 6686809 * 2
def baseEnd_6686809 : Nat := 3433547061810433562735431

theorem tailTrace_6686809 : CollatzResearch.WordTrace tailWord_6686809 prefixEnd_6686809 3433547061810433562735431 := by
  unfold tailWord_6686809
  simp only [CollatzResearch.WordTrace]
  refine ⟨243887960431840483901767481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162591973621226989267844987 243887960431840483901767481)
  ·
    refine ⟨182915970323880362926325611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243887960431840483901767481 182915970323880362926325611)
    ·
      refine ⟨274373955485820544389488417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182915970323880362926325611 274373955485820544389488417)
      ·
        refine ⟨205780466614365408292116313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274373955485820544389488417 205780466614365408292116313)
        ·
          refine ⟨154335349960774056219087235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205780466614365408292116313 154335349960774056219087235)
          ·
            refine ⟨231503024941161084328630853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154335349960774056219087235 231503024941161084328630853)
            ·
              refine ⟨43406817176467703311618285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231503024941161084328630853 43406817176467703311618285)
              ·
                refine ⟨16277556441175388741856857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43406817176467703311618285 16277556441175388741856857)
                ·
                  refine ⟨12208167330881541556392643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16277556441175388741856857 12208167330881541556392643)
                  ·
                    refine ⟨18312250996322312334588965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12208167330881541556392643 18312250996322312334588965)
                    ·
                      refine ⟨3433547061810433562735431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18312250996322312334588965 3433547061810433562735431)
                      ·
                        rfl

theorem cell23_6686809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_6686809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686809 prefixEnd_6686809 := by exact prefixLift 6686809
  have htrace : WordTrace (prefixWord ++ tailWord_6686809) baseStart_6686809 baseEnd_6686809 := by
    simpa [prefixWord, tailWord_6686809, baseEnd_6686809] using wordTrace_append hprefix tailTrace_6686809
  have hstable : (prefixWord ++ tailWord_6686809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686809).length < 2 ^ (prefixWord ++ tailWord_6686809).sum := by decide
  have hdescent : baseEnd_6686809 < baseStart_6686809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686819 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 5, 4]
def baseStart_6686819 : Nat := 118140960795 + 6686819 * 2 ^ 59
def prefixEnd_6686819 : Nat := 4983230072969 + 3 ^ 40 * 6686819 * 2
def baseEnd_6686819 : Nat := 1144517398872326174536795

theorem tailTrace_6686819 : CollatzResearch.WordTrace tailWord_6686819 prefixEnd_6686819 1144517398872326174536795 := by
  unfold tailWord_6686819
  simp only [CollatzResearch.WordTrace]
  refine ⟨243888325161804255609631511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162592216774536170406421007 243888325161804255609631511)
  ·
    refine ⟨365832487742706383414447267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243888325161804255609631511 365832487742706383414447267)
    ·
      refine ⟨548748731614059575121670901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365832487742706383414447267 548748731614059575121670901)
      ·
        refine ⟨51445193588818085167656647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 548748731614059575121670901 51445193588818085167656647)
        ·
          refine ⟨77167790383227127751484971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51445193588818085167656647 77167790383227127751484971)
          ·
            refine ⟨115751685574840691627227457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77167790383227127751484971 115751685574840691627227457)
            ·
              refine ⟨86813764181130518720420593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115751685574840691627227457 86813764181130518720420593)
              ·
                refine ⟨65110323135847889040315445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86813764181130518720420593 65110323135847889040315445)
                ·
                  refine ⟨6104092793985739597529573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65110323135847889040315445 6104092793985739597529573)
                  ·
                    refine ⟨1144517398872326174536795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6104092793985739597529573 1144517398872326174536795)
                    ·
                      rfl

theorem cell23_6686819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 4].length) (baseStart_6686819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686819 prefixEnd_6686819 := by exact prefixLift 6686819
  have htrace : WordTrace (prefixWord ++ tailWord_6686819) baseStart_6686819 baseEnd_6686819 := by
    simpa [prefixWord, tailWord_6686819, baseEnd_6686819] using wordTrace_append hprefix tailTrace_6686819
  have hstable : (prefixWord ++ tailWord_6686819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686819).length < 2 ^ (prefixWord ++ tailWord_6686819).sum := by decide
  have hdescent : baseEnd_6686819 < baseStart_6686819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686910 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_6686910 : Nat := 118140960795 + 6686910 * 2 ^ 59
def prefixEnd_6686910 : Nat := 4983230072969 + 3 ^ 40 * 6686910 * 2
def baseEnd_6686910 : Nat := 3433598923356537667572467

theorem tailTrace_6686910 : CollatzResearch.WordTrace tailWord_6686910 prefixEnd_6686910 3433598923356537667572467 := by
  unfold tailWord_6686910
  simp only [CollatzResearch.WordTrace]
  refine ⟨30486455525559322268899273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162594429469649718767462789 30486455525559322268899273)
  ·
    refine ⟨22864841644169491701674455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30486455525559322268899273 22864841644169491701674455)
    ·
      refine ⟨34297262466254237552511683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22864841644169491701674455 34297262466254237552511683)
      ·
        refine ⟨51445893699381356328767525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34297262466254237552511683 51445893699381356328767525)
        ·
          refine ⟨9646105068634004311643911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51445893699381356328767525 9646105068634004311643911)
          ·
            refine ⟨14469157602951006467465867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9646105068634004311643911 14469157602951006467465867)
            ·
              refine ⟨21703736404426509701198801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14469157602951006467465867 21703736404426509701198801)
              ·
                refine ⟨16277802303319882275899101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21703736404426509701198801 16277802303319882275899101)
                ·
                  refine ⟨6104175863744955853462163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16277802303319882275899101 6104175863744955853462163)
                  ·
                    refine ⟨9156263795617433780193245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6104175863744955853462163 9156263795617433780193245)
                    ·
                      refine ⟨3433598923356537667572467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9156263795617433780193245 3433598923356537667572467)
                      ·
                        rfl

theorem cell23_6686910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_6686910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686910 prefixEnd_6686910 := by exact prefixLift 6686910
  have htrace : WordTrace (prefixWord ++ tailWord_6686910) baseStart_6686910 baseEnd_6686910 := by
    simpa [prefixWord, tailWord_6686910, baseEnd_6686910] using wordTrace_append hprefix tailTrace_6686910
  have hstable : (prefixWord ++ tailWord_6686910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686910).length < 2 ^ (prefixWord ++ tailWord_6686910).sum := by decide
  have hdescent : baseEnd_6686910 < baseStart_6686910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686926 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_6686926 : Nat := 118140960795 + 6686926 * 2 ^ 59
def prefixEnd_6686926 : Nat := 4983230072969 + 3 ^ 40 * 6686926 * 2
def baseEnd_6686926 : Nat := 1144535713015669868324131

theorem tailTrace_6686926 : CollatzResearch.WordTrace tailWord_6686926 prefixEnd_6686926 1144535713015669868324131 := by
  unfold tailWord_6686926
  simp only [CollatzResearch.WordTrace]
  refine ⟨30486528471552076610472079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162594818514944408589184421 30486528471552076610472079)
  ·
    refine ⟨45729792707328114915708119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30486528471552076610472079 45729792707328114915708119)
    ·
      refine ⟨68594689060992172373562179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45729792707328114915708119 68594689060992172373562179)
      ·
        refine ⟨102892033591488258560343269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68594689060992172373562179 102892033591488258560343269)
        ·
          refine ⟨19292256298404048480064363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102892033591488258560343269 19292256298404048480064363)
          ·
            refine ⟨28938384447606072720096545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19292256298404048480064363 28938384447606072720096545)
            ·
              refine ⟨21703788335704554540072409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28938384447606072720096545 21703788335704554540072409)
              ·
                refine ⟨16277841251778415905054307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21703788335704554540072409 16277841251778415905054307)
                ·
                  refine ⟨24416761877667623857581461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16277841251778415905054307 24416761877667623857581461)
                  ·
                    refine ⟨1144535713015669868324131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24416761877667623857581461 1144535713015669868324131)
                    ·
                      rfl

theorem cell23_6686926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_6686926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686926 prefixEnd_6686926 := by exact prefixLift 6686926
  have htrace : WordTrace (prefixWord ++ tailWord_6686926) baseStart_6686926 baseEnd_6686926 := by
    simpa [prefixWord, tailWord_6686926, baseEnd_6686926] using wordTrace_append hprefix tailTrace_6686926
  have hstable : (prefixWord ++ tailWord_6686926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686926).length < 2 ^ (prefixWord ++ tailWord_6686926).sum := by decide
  have hdescent : baseEnd_6686926 < baseStart_6686926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686930 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_6686930 : Nat := 118140960795 + 6686930 * 2 ^ 59
def prefixEnd_6686930 : Nat := 4983230072969 + 3 ^ 40 * 6686930 * 2
def baseEnd_6686930 : Nat := 1144536397656542529774125

theorem tailTrace_6686930 : CollatzResearch.WordTrace tailWord_6686930 prefixEnd_6686930 1144536397656542529774125 := by
  unfold tailWord_6686930
  simp only [CollatzResearch.WordTrace]
  refine ⟨60973093416100530391730561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162594915776268081044614829 60973093416100530391730561)
  ·
    refine ⟨45729820062075397793797921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60973093416100530391730561 45729820062075397793797921)
    ·
      refine ⟨34297365046556548345348441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45729820062075397793797921 34297365046556548345348441)
      ·
        refine ⟨25723023784917411259011331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34297365046556548345348441 25723023784917411259011331)
        ·
          refine ⟨38584535677376116888516997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25723023784917411259011331 38584535677376116888516997)
          ·
            refine ⟨7234600439508021916596937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38584535677376116888516997 7234600439508021916596937)
            ·
              refine ⟨5425950329631016437447703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7234600439508021916596937 5425950329631016437447703)
              ·
                refine ⟨8138925494446524656171555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425950329631016437447703 8138925494446524656171555)
                ·
                  refine ⟨12208388241669786984257333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8138925494446524656171555 12208388241669786984257333)
                  ·
                    refine ⟨1144536397656542529774125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12208388241669786984257333 1144536397656542529774125)
                    ·
                      rfl

theorem cell23_6686930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_6686930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686930 prefixEnd_6686930 := by exact prefixLift 6686930
  have htrace : WordTrace (prefixWord ++ tailWord_6686930) baseStart_6686930 baseEnd_6686930 := by
    simpa [prefixWord, tailWord_6686930, baseEnd_6686930] using wordTrace_append hprefix tailTrace_6686930
  have hstable : (prefixWord ++ tailWord_6686930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686930).length < 2 ^ (prefixWord ++ tailWord_6686930).sum := by decide
  have hdescent : baseEnd_6686930 < baseStart_6686930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686979 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 5]
def baseStart_6686979 : Nat := 118140960795 + 6686979 * 2 ^ 59
def prefixEnd_6686979 : Nat := 4983230072969 + 3 ^ 40 * 6686979 * 2
def baseEnd_6686979 : Nat := 3433634353521697897609649

theorem tailTrace_6686979 : CollatzResearch.WordTrace tailWord_6686979 prefixEnd_6686979 3433634353521697897609649 := by
  unfold tailWord_6686979
  simp only [CollatzResearch.WordTrace]
  refine ⟨243894160841224602935455991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162596107227483068623637327 243894160841224602935455991)
  ·
    refine ⟨365841241261836904403183987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243894160841224602935455991 365841241261836904403183987)
    ·
      refine ⟨548761861892755356604775981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365841241261836904403183987 548761861892755356604775981)
      ·
        refine ⟨205785698209783258726790993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548761861892755356604775981 205785698209783258726790993)
        ·
          refine ⟨154339273657337444045093245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205785698209783258726790993 154339273657337444045093245)
          ·
            refine ⟨57877227621501541516909967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154339273657337444045093245 57877227621501541516909967)
            ·
              refine ⟨86815841432252312275364951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57877227621501541516909967 86815841432252312275364951)
              ·
                refine ⟨130223762148378468413047427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86815841432252312275364951 130223762148378468413047427)
                ·
                  refine ⟨195335643222567702619571141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130223762148378468413047427 195335643222567702619571141)
                  ·
                    refine ⟨36625433104231444241169589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195335643222567702619571141 36625433104231444241169589)
                    ·
                      refine ⟨3433634353521697897609649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36625433104231444241169589 3433634353521697897609649)
                      ·
                        rfl

theorem cell23_6686979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_6686979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686979 prefixEnd_6686979 := by exact prefixLift 6686979
  have htrace : WordTrace (prefixWord ++ tailWord_6686979) baseStart_6686979 baseEnd_6686979 := by
    simpa [prefixWord, tailWord_6686979, baseEnd_6686979] using wordTrace_append hprefix tailTrace_6686979
  have hstable : (prefixWord ++ tailWord_6686979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686979).length < 2 ^ (prefixWord ++ tailWord_6686979).sum := by decide
  have hdescent : baseEnd_6686979 < baseStart_6686979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6686984 : List Nat := [2, 1, 3, 2, 3, 3, 1, 3, 1, 2, 2]
def baseStart_6686984 : Nat := 118140960795 + 6686984 * 2 ^ 59
def prefixEnd_6686984 : Nat := 4983230072969 + 3 ^ 40 * 6686984 * 2
def baseEnd_6686984 : Nat := 3433636920924970378047127

theorem tailTrace_6686984 : CollatzResearch.WordTrace tailWord_6686984 prefixEnd_6686984 3433636920924970378047127 := by
  unfold tailWord_6686984
  simp only [CollatzResearch.WordTrace]
  refine ⟨121947171603103244394694003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162596228804137659192925337 121947171603103244394694003)
  ·
    refine ⟨182920757404654866592041005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121947171603103244394694003 182920757404654866592041005)
    ·
      refine ⟨68595284026745574972015377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182920757404654866592041005 68595284026745574972015377)
      ·
        refine ⟨51446463020059181229011533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68595284026745574972015377 51446463020059181229011533)
        ·
          refine ⟨19292423632522192960879325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51446463020059181229011533 19292423632522192960879325)
          ·
            refine ⟨7234658862195822360329747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19292423632522192960879325 7234658862195822360329747)
            ·
              refine ⟨10851988293293733540494621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7234658862195822360329747 10851988293293733540494621)
              ·
                refine ⟨4069495609985150077685483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10851988293293733540494621 4069495609985150077685483)
                ·
                  refine ⟨6104243414977725116528225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069495609985150077685483 6104243414977725116528225)
                  ·
                    refine ⟨4578182561233293837396169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6104243414977725116528225 4578182561233293837396169)
                    ·
                      refine ⟨3433636920924970378047127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578182561233293837396169 3433636920924970378047127)
                      ·
                        rfl

theorem cell23_6686984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_6686984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6686984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6686984 prefixEnd_6686984 := by exact prefixLift 6686984
  have htrace : WordTrace (prefixWord ++ tailWord_6686984) baseStart_6686984 baseEnd_6686984 := by
    simpa [prefixWord, tailWord_6686984, baseEnd_6686984] using wordTrace_append hprefix tailTrace_6686984
  have hstable : (prefixWord ++ tailWord_6686984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6686984).length < 2 ^ (prefixWord ++ tailWord_6686984).sum := by decide
  have hdescent : baseEnd_6686984 < baseStart_6686984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6686984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687057 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 2, 2, 2]
def baseStart_6687057 : Nat := 118140960795 + 6687057 * 2 ^ 59
def prefixEnd_6687057 : Nat := 4983230072969 + 3 ^ 40 * 6687057 * 2
def baseEnd_6687057 : Nat := 3433674405012748592434291

theorem tailTrace_6687057 : CollatzResearch.WordTrace tailWord_6687057 prefixEnd_6687057 3433674405012748592434291 := by
  unfold tailWord_6687057
  simp only [CollatzResearch.WordTrace]
  refine ⟨243897005734942022256795425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162598003823294681504530283 243897005734942022256795425)
  ·
    refine ⟨182922754301206516692596569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243897005734942022256795425 182922754301206516692596569)
    ·
      refine ⟨137192065725904887519447427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182922754301206516692596569 137192065725904887519447427)
      ·
        refine ⟨205788098588857331279171141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137192065725904887519447427 205788098588857331279171141)
        ·
          refine ⟨38585268485410749614844589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205788098588857331279171141 38585268485410749614844589)
          ·
            refine ⟨14469475682029031105566721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38585268485410749614844589 14469475682029031105566721)
            ·
              refine ⟨10852106761521773329175041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14469475682029031105566721 10852106761521773329175041)
              ·
                refine ⟨8139080071141329996881281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10852106761521773329175041 8139080071141329996881281)
                ·
                  refine ⟨6104310053355997497660961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8139080071141329996881281 6104310053355997497660961)
                  ·
                    refine ⟨4578232540016998123245721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6104310053355997497660961 4578232540016998123245721)
                    ·
                      refine ⟨3433674405012748592434291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578232540016998123245721 3433674405012748592434291)
                      ·
                        rfl

theorem cell23_6687057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 2, 2].length) (baseStart_6687057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687057 prefixEnd_6687057 := by exact prefixLift 6687057
  have htrace : WordTrace (prefixWord ++ tailWord_6687057) baseStart_6687057 baseEnd_6687057 := by
    simpa [prefixWord, tailWord_6687057, baseEnd_6687057] using wordTrace_append hprefix tailTrace_6687057
  have hstable : (prefixWord ++ tailWord_6687057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687057).length < 2 ^ (prefixWord ++ tailWord_6687057).sum := by decide
  have hdescent : baseEnd_6687057 < baseStart_6687057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687063 : List Nat := [1, 1, 3, 2, 3, 1, 3, 4, 5]
def baseStart_6687063 : Nat := 118140960795 + 6687063 * 2 ^ 59
def prefixEnd_6687063 : Nat := 4983230072969 + 3 ^ 40 * 6687063 * 2
def baseEnd_6687063 : Nat := 381519720655186174328807

theorem tailTrace_6687063 : CollatzResearch.WordTrace tailWord_6687063 prefixEnd_6687063 381519720655186174328807 := by
  unfold tailWord_6687063
  simp only [CollatzResearch.WordTrace]
  refine ⟨243897224572920285281513843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162598149715280190187675895 243897224572920285281513843)
  ·
    refine ⟨365845836859380427922270765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243897224572920285281513843 365845836859380427922270765)
    ·
      refine ⟨137192188822267660470851537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365845836859380427922270765 137192188822267660470851537)
      ·
        refine ⟨102894141616700745353138653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137192188822267660470851537 102894141616700745353138653)
        ·
          refine ⟨38585303106262779507426995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102894141616700745353138653 38585303106262779507426995)
          ·
            refine ⟨57877954659394169261140493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38585303106262779507426995 57877954659394169261140493)
            ·
              refine ⟨21704232997272813472927685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57877954659394169261140493 21704232997272813472927685)
              ·
                refine ⟨4069543686988652526173941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21704232997272813472927685 4069543686988652526173941)
                ·
                  refine ⟨381519720655186174328807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4069543686988652526173941 381519720655186174328807)
                  ·
                    rfl

theorem cell23_6687063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 5].length) (baseStart_6687063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687063 prefixEnd_6687063 := by exact prefixLift 6687063
  have htrace : WordTrace (prefixWord ++ tailWord_6687063) baseStart_6687063 baseEnd_6687063 := by
    simpa [prefixWord, tailWord_6687063, baseEnd_6687063] using wordTrace_append hprefix tailTrace_6687063
  have hstable : (prefixWord ++ tailWord_6687063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687063).length < 2 ^ (prefixWord ++ tailWord_6687063).sum := by decide
  have hdescent : baseEnd_6687063 < baseStart_6687063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687076 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_6687076 : Nat := 118140960795 + 6687076 * 2 ^ 59
def prefixEnd_6687076 : Nat := 4983230072969 + 3 ^ 40 * 6687076 * 2
def baseEnd_6687076 : Nat := 1144561387048394672698901

theorem tailTrace_6687076 : CollatzResearch.WordTrace tailWord_6687076 prefixEnd_6687076 1144561387048394672698901 := by
  unfold tailWord_6687076
  simp only [CollatzResearch.WordTrace]
  refine ⟨121948849360936594250868541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162598465814582125667824721 121948849360936594250868541)
  ·
    refine ⟨45730818510351222844075703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121948849360936594250868541 45730818510351222844075703)
    ·
      refine ⟨68596227765526834266113555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45730818510351222844075703 68596227765526834266113555)
      ·
        refine ⟨102894341648290251399170333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68596227765526834266113555 102894341648290251399170333)
        ·
          refine ⟨38585378118108844274688875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102894341648290251399170333 38585378118108844274688875)
          ·
            refine ⟨57878067177163266412033313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38585378118108844274688875 57878067177163266412033313)
            ·
              refine ⟨43408550382872449809024985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57878067177163266412033313 43408550382872449809024985)
              ·
                refine ⟨32556412787154337356768739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43408550382872449809024985 32556412787154337356768739)
                ·
                  refine ⟨48834619180731506035153109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32556412787154337356768739 48834619180731506035153109)
                  ·
                    refine ⟨1144561387048394672698901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48834619180731506035153109 1144561387048394672698901)
                    ·
                      rfl

theorem cell23_6687076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_6687076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687076 prefixEnd_6687076 := by exact prefixLift 6687076
  have htrace : WordTrace (prefixWord ++ tailWord_6687076) baseStart_6687076 baseEnd_6687076 := by
    simpa [prefixWord, tailWord_6687076, baseEnd_6687076] using wordTrace_append hprefix tailTrace_6687076
  have hstable : (prefixWord ++ tailWord_6687076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687076).length < 2 ^ (prefixWord ++ tailWord_6687076).sum := by decide
  have hdescent : baseEnd_6687076 < baseStart_6687076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687093 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_6687093 : Nat := 118140960795 + 6687093 * 2 ^ 59
def prefixEnd_6687093 : Nat := 4983230072969 + 3 ^ 40 * 6687093 * 2
def baseEnd_6687093 : Nat := 1144564296772103483861375

theorem tailTrace_6687093 : CollatzResearch.WordTrace tailWord_6687093 prefixEnd_6687093 1144564296772103483861375 := by
  unfold tailWord_6687093
  simp only [CollatzResearch.WordTrace]
  refine ⟨243898318762811600405105933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162598879175207733603403955 243898318762811600405105933)
  ·
    refine ⟨91461869536054350151914725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243898318762811600405105933 91461869536054350151914725)
    ·
      refine ⟨17149100538010190653484011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91461869536054350151914725 17149100538010190653484011)
      ·
        refine ⟨25723650807015285980226017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17149100538010190653484011 25723650807015285980226017)
        ·
          refine ⟨19292738105261464485169513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25723650807015285980226017 19292738105261464485169513)
          ·
            refine ⟨14469553578946098363877135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19292738105261464485169513 14469553578946098363877135)
            ·
              refine ⟨21704330368419147545815703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14469553578946098363877135 21704330368419147545815703)
              ·
                refine ⟨32556495552628721318723555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21704330368419147545815703 32556495552628721318723555)
                ·
                  refine ⟨48834743328943081978085333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32556495552628721318723555 48834743328943081978085333)
                  ·
                    refine ⟨1144564296772103483861375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48834743328943081978085333 1144564296772103483861375)
                    ·
                      rfl

theorem cell23_6687093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_6687093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687093 prefixEnd_6687093 := by exact prefixLift 6687093
  have htrace : WordTrace (prefixWord ++ tailWord_6687093) baseStart_6687093 baseEnd_6687093 := by
    simpa [prefixWord, tailWord_6687093, baseEnd_6687093] using wordTrace_append hprefix tailTrace_6687093
  have hstable : (prefixWord ++ tailWord_6687093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687093).length < 2 ^ (prefixWord ++ tailWord_6687093).sum := by decide
  have hdescent : baseEnd_6687093 < baseStart_6687093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687130 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2]
def baseStart_6687130 : Nat := 118140960795 + 6687130 * 2 ^ 59
def prefixEnd_6687130 : Nat := 4983230072969 + 3 ^ 40 * 6687130 * 2
def baseEnd_6687130 : Nat := 3433711889100526806821455

theorem tailTrace_6687130 : CollatzResearch.WordTrace tailWord_6687130 prefixEnd_6687130 3433711889100526806821455 := by
  unfold tailWord_6687130
  simp only [CollatzResearch.WordTrace]
  refine ⟨60974917065919388931050711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162599778842451703816135229 60974917065919388931050711)
  ·
    refine ⟨91462375598879083396576067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60974917065919388931050711 91462375598879083396576067)
    ·
      refine ⟨137193563398318625094864101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91462375598879083396576067 137193563398318625094864101)
      ·
        refine ⟨25723793137184742205287019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137193563398318625094864101 25723793137184742205287019)
        ·
          refine ⟨38585689705777113307930529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25723793137184742205287019 38585689705777113307930529)
          ·
            refine ⟨28939267279332834980947897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38585689705777113307930529 28939267279332834980947897)
            ·
              refine ⟨21704450459499626235710923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28939267279332834980947897 21704450459499626235710923)
              ·
                refine ⟨32556675689249439353566385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21704450459499626235710923 32556675689249439353566385)
                ·
                  refine ⟨24417506766937079515174789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32556675689249439353566385 24417506766937079515174789)
                  ·
                    refine ⟨4578282518800702409095273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24417506766937079515174789 4578282518800702409095273)
                    ·
                      refine ⟨3433711889100526806821455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578282518800702409095273 3433711889100526806821455)
                      ·
                        rfl

theorem cell23_6687130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_6687130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687130 prefixEnd_6687130 := by exact prefixLift 6687130
  have htrace : WordTrace (prefixWord ++ tailWord_6687130) baseStart_6687130 baseEnd_6687130 := by
    simpa [prefixWord, tailWord_6687130, baseEnd_6687130] using wordTrace_append hprefix tailTrace_6687130
  have hstable : (prefixWord ++ tailWord_6687130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687130).length < 2 ^ (prefixWord ++ tailWord_6687130).sum := by decide
  have hdescent : baseEnd_6687130 < baseStart_6687130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687173 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 2, 9, 2]
def baseStart_6687173 : Nat := 118140960795 + 6687173 * 2 ^ 59
def prefixEnd_6687173 : Nat := 4983230072969 + 3 ^ 40 * 6687173 * 2
def baseEnd_6687173 : Nat := 3433733968768670138583757

theorem tailTrace_6687173 : CollatzResearch.WordTrace tailWord_6687173 prefixEnd_6687173 3433733968768670138583757 := by
  unfold tailWord_6687173
  simp only [CollatzResearch.WordTrace]
  refine ⟨243901236602521774068018173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162600824401681182712012115 243901236602521774068018173)
  ·
    refine ⟨91462963725945665275506815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243901236602521774068018173 91462963725945665275506815)
    ·
      refine ⟨137194445588918497913260223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91462963725945665275506815 137194445588918497913260223)
      ·
        refine ⟨205791668383377746869890335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137194445588918497913260223 205791668383377746869890335)
        ·
          refine ⟨308687502575066620304835503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205791668383377746869890335 308687502575066620304835503)
          ·
            refine ⟨463031253862599930457253255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308687502575066620304835503 463031253862599930457253255)
            ·
              refine ⟨694546880793899895685879883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463031253862599930457253255 694546880793899895685879883)
              ·
                refine ⟨1041820321190849843528819825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694546880793899895685879883 1041820321190849843528819825)
                ·
                  refine ⟨781365240893137382646614869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1041820321190849843528819825 781365240893137382646614869)
                  ·
                    refine ⟨4578311958358226851445009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 781365240893137382646614869 4578311958358226851445009)
                    ·
                      refine ⟨3433733968768670138583757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578311958358226851445009 3433733968768670138583757)
                      ·
                        rfl

theorem cell23_6687173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 9, 2].length) (baseStart_6687173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687173 prefixEnd_6687173 := by exact prefixLift 6687173
  have htrace : WordTrace (prefixWord ++ tailWord_6687173) baseStart_6687173 baseEnd_6687173 := by
    simpa [prefixWord, tailWord_6687173, baseEnd_6687173] using wordTrace_append hprefix tailTrace_6687173
  have hstable : (prefixWord ++ tailWord_6687173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687173).length < 2 ^ (prefixWord ++ tailWord_6687173).sum := by decide
  have hdescent : baseEnd_6687173 < baseStart_6687173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687207 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_6687207 : Nat := 118140960795 + 6687207 * 2 ^ 59
def prefixEnd_6687207 : Nat := 4983230072969 + 3 ^ 40 * 6687207 * 2
def baseEnd_6687207 : Nat := 3433751427110923005558601

theorem tailTrace_6687207 : CollatzResearch.WordTrace tailWord_6687207 prefixEnd_6687207 3433751427110923005558601 := by
  unfold tailWord_6687207
  simp only [CollatzResearch.WordTrace]
  refine ⟨243902476684398597874755875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162601651122932398583170583 243902476684398597874755875)
  ·
    refine ⟨365853715026597896812133813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243902476684398597874755875 365853715026597896812133813)
    ·
      refine ⟨34298785783743552826137545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 365853715026597896812133813 34298785783743552826137545)
      ·
        refine ⟨25724089337807664619603159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34298785783743552826137545 25724089337807664619603159)
        ·
          refine ⟨38586134006711496929404739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25724089337807664619603159 38586134006711496929404739)
          ·
            refine ⟨57879201010067245394107109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38586134006711496929404739 57879201010067245394107109)
            ·
              refine ⟨10852350189387608511395083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57879201010067245394107109 10852350189387608511395083)
              ·
                refine ⟨16278525284081412767092625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10852350189387608511395083 16278525284081412767092625)
                ·
                  refine ⟨12208893963061059575319469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16278525284081412767092625 12208893963061059575319469)
                  ·
                    refine ⟨4578335236147897340744801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12208893963061059575319469 4578335236147897340744801)
                    ·
                      refine ⟨3433751427110923005558601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4578335236147897340744801 3433751427110923005558601)
                      ·
                        rfl

theorem cell23_6687207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_6687207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687207 prefixEnd_6687207 := by exact prefixLift 6687207
  have htrace : WordTrace (prefixWord ++ tailWord_6687207) baseStart_6687207 baseEnd_6687207 := by
    simpa [prefixWord, tailWord_6687207, baseEnd_6687207] using wordTrace_append hprefix tailTrace_6687207
  have hstable : (prefixWord ++ tailWord_6687207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687207).length < 2 ^ (prefixWord ++ tailWord_6687207).sum := by decide
  have hdescent : baseEnd_6687207 < baseStart_6687207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687243 : List Nat := [1, 1, 1, 1, 7, 1, 3, 8]
def baseStart_6687243 : Nat := 118140960795 + 6687243 * 2 ^ 59
def prefixEnd_6687243 : Nat := 4983230072969 + 3 ^ 40 * 6687243 * 2
def baseEnd_6687243 : Nat := 127176663422758698692905

theorem tailTrace_6687243 : CollatzResearch.WordTrace tailWord_6687243 prefixEnd_6687243 127176663422758698692905 := by
  unfold tailWord_6687243
  simp only [CollatzResearch.WordTrace]
  refine ⟨243903789712268176023066383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162602526474845450682044255 243903789712268176023066383)
  ·
    refine ⟨365855684568402264034599575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243903789712268176023066383 365855684568402264034599575)
    ·
      refine ⟨548783526852603396051899363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365855684568402264034599575 548783526852603396051899363)
      ·
        refine ⟨823175290278905094077849045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548783526852603396051899363 823175290278905094077849045)
        ·
          refine ⟨19293170865911838142449587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 823175290278905094077849045 19293170865911838142449587)
          ·
            refine ⟨28939756298867757213674381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19293170865911838142449587 28939756298867757213674381)
            ·
              refine ⟨10852408612075408955127893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28939756298867757213674381 10852408612075408955127893)
              ·
                refine ⟨127176663422758698692905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10852408612075408955127893 127176663422758698692905)
                ·
                  rfl

theorem cell23_6687243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 8].length) (baseStart_6687243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687243 prefixEnd_6687243 := by exact prefixLift 6687243
  have htrace : WordTrace (prefixWord ++ tailWord_6687243) baseStart_6687243 baseEnd_6687243 := by
    simpa [prefixWord, tailWord_6687243, baseEnd_6687243] using wordTrace_append hprefix tailTrace_6687243
  have hstable : (prefixWord ++ tailWord_6687243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687243).length < 2 ^ (prefixWord ++ tailWord_6687243).sum := by decide
  have hdescent : baseEnd_6687243 < baseStart_6687243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6687260 : List Nat := [2, 2, 3, 1, 2, 3, 3, 7]
def baseStart_6687260 : Nat := 118140960795 + 6687260 * 2 ^ 59
def prefixEnd_6687260 : Nat := 4983230072969 + 3 ^ 40 * 6687260 * 2
def baseEnd_6687260 : Nat := 127176986725393011044291

theorem tailTrace_6687260 : CollatzResearch.WordTrace tailWord_6687260 prefixEnd_6687260 127176986725393011044291 := by
  unfold tailWord_6687260
  simp only [CollatzResearch.WordTrace]
  refine ⟨121952204876603293963217617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162602939835471058617623489 121952204876603293963217617)
  ·
    refine ⟨91464153657452470472413213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121952204876603293963217617 91464153657452470472413213)
    ·
      refine ⟨34299057621544676427154955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91464153657452470472413213 34299057621544676427154955)
      ·
        refine ⟨51448586432317014640732433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34299057621544676427154955 51448586432317014640732433)
        ·
          refine ⟨38586439824237760980549325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51448586432317014640732433 38586439824237760980549325)
          ·
            refine ⟨14469914934089160367705997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38586439824237760980549325 14469914934089160367705997)
            ·
              refine ⟨5426218100283435137889749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14469914934089160367705997 5426218100283435137889749)
              ·
                refine ⟨127176986725393011044291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5426218100283435137889749 127176986725393011044291)
                ·
                  rfl

theorem cell23_6687260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 7].length) (baseStart_6687260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6687260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6687260 prefixEnd_6687260 := by exact prefixLift 6687260
  have htrace : WordTrace (prefixWord ++ tailWord_6687260) baseStart_6687260 baseEnd_6687260 := by
    simpa [prefixWord, tailWord_6687260, baseEnd_6687260] using wordTrace_append hprefix tailTrace_6687260
  have hstable : (prefixWord ++ tailWord_6687260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6687260).length < 2 ^ (prefixWord ++ tailWord_6687260).sum := by decide
  have hdescent : baseEnd_6687260 < baseStart_6687260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6687260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
