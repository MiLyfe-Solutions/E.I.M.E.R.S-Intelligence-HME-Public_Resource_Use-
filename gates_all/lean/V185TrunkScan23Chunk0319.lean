import V185TrunkScan23Chunk0318

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1886434 : List Nat := [3, 3, 4, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1886434 : Nat := 118140960795 + 1886434 * 2 ^ 59
def prefixEnd_1886434 : Nat := 4983230072969 + 3 ^ 40 * 1886434 * 2
def baseEnd_1886434 : Nat := 968647364983777551999455

theorem tailTrace_1886434 : CollatzResearch.WordTrace tailWord_1886434 prefixEnd_1886434 968647364983777551999455 := by
  unfold tailWord_1886434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17200975111944817530616589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45869266965186180081644237 17200975111944817530616589)
  ·
    refine ⟨6450365666979306573981221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17200975111944817530616589 6450365666979306573981221)
    ·
      refine ⟨1209443562558619982621479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6450365666979306573981221 1209443562558619982621479)
      ·
        refine ⟨1814165343837929973932219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209443562558619982621479 1814165343837929973932219)
        ·
          refine ⟨2721248015756894960898329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814165343837929973932219 2721248015756894960898329)
          ·
            refine ⟨2040936011817671220673747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2721248015756894960898329 2040936011817671220673747)
            ·
              refine ⟨3061404017726506831010621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040936011817671220673747 3061404017726506831010621)
              ·
                refine ⟨1148026506647440061628983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3061404017726506831010621 1148026506647440061628983)
                ·
                  refine ⟨1722039759971160092443475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1148026506647440061628983 1722039759971160092443475)
                  ·
                    refine ⟨2583059639956740138665213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1722039759971160092443475 2583059639956740138665213)
                    ·
                      refine ⟨968647364983777551999455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2583059639956740138665213 968647364983777551999455)
                      ·
                        rfl

theorem cell23_1886434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1886434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886434 prefixEnd_1886434 := by exact prefixLift 1886434
  have htrace : WordTrace (prefixWord ++ tailWord_1886434) baseStart_1886434 baseEnd_1886434 := by
    simpa [prefixWord, tailWord_1886434, baseEnd_1886434] using wordTrace_append hprefix tailTrace_1886434
  have hstable : (prefixWord ++ tailWord_1886434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886434).length < 2 ^ (prefixWord ++ tailWord_1886434).sum := by decide
  have hdescent : baseEnd_1886434 < baseStart_1886434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886440 : List Nat := [2, 1, 4, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_1886440 : Nat := 118140960795 + 1886440 * 2 ^ 59
def prefixEnd_1886440 : Nat := 4983230072969 + 3 ^ 40 * 1886440 * 2
def baseEnd_1886440 : Nat := 968650445867704528524427

theorem tailTrace_1886440 : CollatzResearch.WordTrace tailWord_1886440 prefixEnd_1886440 968650445867704528524427 := by
  unfold tailWord_1886440
  simp only [CollatzResearch.WordTrace]
  refine ⟨34402059642878766573592387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45869412857171688764789849 34402059642878766573592387)
  ·
    refine ⟨51603089464318149860388581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34402059642878766573592387 51603089464318149860388581)
    ·
      refine ⟨9675579274559653098822859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51603089464318149860388581 9675579274559653098822859)
      ·
        refine ⟨14513368911839479648234289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9675579274559653098822859 14513368911839479648234289)
        ·
          refine ⟨10885026683879609736175717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14513368911839479648234289 10885026683879609736175717)
          ·
            refine ⟨2040942503227426825532947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10885026683879609736175717 2040942503227426825532947)
            ·
              refine ⟨3061413754841140238299421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040942503227426825532947 3061413754841140238299421)
              ·
                refine ⟨1148030158065427589362283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3061413754841140238299421 1148030158065427589362283)
                ·
                  refine ⟨1722045237098141384043425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1148030158065427589362283 1722045237098141384043425)
                  ·
                    refine ⟨1291533927823606038032569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1722045237098141384043425 1291533927823606038032569)
                    ·
                      refine ⟨968650445867704528524427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291533927823606038032569 968650445867704528524427)
                      ·
                        rfl

theorem cell23_1886440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_1886440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886440 prefixEnd_1886440 := by exact prefixLift 1886440
  have htrace : WordTrace (prefixWord ++ tailWord_1886440) baseStart_1886440 baseEnd_1886440 := by
    simpa [prefixWord, tailWord_1886440, baseEnd_1886440] using wordTrace_append hprefix tailTrace_1886440
  have hstable : (prefixWord ++ tailWord_1886440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886440).length < 2 ^ (prefixWord ++ tailWord_1886440).sum := by decide
  have hdescent : baseEnd_1886440 < baseStart_1886440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886473 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 2, 1, 3]
def baseStart_1886473 : Nat := 118140960795 + 1886473 * 2 ^ 59
def prefixEnd_1886473 : Nat := 4983230072969 + 3 ^ 40 * 1886473 * 2
def baseEnd_1886473 : Nat := 968667390729302899411775

theorem tailTrace_1886473 : CollatzResearch.WordTrace tailWord_1886473 prefixEnd_1886473 968667390729302899411775 := by
  unfold tailWord_1886473
  simp only [CollatzResearch.WordTrace]
  refine ⟨68805322894637979783136073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45870215263091986522090715 68805322894637979783136073)
  ·
    refine ⟨51603992170978484837352055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68805322894637979783136073 51603992170978484837352055)
    ·
      refine ⟨77405988256467727256028083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51603992170978484837352055 77405988256467727256028083)
      ·
        refine ⟨116108982384701590884042125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77405988256467727256028083 116108982384701590884042125)
        ·
          refine ⟨43540868394263096581515797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116108982384701590884042125 43540868394263096581515797)
          ·
            refine ⟨2040978205981082652258553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43540868394263096581515797 2040978205981082652258553)
            ·
              refine ⟨1530733654485811989193915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2040978205981082652258553 1530733654485811989193915)
              ·
                refine ⟨2296100481728717983790873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1530733654485811989193915 2296100481728717983790873)
                ·
                  refine ⟨1722075361296538487843155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2296100481728717983790873 1722075361296538487843155)
                  ·
                    refine ⟨2583113041944807731764733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1722075361296538487843155 2583113041944807731764733)
                    ·
                      refine ⟨968667390729302899411775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2583113041944807731764733 968667390729302899411775)
                      ·
                        rfl

theorem cell23_1886473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 2, 1, 3].length) (baseStart_1886473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886473 prefixEnd_1886473 := by exact prefixLift 1886473
  have htrace : WordTrace (prefixWord ++ tailWord_1886473) baseStart_1886473 baseEnd_1886473 := by
    simpa [prefixWord, tailWord_1886473, baseEnd_1886473] using wordTrace_append hprefix tailTrace_1886473
  have hstable : (prefixWord ++ tailWord_1886473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886473).length < 2 ^ (prefixWord ++ tailWord_1886473).sum := by decide
  have hdescent : baseEnd_1886473 < baseStart_1886473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886492 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1886492 : Nat := 118140960795 + 1886492 * 2 ^ 59
def prefixEnd_1886492 : Nat := 4983230072969 + 3 ^ 40 * 1886492 * 2
def baseEnd_1886492 : Nat := 968677146861738325074187

theorem tailTrace_1886492 : CollatzResearch.WordTrace tailWord_1886492 prefixEnd_1886492 968677146861738325074187 := by
  unfold tailWord_1886492
  simp only [CollatzResearch.WordTrace]
  refine ⟨34403007940784573014038865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45870677254379430685385153 34403007940784573014038865)
  ·
    refine ⟨25802255955588429760529149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34403007940784573014038865 25802255955588429760529149)
    ·
      refine ⟨9675845983345661160198431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25802255955588429760529149 9675845983345661160198431)
      ·
        refine ⟨14513768975018491740297647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9675845983345661160198431 14513768975018491740297647)
        ·
          refine ⟨21770653462527737610446471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14513768975018491740297647 21770653462527737610446471)
          ·
            refine ⟨32655980193791606415669707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21770653462527737610446471 32655980193791606415669707)
            ·
              refine ⟨48983970290687409623504561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32655980193791606415669707 48983970290687409623504561)
              ·
                refine ⟨36737977718015557217628421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48983970290687409623504561 36737977718015557217628421)
                ·
                  refine ⟨6888370822127916978305329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36737977718015557217628421 6888370822127916978305329)
                  ·
                    refine ⟨5166278116595937733728997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6888370822127916978305329 5166278116595937733728997)
                    ·
                      refine ⟨968677146861738325074187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5166278116595937733728997 968677146861738325074187)
                      ·
                        rfl

theorem cell23_1886492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1886492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886492 prefixEnd_1886492 := by exact prefixLift 1886492
  have htrace : WordTrace (prefixWord ++ tailWord_1886492) baseStart_1886492 baseEnd_1886492 := by
    simpa [prefixWord, tailWord_1886492, baseEnd_1886492] using wordTrace_append hprefix tailTrace_1886492
  have hstable : (prefixWord ++ tailWord_1886492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886492).length < 2 ^ (prefixWord ++ tailWord_1886492).sum := by decide
  have hdescent : baseEnd_1886492 < baseStart_1886492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886496 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 1, 4, 2]
def baseStart_1886496 : Nat := 118140960795 + 1886496 * 2 ^ 59
def prefixEnd_1886496 : Nat := 4983230072969 + 3 ^ 40 * 1886496 * 2
def baseEnd_1886496 : Nat := 968679200784356309424169

theorem tailTrace_1886496 : CollatzResearch.WordTrace tailWord_1886496 prefixEnd_1886496 968679200784356309424169 := by
  unfold tailWord_1886496
  simp only [CollatzResearch.WordTrace]
  refine ⟨34403080886777327355611671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45870774515703103140815561 34403080886777327355611671)
  ·
    refine ⟨51604621330165991033417507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34403080886777327355611671 51604621330165991033417507)
    ·
      refine ⟨77406931995248986550126261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51604621330165991033417507 77406931995248986550126261)
      ·
        refine ⟨7256899874554592489074337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77406931995248986550126261 7256899874554592489074337)
        ·
          refine ⟨5442674905915944366805753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7256899874554592489074337 5442674905915944366805753)
          ·
            refine ⟨4082006179436958275104315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5442674905915944366805753 4082006179436958275104315)
            ·
              refine ⟨6123009269155437412656473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4082006179436958275104315 6123009269155437412656473)
              ·
                refine ⟨4592256951866578059492355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6123009269155437412656473 4592256951866578059492355)
                ·
                  refine ⟨6888385427799867089238533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4592256951866578059492355 6888385427799867089238533)
                  ·
                    refine ⟨1291572267712475079232225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6888385427799867089238533 1291572267712475079232225)
                    ·
                      refine ⟨968679200784356309424169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291572267712475079232225 968679200784356309424169)
                      ·
                        rfl

theorem cell23_1886496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_1886496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886496 prefixEnd_1886496 := by exact prefixLift 1886496
  have htrace : WordTrace (prefixWord ++ tailWord_1886496) baseStart_1886496 baseEnd_1886496 := by
    simpa [prefixWord, tailWord_1886496, baseEnd_1886496] using wordTrace_append hprefix tailTrace_1886496
  have hstable : (prefixWord ++ tailWord_1886496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886496).length < 2 ^ (prefixWord ++ tailWord_1886496).sum := by decide
  have hdescent : baseEnd_1886496 < baseStart_1886496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886542 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_1886542 : Nat := 118140960795 + 1886542 * 2 ^ 59
def prefixEnd_1886542 : Nat := 4983230072969 + 3 ^ 40 * 1886542 * 2
def baseEnd_1886542 : Nat := 968702820894463129448957

theorem tailTrace_1886542 : CollatzResearch.WordTrace tailWord_1886542 prefixEnd_1886542 968702820894463129448957 := by
  unfold tailWord_1886542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600979941423500570924735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45871893020925336378265253 8600979941423500570924735)
  ·
    refine ⟨12901469912135250856387103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8600979941423500570924735 12901469912135250856387103)
    ·
      refine ⟨19352204868202876284580655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12901469912135250856387103 19352204868202876284580655)
      ·
        refine ⟨29028307302304314426870983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19352204868202876284580655 29028307302304314426870983)
        ·
          refine ⟨43542460953456471640306475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29028307302304314426870983 43542460953456471640306475)
          ·
            refine ⟨65313691430184707460459713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43542460953456471640306475 65313691430184707460459713)
            ·
              refine ⟨48985268572638530595344785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65313691430184707460459713 48985268572638530595344785)
              ·
                refine ⟨36738951429478897946508589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48985268572638530595344785 36738951429478897946508589)
                ·
                  refine ⟨13777106786054586729940721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36738951429478897946508589 13777106786054586729940721)
                  ·
                    refine ⟨10332830089540940047455541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13777106786054586729940721 10332830089540940047455541)
                    ·
                      refine ⟨968702820894463129448957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10332830089540940047455541 968702820894463129448957)
                      ·
                        rfl

theorem cell23_1886542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_1886542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886542 prefixEnd_1886542 := by exact prefixLift 1886542
  have htrace : WordTrace (prefixWord ++ tailWord_1886542) baseStart_1886542 baseEnd_1886542 := by
    simpa [prefixWord, tailWord_1886542, baseEnd_1886542] using wordTrace_append hprefix tailTrace_1886542
  have hstable : (prefixWord ++ tailWord_1886542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886542).length < 2 ^ (prefixWord ++ tailWord_1886542).sum := by decide
  have hdescent : baseEnd_1886542 < baseStart_1886542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886549 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 1, 7]
def baseStart_1886549 : Nat := 118140960795 + 1886549 * 2 ^ 59
def prefixEnd_1886549 : Nat := 4983230072969 + 3 ^ 40 * 1886549 * 2
def baseEnd_1886549 : Nat := 322902138419681534020475

theorem tailTrace_1886549 : CollatzResearch.WordTrace tailWord_1886549 prefixEnd_1886549 322902138419681534020475 := by
  unfold tailWord_1886549
  simp only [CollatzResearch.WordTrace]
  refine ⟨68808094842362644762902701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45872063228241763175268467 68808094842362644762902701)
  ·
    refine ⟨25803035565885991786088513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68808094842362644762902701 25803035565885991786088513)
    ·
      refine ⟨19352276674414493839566385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25803035565885991786088513 19352276674414493839566385)
      ·
        refine ⟨14514207505810870379674789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19352276674414493839566385 14514207505810870379674789)
        ·
          refine ⟨2721413907339538196189023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14514207505810870379674789 2721413907339538196189023)
          ·
            refine ⟨4082120861009307294283535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721413907339538196189023 4082120861009307294283535)
            ·
              refine ⟨6123181291513960941425303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4082120861009307294283535 6123181291513960941425303)
              ·
                refine ⟨9184771937270941412137955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6123181291513960941425303 9184771937270941412137955)
                ·
                  refine ⟨13777157905906412118206933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9184771937270941412137955 13777157905906412118206933)
                  ·
                    refine ⟨322902138419681534020475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13777157905906412118206933 322902138419681534020475)
                    ·
                      rfl

theorem cell23_1886549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_1886549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886549 prefixEnd_1886549 := by exact prefixLift 1886549
  have htrace : WordTrace (prefixWord ++ tailWord_1886549) baseStart_1886549 baseEnd_1886549 := by
    simpa [prefixWord, tailWord_1886549, baseEnd_1886549] using wordTrace_append hprefix tailTrace_1886549
  have hstable : (prefixWord ++ tailWord_1886549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886549).length < 2 ^ (prefixWord ++ tailWord_1886549).sum := by decide
  have hdescent : baseEnd_1886549 < baseStart_1886549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886569 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 4, 4, 2]
def baseStart_1886569 : Nat := 118140960795 + 1886569 * 2 ^ 59
def prefixEnd_1886569 : Nat := 4983230072969 + 3 ^ 40 * 1886569 * 2
def baseEnd_1886569 : Nat := 968716684872134523811333

theorem tailTrace_1886569 : CollatzResearch.WordTrace tailWord_1886569 prefixEnd_1886569 968716684872134523811333 := by
  unfold tailWord_1886569
  simp only [CollatzResearch.WordTrace]
  refine ⟨68808824302290188178630761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45872549534860125452420507 68808824302290188178630761)
  ·
    refine ⟨51606618226717641133973071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68808824302290188178630761 51606618226717641133973071)
    ·
      refine ⟨77409927340076461700959607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51606618226717641133973071 77409927340076461700959607)
      ·
        refine ⟨116114891010114692551439411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77409927340076461700959607 116114891010114692551439411)
        ·
          refine ⟨174172336515172038827159117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116114891010114692551439411 174172336515172038827159117)
          ·
            refine ⟨65314626193189514560184669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174172336515172038827159117 65314626193189514560184669)
            ·
              refine ⟨24492984822446067960069251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65314626193189514560184669 24492984822446067960069251)
              ·
                refine ⟨36739477233669101940103877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24492984822446067960069251 36739477233669101940103877)
                ·
                  refine ⟨6888651981312956613769477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36739477233669101940103877 6888651981312956613769477)
                  ·
                    refine ⟨1291622246496179365081777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6888651981312956613769477 1291622246496179365081777)
                    ·
                      refine ⟨968716684872134523811333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291622246496179365081777 968716684872134523811333)
                      ·
                        rfl

theorem cell23_1886569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 4, 2].length) (baseStart_1886569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886569 prefixEnd_1886569 := by exact prefixLift 1886569
  have htrace : WordTrace (prefixWord ++ tailWord_1886569) baseStart_1886569 baseEnd_1886569 := by
    simpa [prefixWord, tailWord_1886569, baseEnd_1886569] using wordTrace_append hprefix tailTrace_1886569
  have hstable : (prefixWord ++ tailWord_1886569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886569).length < 2 ^ (prefixWord ++ tailWord_1886569).sum := by decide
  have hdescent : baseEnd_1886569 < baseStart_1886569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886589 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_1886589 : Nat := 118140960795 + 1886589 * 2 ^ 59
def prefixEnd_1886589 : Nat := 4983230072969 + 3 ^ 40 * 1886589 * 2
def baseEnd_1886589 : Nat := 968726954485224445561241

theorem tailTrace_1886589 : CollatzResearch.WordTrace tailWord_1886589 prefixEnd_1886589 968726954485224445561241 := by
  unfold tailWord_1886589
  simp only [CollatzResearch.WordTrace]
  refine ⟨68809553762217731594358821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45873035841478487729572547 68809553762217731594358821)
  ·
    refine ⟨12901791330415824673942279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68809553762217731594358821 12901791330415824673942279)
    ·
      refine ⟨19352686995623737010913419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12901791330415824673942279 19352686995623737010913419)
      ·
        refine ⟨29029030493435605516370129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19352686995623737010913419 29029030493435605516370129)
        ·
          refine ⟨21771772870076704137277597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29029030493435605516370129 21771772870076704137277597)
          ·
            refine ⟨8164414826278764051479099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21771772870076704137277597 8164414826278764051479099)
            ·
              refine ⟨12246622239418146077218649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8164414826278764051479099 12246622239418146077218649)
              ·
                refine ⟨9184966679563609557913987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12246622239418146077218649 9184966679563609557913987)
                ·
                  refine ⟨13777450019345414336870981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9184966679563609557913987 13777450019345414336870981)
                  ·
                    refine ⟨2583271878627265188163309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13777450019345414336870981 2583271878627265188163309)
                    ·
                      refine ⟨968726954485224445561241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2583271878627265188163309 968726954485224445561241)
                      ·
                        rfl

theorem cell23_1886589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_1886589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886589 prefixEnd_1886589 := by exact prefixLift 1886589
  have htrace : WordTrace (prefixWord ++ tailWord_1886589) baseStart_1886589 baseEnd_1886589 := by
    simpa [prefixWord, tailWord_1886589, baseEnd_1886589] using wordTrace_append hprefix tailTrace_1886589
  have hstable : (prefixWord ++ tailWord_1886589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886589).length < 2 ^ (prefixWord ++ tailWord_1886589).sum := by decide
  have hdescent : baseEnd_1886589 < baseStart_1886589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886606 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1886606 : Nat := 118140960795 + 1886606 * 2 ^ 59
def prefixEnd_1886606 : Nat := 4983230072969 + 3 ^ 40 * 1886606 * 2
def baseEnd_1886606 : Nat := 968735683656350879048663

theorem tailTrace_1886606 : CollatzResearch.WordTrace tailWord_1886606 prefixEnd_1886606 968735683656350879048663 := by
  unfold tailWord_1886606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601271725394517937215959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45873449202104095665151781 8601271725394517937215959)
  ·
    refine ⟨12901907588091776905823939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8601271725394517937215959 12901907588091776905823939)
    ·
      refine ⟨19352861382137665358735909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12901907588091776905823939 19352861382137665358735909)
      ·
        refine ⟨3628661509150812254762983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19352861382137665358735909 3628661509150812254762983)
        ·
          refine ⟨5442992263726218382144475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628661509150812254762983 5442992263726218382144475)
          ·
            refine ⟨8164488395589327573216713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5442992263726218382144475 8164488395589327573216713)
            ·
              refine ⟨6123366296691995679912535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8164488395589327573216713 6123366296691995679912535)
              ·
                refine ⟨9185049445037993519868803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6123366296691995679912535 9185049445037993519868803)
                ·
                  refine ⟨13777574167556990279803205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9185049445037993519868803 13777574167556990279803205)
                  ·
                    refine ⟨2583295156416935677463101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13777574167556990279803205 2583295156416935677463101)
                    ·
                      refine ⟨968735683656350879048663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2583295156416935677463101 968735683656350879048663)
                      ·
                        rfl

theorem cell23_1886606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1886606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886606 prefixEnd_1886606 := by exact prefixLift 1886606
  have htrace : WordTrace (prefixWord ++ tailWord_1886606) baseStart_1886606 baseEnd_1886606 := by
    simpa [prefixWord, tailWord_1886606, baseEnd_1886606] using wordTrace_append hprefix tailTrace_1886606
  have hstable : (prefixWord ++ tailWord_1886606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886606).length < 2 ^ (prefixWord ++ tailWord_1886606).sum := by decide
  have hdescent : baseEnd_1886606 < baseStart_1886606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886657 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1886657 : Nat := 118140960795 + 1886657 * 2 ^ 59
def prefixEnd_1886657 : Nat := 4983230072969 + 3 ^ 40 * 1886657 * 2
def baseEnd_1886657 : Nat := 968761871169730179510929

theorem tailTrace_1886657 : CollatzResearch.WordTrace tailWord_1886657 prefixEnd_1886657 968761871169730179510929 := by
  unfold tailWord_1886657
  simp only [CollatzResearch.WordTrace]
  refine ⟨68812033925971379207834225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45874689283980919471889483 68812033925971379207834225)
  ·
    refine ⟨51609025444478534405875669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68812033925971379207834225 51609025444478534405875669)
    ·
      refine ⟨1209586533854965650137711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 51609025444478534405875669 1209586533854965650137711)
      ·
        refine ⟨1814379800782448475206567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209586533854965650137711 1814379800782448475206567)
        ·
          refine ⟨2721569701173672712809851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814379800782448475206567 2721569701173672712809851)
          ·
            refine ⟨4082354551760509069214777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721569701173672712809851 4082354551760509069214777)
            ·
              refine ⟨3061765913820381801911083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4082354551760509069214777 3061765913820381801911083)
              ·
                refine ⟨4592648870730572702866625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061765913820381801911083 4592648870730572702866625)
                ·
                  refine ⟨3444486653047929527149969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4592648870730572702866625 3444486653047929527149969)
                  ·
                    refine ⟨2583364989785947145362477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3444486653047929527149969 2583364989785947145362477)
                    ·
                      refine ⟨968761871169730179510929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2583364989785947145362477 968761871169730179510929)
                      ·
                        rfl

theorem cell23_1886657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1886657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886657 prefixEnd_1886657 := by exact prefixLift 1886657
  have htrace : WordTrace (prefixWord ++ tailWord_1886657) baseStart_1886657 baseEnd_1886657 := by
    simpa [prefixWord, tailWord_1886657, baseEnd_1886657] using wordTrace_append hprefix tailTrace_1886657
  have hstable : (prefixWord ++ tailWord_1886657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886657).length < 2 ^ (prefixWord ++ tailWord_1886657).sum := by decide
  have hdescent : baseEnd_1886657 < baseStart_1886657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886663 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 2, 3, 2]
def baseStart_1886663 : Nat := 118140960795 + 1886663 * 2 ^ 59
def prefixEnd_1886663 : Nat := 4983230072969 + 3 ^ 40 * 1886663 * 2
def baseEnd_1886663 : Nat := 968764952053657156035901

theorem tailTrace_1886663 : CollatzResearch.WordTrace tailWord_1886663 prefixEnd_1886663 968764952053657156035901 := by
  unfold tailWord_1886663
  simp only [CollatzResearch.WordTrace]
  refine ⟨68812252763949642232552643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45874835175966428155035095 68812252763949642232552643)
  ·
    refine ⟨103218379145924463348828965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68812252763949642232552643 103218379145924463348828965)
    ·
      refine ⟨19353446089860836877905431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103218379145924463348828965 19353446089860836877905431)
      ·
        refine ⟨29030169134791255316858147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19353446089860836877905431 29030169134791255316858147)
        ·
          refine ⟨43545253702186882975287221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29030169134791255316858147 43545253702186882975287221)
          ·
            refine ⟨4082367534580020278933177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43545253702186882975287221 4082367534580020278933177)
            ·
              refine ⟨3061775650935015209199883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4082367534580020278933177 3061775650935015209199883)
              ·
                refine ⟨4592663476402522813799825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061775650935015209199883 4592663476402522813799825)
                ·
                  refine ⟨3444497607301892110349869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4592663476402522813799825 3444497607301892110349869)
                  ·
                    refine ⟨1291686602738209541381201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3444497607301892110349869 1291686602738209541381201)
                    ·
                      refine ⟨968764952053657156035901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291686602738209541381201 968764952053657156035901)
                      ·
                        rfl

theorem cell23_1886663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_1886663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886663 prefixEnd_1886663 := by exact prefixLift 1886663
  have htrace : WordTrace (prefixWord ++ tailWord_1886663) baseStart_1886663 baseEnd_1886663 := by
    simpa [prefixWord, tailWord_1886663, baseEnd_1886663] using wordTrace_append hprefix tailTrace_1886663
  have hstable : (prefixWord ++ tailWord_1886663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886663).length < 2 ^ (prefixWord ++ tailWord_1886663).sum := by decide
  have hdescent : baseEnd_1886663 < baseStart_1886663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886687 : List Nat := [1, 1, 2, 3, 3, 4, 2, 2, 1, 1, 3]
def baseStart_1886687 : Nat := 118140960795 + 1886687 * 2 ^ 59
def prefixEnd_1886687 : Nat := 4983230072969 + 3 ^ 40 * 1886687 * 2
def baseEnd_1886687 : Nat := 968777275589365062135791

theorem tailTrace_1886687 : CollatzResearch.WordTrace tailWord_1886687 prefixEnd_1886687 968777275589365062135791 := by
  unfold tailWord_1886687
  simp only [CollatzResearch.WordTrace]
  refine ⟨68813128115862694331426315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45875418743908462887617543 68813128115862694331426315)
  ·
    refine ⟨103219692173794041497139473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68813128115862694331426315 103219692173794041497139473)
    ·
      refine ⟨77414769130345531122854605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103219692173794041497139473 77414769130345531122854605)
      ·
        refine ⟨29030538423879574171070477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77414769130345531122854605 29030538423879574171070477)
        ·
          refine ⟨10886451908954840314151429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29030538423879574171070477 10886451908954840314151429)
          ·
            refine ⟨2041209732929032558903393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10886451908954840314151429 2041209732929032558903393)
            ·
              refine ⟨1530907299696774419177545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041209732929032558903393 1530907299696774419177545)
              ·
                refine ⟨1148180474772580814383159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530907299696774419177545 1148180474772580814383159)
                ·
                  refine ⟨1722270712158871221574739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1148180474772580814383159 1722270712158871221574739)
                  ·
                    refine ⟨2583406068238306832362109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1722270712158871221574739 2583406068238306832362109)
                    ·
                      refine ⟨968777275589365062135791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2583406068238306832362109 968777275589365062135791)
                      ·
                        rfl

theorem cell23_1886687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_1886687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886687 prefixEnd_1886687 := by exact prefixLift 1886687
  have htrace : WordTrace (prefixWord ++ tailWord_1886687) baseStart_1886687 baseEnd_1886687 := by
    simpa [prefixWord, tailWord_1886687, baseEnd_1886687] using wordTrace_append hprefix tailTrace_1886687
  have hstable : (prefixWord ++ tailWord_1886687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886687).length < 2 ^ (prefixWord ++ tailWord_1886687).sum := by decide
  have hdescent : baseEnd_1886687 < baseStart_1886687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886689 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_1886689 : Nat := 118140960795 + 1886689 * 2 ^ 59
def prefixEnd_1886689 : Nat := 4983230072969 + 3 ^ 40 * 1886689 * 2
def baseEnd_1886689 : Nat := 968778302550674054310781

theorem tailTrace_1886689 : CollatzResearch.WordTrace tailWord_1886689 prefixEnd_1886689 968778302550674054310781 := by
  unfold tailWord_1886689
  simp only [CollatzResearch.WordTrace]
  refine ⟨68813201061855448672999121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45875467374570299115332747 68813201061855448672999121)
  ·
    refine ⟨51609900796391586504749341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68813201061855448672999121 51609900796391586504749341)
    ·
      refine ⟨19353712798646844939281003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51609900796391586504749341 19353712798646844939281003)
      ·
        refine ⟨29030569197970267408921505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19353712798646844939281003 29030569197970267408921505)
        ·
          refine ⟨21772926898477700556691129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29030569197970267408921505 21772926898477700556691129)
          ·
            refine ⟨16329695173858275417518347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21772926898477700556691129 16329695173858275417518347)
            ·
              refine ⟨24494542760787413126277521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16329695173858275417518347 24494542760787413126277521)
              ·
                refine ⟨18370907070590559844708141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24494542760787413126277521 18370907070590559844708141)
                ·
                  refine ⟨6889090151471459941765553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18370907070590559844708141 6889090151471459941765553)
                  ·
                    refine ⟨5166817613603594956324165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6889090151471459941765553 5166817613603594956324165)
                    ·
                      refine ⟨968778302550674054310781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5166817613603594956324165 968778302550674054310781)
                      ·
                        rfl

theorem cell23_1886689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_1886689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886689 prefixEnd_1886689 := by exact prefixLift 1886689
  have htrace : WordTrace (prefixWord ++ tailWord_1886689) baseStart_1886689 baseEnd_1886689 := by
    simpa [prefixWord, tailWord_1886689, baseEnd_1886689] using wordTrace_append hprefix tailTrace_1886689
  have hstable : (prefixWord ++ tailWord_1886689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886689).length < 2 ^ (prefixWord ++ tailWord_1886689).sum := by decide
  have hdescent : baseEnd_1886689 < baseStart_1886689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886696 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1886696 : Nat := 118140960795 + 1886696 * 2 ^ 59
def prefixEnd_1886696 : Nat := 4983230072969 + 3 ^ 40 * 1886696 * 2
def baseEnd_1886696 : Nat := 968781896915255526923249

theorem tailTrace_1886696 : CollatzResearch.WordTrace tailWord_1886696 prefixEnd_1886696 968781896915255526923249 := by
  unfold tailWord_1886696
  simp only [CollatzResearch.WordTrace]
  refine ⟨34406728186415044434251971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45875637581886725912335961 34406728186415044434251971)
  ·
    refine ⟨51610092279622566651377957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34406728186415044434251971 51610092279622566651377957)
    ·
      refine ⟨9676892302429231247133367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51610092279622566651377957 9676892302429231247133367)
      ·
        refine ⟨14515338453643846870700051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9676892302429231247133367 14515338453643846870700051)
        ·
          refine ⟨21773007680465770306050077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14515338453643846870700051 21773007680465770306050077)
          ·
            refine ⟨8164877880174663864768779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21773007680465770306050077 8164877880174663864768779)
            ·
              refine ⟨12247316820261995797153169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8164877880174663864768779 12247316820261995797153169)
              ·
                refine ⟨9185487615196496847864877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12247316820261995797153169 9185487615196496847864877)
                ·
                  refine ⟨3444557855698686317949329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9185487615196496847864877 3444557855698686317949329)
                  ·
                    refine ⟨2583418391774014738461997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3444557855698686317949329 2583418391774014738461997)
                    ·
                      refine ⟨968781896915255526923249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2583418391774014738461997 968781896915255526923249)
                      ·
                        rfl

theorem cell23_1886696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1886696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886696 prefixEnd_1886696 := by exact prefixLift 1886696
  have htrace : WordTrace (prefixWord ++ tailWord_1886696) baseStart_1886696 baseEnd_1886696 := by
    simpa [prefixWord, tailWord_1886696, baseEnd_1886696] using wordTrace_append hprefix tailTrace_1886696
  have hstable : (prefixWord ++ tailWord_1886696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886696).length < 2 ^ (prefixWord ++ tailWord_1886696).sum := by decide
  have hdescent : baseEnd_1886696 < baseStart_1886696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886710 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_1886710 : Nat := 118140960795 + 1886710 * 2 ^ 59
def prefixEnd_1886710 : Nat := 4983230072969 + 3 ^ 40 * 1886710 * 2
def baseEnd_1886710 : Nat := 968789085644418472148185

theorem tailTrace_1886710 : CollatzResearch.WordTrace tailWord_1886710 prefixEnd_1886710 968789085644418472148185 := by
  unfold tailWord_1886710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4300872937173710578719599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45875977996519579506342389 4300872937173710578719599)
  ·
    refine ⟨6451309405760565868079399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4300872937173710578719599 6451309405760565868079399)
    ·
      refine ⟨9676964108640848802119099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6451309405760565868079399 9676964108640848802119099)
      ·
        refine ⟨14515446162961273203178649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9676964108640848802119099 14515446162961273203178649)
        ·
          refine ⟨10886584622220954902383987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14515446162961273203178649 10886584622220954902383987)
          ·
            refine ⟨16329876933331432353575981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10886584622220954902383987 16329876933331432353575981)
            ·
              refine ⟨6123703849999287132590993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16329876933331432353575981 6123703849999287132590993)
              ·
                refine ⟨4592777887499465349443245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6123703849999287132590993 4592777887499465349443245)
                ·
                  refine ⟨1722291707812299506041217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4592777887499465349443245 1722291707812299506041217)
                  ·
                    refine ⟨1291718780859224629530913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1722291707812299506041217 1291718780859224629530913)
                    ·
                      refine ⟨968789085644418472148185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291718780859224629530913 968789085644418472148185)
                      ·
                        rfl

theorem cell23_1886710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_1886710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886710 prefixEnd_1886710 := by exact prefixLift 1886710
  have htrace : WordTrace (prefixWord ++ tailWord_1886710) baseStart_1886710 baseEnd_1886710 := by
    simpa [prefixWord, tailWord_1886710, baseEnd_1886710] using wordTrace_append hprefix tailTrace_1886710
  have hstable : (prefixWord ++ tailWord_1886710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886710).length < 2 ^ (prefixWord ++ tailWord_1886710).sum := by decide
  have hdescent : baseEnd_1886710 < baseStart_1886710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886727 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 1, 1, 4]
def baseStart_1886727 : Nat := 118140960795 + 1886727 * 2 ^ 59
def prefixEnd_1886727 : Nat := 4983230072969 + 3 ^ 40 * 1886727 * 2
def baseEnd_1886727 : Nat := 968797814815544905635607

theorem tailTrace_1886727 : CollatzResearch.WordTrace tailWord_1886727 prefixEnd_1886727 968797814815544905635607 := by
  unfold tailWord_1886727
  simp only [CollatzResearch.WordTrace]
  refine ⟨68814587035717781162882435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45876391357145187441921623 68814587035717781162882435)
  ·
    refine ⟨103221880553576671744323653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68814587035717781162882435 103221880553576671744323653)
    ·
      refine ⟨19354102603795625952060685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103221880553576671744323653 19354102603795625952060685)
      ·
        refine ⟨7257788476423359732022757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19354102603795625952060685 7257788476423359732022757)
        ·
          refine ⟨1360835339329379949754267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7257788476423359732022757 1360835339329379949754267)
          ·
            refine ⟨2041253008994069924631401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360835339329379949754267 2041253008994069924631401)
            ·
              refine ⟨1530939756745552443473551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041253008994069924631401 1530939756745552443473551)
              ·
                refine ⟨2296409635118328665210327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1530939756745552443473551 2296409635118328665210327)
                ·
                  refine ⟨3444614452677492997815491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296409635118328665210327 3444614452677492997815491)
                  ·
                    refine ⟨5166921679016239496723237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3444614452677492997815491 5166921679016239496723237)
                    ·
                      refine ⟨968797814815544905635607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5166921679016239496723237 968797814815544905635607)
                      ·
                        rfl

theorem cell23_1886727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_1886727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886727 prefixEnd_1886727 := by exact prefixLift 1886727
  have htrace : WordTrace (prefixWord ++ tailWord_1886727) baseStart_1886727 baseEnd_1886727 := by
    simpa [prefixWord, tailWord_1886727, baseEnd_1886727] using wordTrace_append hprefix tailTrace_1886727
  have hstable : (prefixWord ++ tailWord_1886727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886727).length < 2 ^ (prefixWord ++ tailWord_1886727).sum := by decide
  have hdescent : baseEnd_1886727 < baseStart_1886727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886733 : List Nat := [1, 7, 1, 1, 1, 2, 10]
def baseStart_1886733 : Nat := 118140960795 + 1886733 * 2 ^ 59
def prefixEnd_1886733 : Nat := 4983230072969 + 3 ^ 40 * 1886733 * 2
def baseEnd_1886733 : Nat := 11960504885178665211859

theorem tailTrace_1886733 : CollatzResearch.WordTrace tailWord_1886733 prefixEnd_1886733 11960504885178665211859 := by
  unfold tailWord_1886733
  simp only [CollatzResearch.WordTrace]
  refine ⟨68814805873696044187600853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45876537249130696125067235 68814805873696044187600853)
  ·
    refine ⟨1612847012664751035646895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 68814805873696044187600853 1612847012664751035646895)
    ·
      refine ⟨2419270518997126553470343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612847012664751035646895 2419270518997126553470343)
      ·
        refine ⟨3628905778495689830205515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419270518997126553470343 3628905778495689830205515)
        ·
          refine ⟨5443358667743534745308273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628905778495689830205515 5443358667743534745308273)
          ·
            refine ⟨4082519000807651058981205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5443358667743534745308273 4082519000807651058981205)
            ·
              refine ⟨11960504885178665211859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4082519000807651058981205 11960504885178665211859)
              ·
                rfl

theorem cell23_1886733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 10].length) (baseStart_1886733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886733 prefixEnd_1886733 := by exact prefixLift 1886733
  have htrace : WordTrace (prefixWord ++ tailWord_1886733) baseStart_1886733 baseEnd_1886733 := by
    simpa [prefixWord, tailWord_1886733, baseEnd_1886733] using wordTrace_append hprefix tailTrace_1886733
  have hstable : (prefixWord ++ tailWord_1886733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886733).length < 2 ^ (prefixWord ++ tailWord_1886733).sum := by decide
  have hdescent : baseEnd_1886733 < baseStart_1886733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886760 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1886760 : Nat := 118140960795 + 1886760 * 2 ^ 59
def prefixEnd_1886760 : Nat := 4983230072969 + 3 ^ 40 * 1886760 * 2
def baseEnd_1886760 : Nat := 968814759677143276522955

theorem tailTrace_1886760 : CollatzResearch.WordTrace tailWord_1886760 prefixEnd_1886760 968814759677143276522955 := by
  unfold tailWord_1886760
  simp only [CollatzResearch.WordTrace]
  refine ⟨34407895322299113899416867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45877193763065485199222489 34407895322299113899416867)
  ·
    refine ⟨51611842983448670849125301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34407895322299113899416867 51611842983448670849125301)
    ·
      refine ⟨4838610279698312892105497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51611842983448670849125301 4838610279698312892105497)
      ·
        refine ⟨3628957709773734669079123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4838610279698312892105497 3628957709773734669079123)
        ·
          refine ⟨5443436564660602003618685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628957709773734669079123 5443436564660602003618685)
          ·
            refine ⟨2041288711747725751357007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5443436564660602003618685 2041288711747725751357007)
            ·
              refine ⟨3061933067621588627035511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041288711747725751357007 3061933067621588627035511)
              ·
                refine ⟨4592899601432382940553267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061933067621588627035511 4592899601432382940553267)
                ·
                  refine ⟨6889349402148574410829901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4592899601432382940553267 6889349402148574410829901)
                  ·
                    refine ⟨2583506025805715404061213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6889349402148574410829901 2583506025805715404061213)
                    ·
                      refine ⟨968814759677143276522955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2583506025805715404061213 968814759677143276522955)
                      ·
                        rfl

theorem cell23_1886760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1886760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886760 prefixEnd_1886760 := by exact prefixLift 1886760
  have htrace : WordTrace (prefixWord ++ tailWord_1886760) baseStart_1886760 baseEnd_1886760 := by
    simpa [prefixWord, tailWord_1886760, baseEnd_1886760] using wordTrace_append hprefix tailTrace_1886760
  have hstable : (prefixWord ++ tailWord_1886760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886760).length < 2 ^ (prefixWord ++ tailWord_1886760).sum := by decide
  have hdescent : baseEnd_1886760 < baseStart_1886760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886783 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 6, 2, 2]
def baseStart_1886783 : Nat := 118140960795 + 1886783 * 2 ^ 59
def prefixEnd_1886783 : Nat := 4983230072969 + 3 ^ 40 * 1886783 * 2
def baseEnd_1886783 : Nat := 968826569732196686535349

theorem tailTrace_1886783 : CollatzResearch.WordTrace tailWord_1886783 prefixEnd_1886783 968826569732196686535349 := by
  unfold tailWord_1886783
  simp only [CollatzResearch.WordTrace]
  refine ⟨68816629523514902726921003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45877753015676601817947335 68816629523514902726921003)
  ·
    refine ⟨103224944285272354090381505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68816629523514902726921003 103224944285272354090381505)
    ·
      refine ⟨77418708213954265567786129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103224944285272354090381505 77418708213954265567786129)
      ·
        refine ⟨58064031160465699175839597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77418708213954265567786129 58064031160465699175839597)
        ·
          refine ⟨21774011685174637190939849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58064031160465699175839597 21774011685174637190939849)
          ·
            refine ⟨16330508763880977893204887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21774011685174637190939849 16330508763880977893204887)
            ·
              refine ⟨24495763145821466839807331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16330508763880977893204887 24495763145821466839807331)
              ·
                refine ⟨36743644718732200259710997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24495763145821466839807331 36743644718732200259710997)
                ·
                  refine ⟨1722358346190571887173953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36743644718732200259710997 1722358346190571887173953)
                  ·
                    refine ⟨1291768759642928915380465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1722358346190571887173953 1291768759642928915380465)
                    ·
                      refine ⟨968826569732196686535349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291768759642928915380465 968826569732196686535349)
                      ·
                        rfl

theorem cell23_1886783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 2, 2].length) (baseStart_1886783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886783 prefixEnd_1886783 := by exact prefixLift 1886783
  have htrace : WordTrace (prefixWord ++ tailWord_1886783) baseStart_1886783 baseEnd_1886783 := by
    simpa [prefixWord, tailWord_1886783, baseEnd_1886783] using wordTrace_append hprefix tailTrace_1886783
  have hstable : (prefixWord ++ tailWord_1886783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886783).length < 2 ^ (prefixWord ++ tailWord_1886783).sum := by decide
  have hdescent : baseEnd_1886783 < baseStart_1886783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886816 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 3]
def baseStart_1886816 : Nat := 118140960795 + 1886816 * 2 ^ 59
def prefixEnd_1886816 : Nat := 4983230072969 + 3 ^ 40 * 1886816 * 2
def baseEnd_1886816 : Nat := 968843514593795057422697

theorem tailTrace_1886816 : CollatzResearch.WordTrace tailWord_1886816 prefixEnd_1886816 968843514593795057422697 := by
  unfold tailWord_1886816
  simp only [CollatzResearch.WordTrace]
  refine ⟨34408916566197674681436151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45878555421596899575248201 34408916566197674681436151)
  ·
    refine ⟨51613374849296512022154227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34408916566197674681436151 51613374849296512022154227)
    ·
      refine ⟨77420062273944768033231341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51613374849296512022154227 77420062273944768033231341)
      ·
        refine ⟨29032523352729288012461753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77420062273944768033231341 29032523352729288012461753)
        ·
          refine ⟨21774392514546966009346315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29032523352729288012461753 21774392514546966009346315)
          ·
            refine ⟨32661588771820449014019473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21774392514546966009346315 32661588771820449014019473)
            ·
              refine ⟨24496191578865336760514605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32661588771820449014019473 24496191578865336760514605)
              ·
                refine ⟨9186071842074501285192977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24496191578865336760514605 9186071842074501285192977)
                ·
                  refine ⟨6889553881555875963894733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9186071842074501285192977 6889553881555875963894733)
                  ·
                    refine ⟨2583582705583453486460525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6889553881555875963894733 2583582705583453486460525)
                    ·
                      refine ⟨968843514593795057422697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2583582705583453486460525 968843514593795057422697)
                      ·
                        rfl

theorem cell23_1886816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_1886816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886816 prefixEnd_1886816 := by exact prefixLift 1886816
  have htrace : WordTrace (prefixWord ++ tailWord_1886816) baseStart_1886816 baseEnd_1886816 := by
    simpa [prefixWord, tailWord_1886816, baseEnd_1886816] using wordTrace_append hprefix tailTrace_1886816
  have hstable : (prefixWord ++ tailWord_1886816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886816).length < 2 ^ (prefixWord ++ tailWord_1886816).sum := by decide
  have hdescent : baseEnd_1886816 < baseStart_1886816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886817 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 2, 2, 2]
def baseStart_1886817 : Nat := 118140960795 + 1886817 * 2 ^ 59
def prefixEnd_1886817 : Nat := 4983230072969 + 3 ^ 40 * 1886817 * 2
def baseEnd_1886817 : Nat := 968844028074449553510193

theorem tailTrace_1886817 : CollatzResearch.WordTrace tailWord_1886817 prefixEnd_1886817 968844028074449553510193 := by
  unfold tailWord_1886817
  simp only [CollatzResearch.WordTrace]
  refine ⟨68817869605391726533658705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45878579736927817689105803 68817869605391726533658705)
  ·
    refine ⟨51613402204043794900244029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68817869605391726533658705 51613402204043794900244029)
    ·
      refine ⟨19355025826516423087591511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51613402204043794900244029 19355025826516423087591511)
      ·
        refine ⟨29032538739774634631387267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19355025826516423087591511 29032538739774634631387267)
        ·
          refine ⟨43548808109661951947080901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29032538739774634631387267 43548808109661951947080901)
          ·
            refine ⟨8165401520561615990077669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43548808109661951947080901 8165401520561615990077669)
            ·
              refine ⟨1531012785105302998139563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8165401520561615990077669 1531012785105302998139563)
              ·
                refine ⟨2296519177657954497209345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531012785105302998139563 2296519177657954497209345)
                ·
                  refine ⟨1722389383243465872907009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2296519177657954497209345 1722389383243465872907009)
                  ·
                    refine ⟨1291792037432599404680257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1722389383243465872907009 1291792037432599404680257)
                    ·
                      refine ⟨968844028074449553510193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291792037432599404680257 968844028074449553510193)
                      ·
                        rfl

theorem cell23_1886817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_1886817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886817 prefixEnd_1886817 := by exact prefixLift 1886817
  have htrace : WordTrace (prefixWord ++ tailWord_1886817) baseStart_1886817 baseEnd_1886817 := by
    simpa [prefixWord, tailWord_1886817, baseEnd_1886817] using wordTrace_append hprefix tailTrace_1886817
  have hstable : (prefixWord ++ tailWord_1886817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886817).length < 2 ^ (prefixWord ++ tailWord_1886817).sum := by decide
  have hdescent : baseEnd_1886817 < baseStart_1886817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886873 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 2, 4, 2]
def baseStart_1886873 : Nat := 118140960795 + 1886873 * 2 ^ 59
def prefixEnd_1886873 : Nat := 4983230072969 + 3 ^ 40 * 1886873 * 2
def baseEnd_1886873 : Nat := 968872782991101334409935

theorem tailTrace_1886873 : CollatzResearch.WordTrace tailWord_1886873 prefixEnd_1886873 968872782991101334409935 := by
  unfold tailWord_1886873
  simp only [CollatzResearch.WordTrace]
  refine ⟨68819912093188848097697273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45879941395459232065131515 68819912093188848097697273)
  ·
    refine ⟨51614934069891636073272955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68819912093188848097697273 51614934069891636073272955)
    ·
      refine ⟨77422401104837454109909433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51614934069891636073272955 77422401104837454109909433)
      ·
        refine ⟨58066800828628090582432075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77422401104837454109909433 58066800828628090582432075)
        ·
          refine ⟨87100201242942135873648113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58066800828628090582432075 87100201242942135873648113)
          ·
            refine ⟨65325150932206601905236085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87100201242942135873648113 65325150932206601905236085)
            ·
              refine ⟨6124232899894368928615883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65325150932206601905236085 6124232899894368928615883)
              ·
                refine ⟨9186349349841553392923825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6124232899894368928615883 9186349349841553392923825)
                ·
                  refine ⟨6889762012381165044692869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9186349349841553392923825 6889762012381165044692869)
                  ·
                    refine ⟨1291830377321468445879913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6889762012381165044692869 1291830377321468445879913)
                    ·
                      refine ⟨968872782991101334409935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1291830377321468445879913 968872782991101334409935)
                      ·
                        rfl

theorem cell23_1886873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 4, 2].length) (baseStart_1886873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886873 prefixEnd_1886873 := by exact prefixLift 1886873
  have htrace : WordTrace (prefixWord ++ tailWord_1886873) baseStart_1886873 baseEnd_1886873 := by
    simpa [prefixWord, tailWord_1886873, baseEnd_1886873] using wordTrace_append hprefix tailTrace_1886873
  have hstable : (prefixWord ++ tailWord_1886873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886873).length < 2 ^ (prefixWord ++ tailWord_1886873).sum := by decide
  have hdescent : baseEnd_1886873 < baseStart_1886873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886887 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1886887 : Nat := 118140960795 + 1886887 * 2 ^ 59
def prefixEnd_1886887 : Nat := 4983230072969 + 3 ^ 40 * 1886887 * 2
def baseEnd_1886887 : Nat := 322959990573421426544957

theorem tailTrace_1886887 : CollatzResearch.WordTrace tailWord_1886887 prefixEnd_1886887 322959990573421426544957 := by
  unfold tailWord_1886887
  simp only [CollatzResearch.WordTrace]
  refine ⟨68820422715138128488706915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45880281810092085659137943 68820422715138128488706915)
  ·
    refine ⟨103230634072707192733060373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68820422715138128488706915 103230634072707192733060373)
    ·
      refine ⟨4838935972158149659362205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103230634072707192733060373 4838935972158149659362205)
      ·
        refine ⟨1814600989559306122260827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4838935972158149659362205 1814600989559306122260827)
        ·
          refine ⟨2721901484338959183391241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814600989559306122260827 2721901484338959183391241)
          ·
            refine ⟨2041426113254219387543431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2721901484338959183391241 2041426113254219387543431)
            ·
              refine ⟨3062139169881329081315147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041426113254219387543431 3062139169881329081315147)
              ·
                refine ⟨4593208754821993621972721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062139169881329081315147 4593208754821993621972721)
                ·
                  refine ⟨3444906566116495216479541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4593208754821993621972721 3444906566116495216479541)
                  ·
                    refine ⟨322959990573421426544957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3444906566116495216479541 322959990573421426544957)
                    ·
                      rfl

theorem cell23_1886887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1886887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886887 prefixEnd_1886887 := by exact prefixLift 1886887
  have htrace : WordTrace (prefixWord ++ tailWord_1886887) baseStart_1886887 baseEnd_1886887 := by
    simpa [prefixWord, tailWord_1886887, baseEnd_1886887] using wordTrace_append hprefix tailTrace_1886887
  have hstable : (prefixWord ++ tailWord_1886887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886887).length < 2 ^ (prefixWord ++ tailWord_1886887).sum := by decide
  have hdescent : baseEnd_1886887 < baseStart_1886887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886943 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 1, 5]
def baseStart_1886943 : Nat := 118140960795 + 1886943 * 2 ^ 59
def prefixEnd_1886943 : Nat := 4983230072969 + 3 ^ 40 * 1886943 * 2
def baseEnd_1886943 : Nat := 322969575545638686844871

theorem tailTrace_1886943 : CollatzResearch.WordTrace tailWord_1886943 prefixEnd_1886943 322969575545638686844871 := by
  unfold tailWord_1886943
  simp only [CollatzResearch.WordTrace]
  refine ⟨68822465202935250052745483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45881643468623500035163655 68822465202935250052745483)
  ·
    refine ⟨103233697804402875079118225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68822465202935250052745483 103233697804402875079118225)
    ·
      refine ⟨77425273353302156309338669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103233697804402875079118225 77425273353302156309338669)
      ·
        refine ⟨29034477507488308616002001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77425273353302156309338669 29034477507488308616002001)
        ·
          refine ⟨21775858130616231462001501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29034477507488308616002001 21775858130616231462001501)
          ·
            refine ⟨8165946798981086798250563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21775858130616231462001501 8165946798981086798250563)
            ·
              refine ⟨12248920198471630197375845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8165946798981086798250563 12248920198471630197375845)
              ·
                refine ⟨2296672537213430662007971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12248920198471630197375845 2296672537213430662007971)
                ·
                  refine ⟨3445008805820145993011957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296672537213430662007971 3445008805820145993011957)
                  ·
                    refine ⟨322969575545638686844871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3445008805820145993011957 322969575545638686844871)
                    ·
                      rfl

theorem cell23_1886943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 5].length) (baseStart_1886943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886943 prefixEnd_1886943 := by exact prefixLift 1886943
  have htrace : WordTrace (prefixWord ++ tailWord_1886943) baseStart_1886943 baseEnd_1886943 := by
    simpa [prefixWord, tailWord_1886943, baseEnd_1886943] using wordTrace_append hprefix tailTrace_1886943
  have hstable : (prefixWord ++ tailWord_1886943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886943).length < 2 ^ (prefixWord ++ tailWord_1886943).sum := by decide
  have hdescent : baseEnd_1886943 < baseStart_1886943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886956 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_1886956 : Nat := 118140960795 + 1886956 * 2 ^ 59
def prefixEnd_1886956 : Nat := 4983230072969 + 3 ^ 40 * 1886956 * 2
def baseEnd_1886956 : Nat := 322971800628474836557351

theorem tailTrace_1886956 : CollatzResearch.WordTrace tailWord_1886956 prefixEnd_1886956 322971800628474836557351 := by
  unfold tailWord_1886956
  simp only [CollatzResearch.WordTrace]
  refine ⟨34411469675944076636484361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45881959567925435515312481 34411469675944076636484361)
  ·
    refine ⟨25808602256958057477363271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34411469675944076636484361 25808602256958057477363271)
    ·
      refine ⟨38712903385437086216044907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25808602256958057477363271 38712903385437086216044907)
      ·
        refine ⟨58069355078155629324067361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38712903385437086216044907 58069355078155629324067361)
        ·
          refine ⟨43552016308616721993050521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58069355078155629324067361 43552016308616721993050521)
          ·
            refine ⟨32664012231462541494787891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43552016308616721993050521 32664012231462541494787891)
            ·
              refine ⟨48996018347193812242181837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32664012231462541494787891 48996018347193812242181837)
              ·
                refine ⟨18373506880197679590818189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48996018347193812242181837 18373506880197679590818189)
                ·
                  refine ⟨6890065080074129846556821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18373506880197679590818189 6890065080074129846556821)
                  ·
                    refine ⟨322971800628474836557351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6890065080074129846556821 322971800628474836557351)
                    ·
                      rfl

theorem cell23_1886956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_1886956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886956 prefixEnd_1886956 := by exact prefixLift 1886956
  have htrace : WordTrace (prefixWord ++ tailWord_1886956) baseStart_1886956 baseEnd_1886956 := by
    simpa [prefixWord, tailWord_1886956, baseEnd_1886956] using wordTrace_append hprefix tailTrace_1886956
  have hstable : (prefixWord ++ tailWord_1886956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886956).length < 2 ^ (prefixWord ++ tailWord_1886956).sum := by decide
  have hdescent : baseEnd_1886956 < baseStart_1886956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886973 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_1886973 : Nat := 118140960795 + 1886973 * 2 ^ 59
def prefixEnd_1886973 : Nat := 4983230072969 + 3 ^ 40 * 1886973 * 2
def baseEnd_1886973 : Nat := 322974710352183647719825

theorem tailTrace_1886973 : CollatzResearch.WordTrace tailWord_1886973 prefixEnd_1886973 322974710352183647719825 := by
  unfold tailWord_1886973
  simp only [CollatzResearch.WordTrace]
  refine ⟨68823559392826565176337573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45882372928551043450891715 68823559392826565176337573)
  ·
    refine ⟨12904417386154980970563295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68823559392826565176337573 12904417386154980970563295)
    ·
      refine ⟨19356626079232471455844943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12904417386154980970563295 19356626079232471455844943)
      ·
        refine ⟨29034939118848707183767415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19356626079232471455844943 29034939118848707183767415)
        ·
          refine ⟨43552408678273060775651123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29034939118848707183767415 43552408678273060775651123)
          ·
            refine ⟨65328613017409591163476685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43552408678273060775651123 65328613017409591163476685)
            ·
              refine ⟨24498229881528596686303757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65328613017409591163476685 24498229881528596686303757)
              ·
                refine ⟨9186836205573223757363909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24498229881528596686303757 9186836205573223757363909)
                ·
                  refine ⟨1722531788544979454505733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9186836205573223757363909 1722531788544979454505733)
                  ·
                    refine ⟨322974710352183647719825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1722531788544979454505733 322974710352183647719825)
                    ·
                      rfl

theorem cell23_1886973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_1886973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886973 prefixEnd_1886973 := by exact prefixLift 1886973
  have htrace : WordTrace (prefixWord ++ tailWord_1886973) baseStart_1886973 baseEnd_1886973 := by
    simpa [prefixWord, tailWord_1886973, baseEnd_1886973] using wordTrace_append hprefix tailTrace_1886973
  have hstable : (prefixWord ++ tailWord_1886973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886973).length < 2 ^ (prefixWord ++ tailWord_1886973).sum := by decide
  have hdescent : baseEnd_1886973 < baseStart_1886973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886974 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1886974 : Nat := 118140960795 + 1886974 * 2 ^ 59
def prefixEnd_1886974 : Nat := 4983230072969 + 3 ^ 40 * 1886974 * 2
def baseEnd_1886974 : Nat := 968924644537205439246971

theorem tailTrace_1886974 : CollatzResearch.WordTrace tailWord_1886974 prefixEnd_1886974 968924644537205439246971 := by
  unfold tailWord_1886974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8602949483227867793390497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45882397243881961564749317 8602949483227867793390497)
  ·
    refine ⟨6452212112420900845042873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8602949483227867793390497 6452212112420900845042873)
    ·
      refine ⟨4839159084315675633782155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6452212112420900845042873 4839159084315675633782155)
      ·
        refine ⟨7258738626473513450673233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4839159084315675633782155 7258738626473513450673233)
        ·
          refine ⟨5444053969855135088004925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7258738626473513450673233 5444053969855135088004925)
          ·
            refine ⟨2041520238695675658001847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5444053969855135088004925 2041520238695675658001847)
            ·
              refine ⟨3062280358043513487002771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041520238695675658001847 3062280358043513487002771)
              ·
                refine ⟨4593420537065270230504157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062280358043513487002771 4593420537065270230504157)
                ·
                  refine ⟨1722532701399476336439059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4593420537065270230504157 1722532701399476336439059)
                  ·
                    refine ⟨2583799052099214504658589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1722532701399476336439059 2583799052099214504658589)
                    ·
                      refine ⟨968924644537205439246971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2583799052099214504658589 968924644537205439246971)
                      ·
                        rfl

theorem cell23_1886974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1886974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886974 prefixEnd_1886974 := by exact prefixLift 1886974
  have htrace : WordTrace (prefixWord ++ tailWord_1886974) baseStart_1886974 baseEnd_1886974 := by
    simpa [prefixWord, tailWord_1886974, baseEnd_1886974] using wordTrace_append hprefix tailTrace_1886974
  have hstable : (prefixWord ++ tailWord_1886974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886974).length < 2 ^ (prefixWord ++ tailWord_1886974).sum := by decide
  have hdescent : baseEnd_1886974 < baseStart_1886974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886976 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 4]
def baseStart_1886976 : Nat := 118140960795 + 1886976 * 2 ^ 59
def prefixEnd_1886976 : Nat := 4983230072969 + 3 ^ 40 * 1886976 * 2
def baseEnd_1886976 : Nat := 968925671498514431421961

theorem tailTrace_1886976 : CollatzResearch.WordTrace tailWord_1886976 prefixEnd_1886976 968925671498514431421961 := by
  unfold tailWord_1886976
  simp only [CollatzResearch.WordTrace]
  refine ⟨34411834405907848344348391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45882445874543797792464521 34411834405907848344348391)
  ·
    refine ⟨51617751608861772516522587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34411834405907848344348391 51617751608861772516522587)
    ·
      refine ⟨77426627413292658774783881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51617751608861772516522587 77426627413292658774783881)
      ·
        refine ⟨58069970559969494081087911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77426627413292658774783881 58069970559969494081087911)
        ·
          refine ⟨87104955839954241121631867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58069970559969494081087911 87104955839954241121631867)
          ·
            refine ⟨130657433759931361682447801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87104955839954241121631867 130657433759931361682447801)
            ·
              refine ⟨97993075319948521261835851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130657433759931361682447801 97993075319948521261835851)
              ·
                refine ⟨146989612979922781892753777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97993075319948521261835851 146989612979922781892753777)
                ·
                  refine ⟨110242209734942086419565333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146989612979922781892753777 110242209734942086419565333)
                  ·
                    refine ⟨5167603581325410300917125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110242209734942086419565333 5167603581325410300917125)
                    ·
                      refine ⟨968925671498514431421961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5167603581325410300917125 968925671498514431421961)
                      ·
                        rfl

theorem cell23_1886976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_1886976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886976 prefixEnd_1886976 := by exact prefixLift 1886976
  have htrace : WordTrace (prefixWord ++ tailWord_1886976) baseStart_1886976 baseEnd_1886976 := by
    simpa [prefixWord, tailWord_1886976, baseEnd_1886976] using wordTrace_append hprefix tailTrace_1886976
  have hstable : (prefixWord ++ tailWord_1886976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886976).length < 2 ^ (prefixWord ++ tailWord_1886976).sum := by decide
  have hdescent : baseEnd_1886976 < baseStart_1886976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886994 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1886994 : Nat := 118140960795 + 1886994 * 2 ^ 59
def prefixEnd_1886994 : Nat := 4983230072969 + 3 ^ 40 * 1886994 * 2
def baseEnd_1886994 : Nat := 322978304716765120332293

theorem tailTrace_1886994 : CollatzResearch.WordTrace tailWord_1886994 prefixEnd_1886994 322978304716765120332293 := by
  unfold tailWord_1886994
  simp only [CollatzResearch.WordTrace]
  refine ⟨17206081331437621440713009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45882883550500323841901357 17206081331437621440713009)
  ·
    refine ⟨12904560998578216080534757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17206081331437621440713009 12904560998578216080534757)
    ·
      refine ⟨2419605187233415515100267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12904560998578216080534757 2419605187233415515100267)
      ·
        refine ⟨3629407780850123272650401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419605187233415515100267 3629407780850123272650401)
        ·
          refine ⟨2722055835637592454487801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3629407780850123272650401 2722055835637592454487801)
          ·
            refine ⟨2041541876728194340865851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2722055835637592454487801 2041541876728194340865851)
            ·
              refine ⟨3062312815092291511298777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041541876728194340865851 3062312815092291511298777)
              ·
                refine ⟨2296734611319218633474083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3062312815092291511298777 2296734611319218633474083)
                ·
                  refine ⟨3445101916978827950211125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296734611319218633474083 3445101916978827950211125)
                  ·
                    refine ⟨322978304716765120332293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3445101916978827950211125 322978304716765120332293)
                    ·
                      rfl

theorem cell23_1886994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1886994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1886994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1886994 prefixEnd_1886994 := by exact prefixLift 1886994
  have htrace : WordTrace (prefixWord ++ tailWord_1886994) baseStart_1886994 baseEnd_1886994 := by
    simpa [prefixWord, tailWord_1886994, baseEnd_1886994] using wordTrace_append hprefix tailTrace_1886994
  have hstable : (prefixWord ++ tailWord_1886994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886994).length < 2 ^ (prefixWord ++ tailWord_1886994).sum := by decide
  have hdescent : baseEnd_1886994 < baseStart_1886994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887010 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_1887010 : Nat := 118140960795 + 1887010 * 2 ^ 59
def prefixEnd_1887010 : Nat := 4983230072969 + 3 ^ 40 * 1887010 * 2
def baseEnd_1887010 : Nat := 968943129840767298396805

theorem tailTrace_1887010 : CollatzResearch.WordTrace tailWord_1887010 prefixEnd_1887010 968943129840767298396805 := by
  unfold tailWord_1887010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17206227223423130123858621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45883272595795013663622989 17206227223423130123858621)
  ·
    refine ⟨6452335208783673796446983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17206227223423130123858621 6452335208783673796446983)
    ·
      refine ⟨9678502813175510694670475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6452335208783673796446983 9678502813175510694670475)
      ·
        refine ⟨14517754219763266042005713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9678502813175510694670475 14517754219763266042005713)
        ·
          refine ⟨10888315664822449531504285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14517754219763266042005713 10888315664822449531504285)
          ·
            refine ⟨4083118374308418574314107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10888315664822449531504285 4083118374308418574314107)
            ·
              refine ⟨6124677561462627861471161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4083118374308418574314107 6124677561462627861471161)
              ·
                refine ⟨4593508171096970896103371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6124677561462627861471161 4593508171096970896103371)
                ·
                  refine ⟨6890262256645456344155057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4593508171096970896103371 6890262256645456344155057)
                  ·
                    refine ⟨5167696692484092258116293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6890262256645456344155057 5167696692484092258116293)
                    ·
                      refine ⟨968943129840767298396805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5167696692484092258116293 968943129840767298396805)
                      ·
                        rfl

theorem cell23_1887010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_1887010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887010 prefixEnd_1887010 := by exact prefixLift 1887010
  have htrace : WordTrace (prefixWord ++ tailWord_1887010) baseStart_1887010 baseEnd_1887010 := by
    simpa [prefixWord, tailWord_1887010, baseEnd_1887010] using wordTrace_append hprefix tailTrace_1887010
  have hstable : (prefixWord ++ tailWord_1887010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887010).length < 2 ^ (prefixWord ++ tailWord_1887010).sum := by decide
  have hdescent : baseEnd_1887010 < baseStart_1887010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887037 : List Nat := [1, 4, 1, 4, 3, 1, 1, 8]
def baseStart_1887037 : Nat := 118140960795 + 1887037 * 2 ^ 59
def prefixEnd_1887037 : Nat := 4983230072969 + 3 ^ 40 * 1887037 * 2
def baseEnd_1887037 : Nat := 35887296067349581213303

theorem tailTrace_1887037 : CollatzResearch.WordTrace tailWord_1887037 prefixEnd_1887037 35887296067349581213303 := by
  unfold tailWord_1887037
  simp only [CollatzResearch.WordTrace]
  refine ⟨68825893664594704106667365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45883929109729802737778243 68825893664594704106667365)
  ·
    refine ⟨12904855062111507020000131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68825893664594704106667365 12904855062111507020000131)
    ·
      refine ⟨19357282593167260530000197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12904855062111507020000131 19357282593167260530000197)
      ·
        refine ⟨3629490486218861349375037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19357282593167260530000197 3629490486218861349375037)
        ·
          refine ⟨1361058932332073006015639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3629490486218861349375037 1361058932332073006015639)
          ·
            refine ⟨2041588398498109509023459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361058932332073006015639 2041588398498109509023459)
            ·
              refine ⟨3062382597747164263535189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041588398498109509023459 3062382597747164263535189)
              ·
                refine ⟨35887296067349581213303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3062382597747164263535189 35887296067349581213303)
                ·
                  rfl

theorem cell23_1887037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 8].length) (baseStart_1887037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887037 prefixEnd_1887037 := by exact prefixLift 1887037
  have htrace : WordTrace (prefixWord ++ tailWord_1887037) baseStart_1887037 baseEnd_1887037 := by
    simpa [prefixWord, tailWord_1887037, baseEnd_1887037] using wordTrace_append hprefix tailTrace_1887037
  have hstable : (prefixWord ++ tailWord_1887037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887037).length < 2 ^ (prefixWord ++ tailWord_1887037).sum := by decide
  have hdescent : baseEnd_1887037 < baseStart_1887037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887044 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1887044 : Nat := 118140960795 + 1887044 * 2 ^ 59
def prefixEnd_1887044 : Nat := 4983230072969 + 3 ^ 40 * 1887044 * 2
def baseEnd_1887044 : Nat := 968960588183020165371649

theorem tailTrace_1887044 : CollatzResearch.WordTrace tailWord_1887044 prefixEnd_1887044 968960588183020165371649 := by
  unfold tailWord_1887044
  simp only [CollatzResearch.WordTrace]
  refine ⟨34413074487784672151086093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45884099317046229534781457 34413074487784672151086093)
  ·
    refine ⟨12904902932919252056657285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34413074487784672151086093 12904902932919252056657285)
    ·
      refine ⟨2419669299922359760623241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12904902932919252056657285 2419669299922359760623241)
      ·
        refine ⟨1814751974941769820467431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2419669299922359760623241 1814751974941769820467431)
        ·
          refine ⟨2722127962412654730701147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814751974941769820467431 2722127962412654730701147)
          ·
            refine ⟨4083191943618982096051721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722127962412654730701147 4083191943618982096051721)
            ·
              refine ⟨3062393957714236572038791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083191943618982096051721 3062393957714236572038791)
              ·
                refine ⟨4593590936571354858058187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062393957714236572038791 4593590936571354858058187)
                ·
                  refine ⟨6890386404857032287087281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4593590936571354858058187 6890386404857032287087281)
                  ·
                    refine ⟨5167789803642774215315461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6890386404857032287087281 5167789803642774215315461)
                    ·
                      refine ⟨968960588183020165371649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5167789803642774215315461 968960588183020165371649)
                      ·
                        rfl

theorem cell23_1887044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1887044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887044 prefixEnd_1887044 := by exact prefixLift 1887044
  have htrace : WordTrace (prefixWord ++ tailWord_1887044) baseStart_1887044 baseEnd_1887044 := by
    simpa [prefixWord, tailWord_1887044, baseEnd_1887044] using wordTrace_append hprefix tailTrace_1887044
  have hstable : (prefixWord ++ tailWord_1887044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887044).length < 2 ^ (prefixWord ++ tailWord_1887044).sum := by decide
  have hdescent : baseEnd_1887044 < baseStart_1887044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887073 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_1887073 : Nat := 118140960795 + 1887073 * 2 ^ 59
def prefixEnd_1887073 : Nat := 4983230072969 + 3 ^ 40 * 1887073 * 2
def baseEnd_1887073 : Nat := 968975479122000551909015

theorem tailTrace_1887073 : CollatzResearch.WordTrace tailWord_1887073 prefixEnd_1887073 968975479122000551909015 := by
  unfold tailWord_1887073
  simp only [CollatzResearch.WordTrace]
  refine ⟨68827206692464282254977873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45884804461642854836651915 68827206692464282254977873)
  ·
    refine ⟨51620405019348211691233405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68827206692464282254977873 51620405019348211691233405)
    ·
      refine ⟨19357651882255579384212527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51620405019348211691233405 19357651882255579384212527)
      ·
        refine ⟨29036477823383369076318791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19357651882255579384212527 29036477823383369076318791)
        ·
          refine ⟨43554716735075053614478187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29036477823383369076318791 43554716735075053614478187)
          ·
            refine ⟨65332075102612580421717281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43554716735075053614478187 65332075102612580421717281)
            ·
              refine ⟨48999056326959435316287961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65332075102612580421717281 48999056326959435316287961)
              ·
                refine ⟨36749292245219576487215971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48999056326959435316287961 36749292245219576487215971)
                ·
                  refine ⟨55123938367829364730823957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36749292245219576487215971 55123938367829364730823957)
                  ·
                    refine ⟨2583934610992001471757373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55123938367829364730823957 2583934610992001471757373)
                    ·
                      refine ⟨968975479122000551909015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2583934610992001471757373 968975479122000551909015)
                      ·
                        rfl

theorem cell23_1887073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_1887073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887073 prefixEnd_1887073 := by exact prefixLift 1887073
  have htrace : WordTrace (prefixWord ++ tailWord_1887073) baseStart_1887073 baseEnd_1887073 := by
    simpa [prefixWord, tailWord_1887073, baseEnd_1887073] using wordTrace_append hprefix tailTrace_1887073
  have hstable : (prefixWord ++ tailWord_1887073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887073).length < 2 ^ (prefixWord ++ tailWord_1887073).sum := by decide
  have hdescent : baseEnd_1887073 < baseStart_1887073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887083 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 4]
def baseStart_1887083 : Nat := 118140960795 + 1887083 * 2 ^ 59
def prefixEnd_1887083 : Nat := 4983230072969 + 3 ^ 40 * 1887083 * 2
def baseEnd_1887083 : Nat := 968980613928545512783969

theorem tailTrace_1887083 : CollatzResearch.WordTrace tailWord_1887083 prefixEnd_1887083 968980613928545512783969 := by
  unfold tailWord_1887083
  simp only [CollatzResearch.WordTrace]
  refine ⟨68827571422428053962841903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45885047614952035975227935 68827571422428053962841903)
  ·
    refine ⟨103241357133642080944262855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68827571422428053962841903 103241357133642080944262855)
    ·
      refine ⟨154862035700463121416394283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103241357133642080944262855 154862035700463121416394283)
      ·
        refine ⟨232293053550694682124591425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154862035700463121416394283 232293053550694682124591425)
        ·
          refine ⟨174219790163021011593443569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232293053550694682124591425 174219790163021011593443569)
          ·
            refine ⟨130664842622265758695082677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174219790163021011593443569 130664842622265758695082677)
            ·
              refine ⟨12249828995837414877664001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130664842622265758695082677 12249828995837414877664001)
              ·
                refine ⟨9187371746878061158248001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12249828995837414877664001 9187371746878061158248001)
                ·
                  refine ⟨6890528810158545868686001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9187371746878061158248001 6890528810158545868686001)
                  ·
                    refine ⟨5167896607618909401514501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6890528810158545868686001 5167896607618909401514501)
                    ·
                      refine ⟨968980613928545512783969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5167896607618909401514501 968980613928545512783969)
                      ·
                        rfl

theorem cell23_1887083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 4].length) (baseStart_1887083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887083 prefixEnd_1887083 := by exact prefixLift 1887083
  have htrace : WordTrace (prefixWord ++ tailWord_1887083) baseStart_1887083 baseEnd_1887083 := by
    simpa [prefixWord, tailWord_1887083, baseEnd_1887083] using wordTrace_append hprefix tailTrace_1887083
  have hstable : (prefixWord ++ tailWord_1887083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887083).length < 2 ^ (prefixWord ++ tailWord_1887083).sum := by decide
  have hdescent : baseEnd_1887083 < baseStart_1887083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887140 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_1887140 : Nat := 118140960795 + 1887140 * 2 ^ 59
def prefixEnd_1887140 : Nat := 4983230072969 + 3 ^ 40 * 1887140 * 2
def baseEnd_1887140 : Nat := 323003294108617263257069

theorem tailTrace_1887140 : CollatzResearch.WordTrace tailWord_1887140 prefixEnd_1887140 323003294108617263257069 := by
  unfold tailWord_1887140
  simp only [CollatzResearch.WordTrace]
  refine ⟨34414825191610776348833437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45886433588814368465111249 34414825191610776348833437)
  ·
    refine ⟨12905559446854041130812539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34414825191610776348833437 12905559446854041130812539)
    ·
      refine ⟨19358339170281061696218809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12905559446854041130812539 19358339170281061696218809)
      ·
        refine ⟨14518754377710796272164107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19358339170281061696218809 14518754377710796272164107)
        ·
          refine ⟨21778131566566194408246161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14518754377710796272164107 21778131566566194408246161)
          ·
            refine ⟨16333598674924645806184621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21778131566566194408246161 16333598674924645806184621)
            ·
              refine ⟨6125099503096742177319233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16333598674924645806184621 6125099503096742177319233)
              ·
                refine ⟨4593824627322556632989425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6125099503096742177319233 4593824627322556632989425)
                ·
                  refine ⟨3445368470491917474742069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4593824627322556632989425 3445368470491917474742069)
                  ·
                    refine ⟨323003294108617263257069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3445368470491917474742069 323003294108617263257069)
                    ·
                      rfl

theorem cell23_1887140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_1887140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887140 prefixEnd_1887140 := by exact prefixLift 1887140
  have htrace : WordTrace (prefixWord ++ tailWord_1887140) baseStart_1887140 baseEnd_1887140 := by
    simpa [prefixWord, tailWord_1887140, baseEnd_1887140] using wordTrace_append hprefix tailTrace_1887140
  have hstable : (prefixWord ++ tailWord_1887140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887140).length < 2 ^ (prefixWord ++ tailWord_1887140).sum := by decide
  have hdescent : baseEnd_1887140 < baseStart_1887140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887221 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1887221 : Nat := 118140960795 + 1887221 * 2 ^ 59
def prefixEnd_1887221 : Nat := 4983230072969 + 3 ^ 40 * 1887221 * 2
def baseEnd_1887221 : Nat := 323017158086288657619445

theorem tailTrace_1887221 : CollatzResearch.WordTrace tailWord_1887221 prefixEnd_1887221 323017158086288657619445 := by
  unfold tailWord_1887221
  simp only [CollatzResearch.WordTrace]
  refine ⟨68832604695928103531365517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45888403130618735687577011 68832604695928103531365517)
  ·
    refine ⟨25812226760973038824262069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68832604695928103531365517 25812226760973038824262069)
    ·
      refine ⟨2419896258841222389774569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25812226760973038824262069 2419896258841222389774569)
      ·
        refine ⟨1814922194130916792330927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2419896258841222389774569 1814922194130916792330927)
        ·
          refine ⟨2722383291196375188496391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814922194130916792330927 2722383291196375188496391)
          ·
            refine ⟨4083574936794562782744587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722383291196375188496391 4083574936794562782744587)
            ·
              refine ⟨6125362405191844174116881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4083574936794562782744587 6125362405191844174116881)
              ·
                refine ⟨4594021803893883130587661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6125362405191844174116881 4594021803893883130587661)
                ·
                  refine ⟨1722758176460206173970373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4594021803893883130587661 1722758176460206173970373)
                  ·
                    refine ⟨323017158086288657619445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1722758176460206173970373 323017158086288657619445)
                    ·
                      rfl

theorem cell23_1887221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1887221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887221 prefixEnd_1887221 := by exact prefixLift 1887221
  have htrace : WordTrace (prefixWord ++ tailWord_1887221) baseStart_1887221 baseEnd_1887221 := by
    simpa [prefixWord, tailWord_1887221, baseEnd_1887221] using wordTrace_append hprefix tailTrace_1887221
  have hstable : (prefixWord ++ tailWord_1887221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887221).length < 2 ^ (prefixWord ++ tailWord_1887221).sum := by decide
  have hdescent : baseEnd_1887221 < baseStart_1887221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887237 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 1, 5, 2]
def baseStart_1887237 : Nat := 118140960795 + 1887237 * 2 ^ 59
def prefixEnd_1887237 : Nat := 4983230072969 + 3 ^ 40 * 1887237 * 2
def baseEnd_1887237 : Nat := 969059689949337910258261

theorem tailTrace_1887237 : CollatzResearch.WordTrace tailWord_1887237 prefixEnd_1887237 969059689949337910258261 := by
  unfold tailWord_1887237
  simp only [CollatzResearch.WordTrace]
  refine ⟨68833188263870138263947965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45888792175913425509298643 68833188263870138263947965)
  ·
    refine ⟨25812445598951301848980487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68833188263870138263947965 25812445598951301848980487)
    ·
      refine ⟨38718668398426952773470731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25812445598951301848980487 38718668398426952773470731)
      ·
        refine ⟨58078002597640429160206097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38718668398426952773470731 58078002597640429160206097)
        ·
          refine ⟨43558501948230321870154573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58078002597640429160206097 43558501948230321870154573)
          ·
            refine ⟨16334438230586370701307965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43558501948230321870154573 16334438230586370701307965)
            ·
              refine ⟨6125414336469889012990487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16334438230586370701307965 6125414336469889012990487)
              ·
                refine ⟨9188121504704833519485731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6125414336469889012990487 9188121504704833519485731)
                ·
                  refine ⟨13782182257057250279228597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9188121504704833519485731 13782182257057250279228597)
                  ·
                    refine ⟨1292079586599117213677681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13782182257057250279228597 1292079586599117213677681)
                    ·
                      refine ⟨969059689949337910258261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292079586599117213677681 969059689949337910258261)
                      ·
                        rfl

theorem cell23_1887237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 5, 2].length) (baseStart_1887237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887237 prefixEnd_1887237 := by exact prefixLift 1887237
  have htrace : WordTrace (prefixWord ++ tailWord_1887237) baseStart_1887237 baseEnd_1887237 := by
    simpa [prefixWord, tailWord_1887237, baseEnd_1887237] using wordTrace_append hprefix tailTrace_1887237
  have hstable : (prefixWord ++ tailWord_1887237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887237).length < 2 ^ (prefixWord ++ tailWord_1887237).sum := by decide
  have hdescent : baseEnd_1887237 < baseStart_1887237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887261 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_1887261 : Nat := 118140960795 + 1887261 * 2 ^ 59
def prefixEnd_1887261 : Nat := 4983230072969 + 3 ^ 40 * 1887261 * 2
def baseEnd_1887261 : Nat := 969072013485045816358151

theorem tailTrace_1887261 : CollatzResearch.WordTrace tailWord_1887261 prefixEnd_1887261 969072013485045816358151 := by
  unfold tailWord_1887261
  simp only [CollatzResearch.WordTrace]
  refine ⟨68834063615783190362821637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45889375743855460241881091 68834063615783190362821637)
  ·
    refine ⟨12906386927959348193029057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68834063615783190362821637 12906386927959348193029057)
    ·
      refine ⟨9679790195969511144771793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12906386927959348193029057 9679790195969511144771793)
      ·
        refine ⟨7259842646977133358578845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9679790195969511144771793 7259842646977133358578845)
        ·
          refine ⟨2722440992616425009467067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7259842646977133358578845 2722440992616425009467067)
          ·
            refine ⟨4083661488924637514200601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722440992616425009467067 4083661488924637514200601)
            ·
              refine ⟨3062746116693478135650451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083661488924637514200601 3062746116693478135650451)
              ·
                refine ⟨4594119175040217203475677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062746116693478135650451 4594119175040217203475677)
                ·
                  refine ⟨1722794690640081451303379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4594119175040217203475677 1722794690640081451303379)
                  ·
                    refine ⟨2584192035960122176955069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1722794690640081451303379 2584192035960122176955069)
                    ·
                      refine ⟨969072013485045816358151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2584192035960122176955069 969072013485045816358151)
                      ·
                        rfl

theorem cell23_1887261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_1887261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887261 prefixEnd_1887261 := by exact prefixLift 1887261
  have htrace : WordTrace (prefixWord ++ tailWord_1887261) baseStart_1887261 baseEnd_1887261 := by
    simpa [prefixWord, tailWord_1887261, baseEnd_1887261] using wordTrace_append hprefix tailTrace_1887261
  have hstable : (prefixWord ++ tailWord_1887261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887261).length < 2 ^ (prefixWord ++ tailWord_1887261).sum := by decide
  have hdescent : baseEnd_1887261 < baseStart_1887261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887280 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 6]
def baseStart_1887280 : Nat := 118140960795 + 1887280 * 2 ^ 59
def prefixEnd_1887280 : Nat := 4983230072969 + 3 ^ 40 * 1887280 * 2
def baseEnd_1887280 : Nat := 969081769617481242020563

theorem tailTrace_1887280 : CollatzResearch.WordTrace tailWord_1887280 prefixEnd_1887280 969081769617481242020563 := by
  unfold tailWord_1887280
  simp only [CollatzResearch.WordTrace]
  refine ⟨34417378301357178303881647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45889837735142904405175529 34417378301357178303881647)
  ·
    refine ⟨51626067452035767455822471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34417378301357178303881647 51626067452035767455822471)
    ·
      refine ⟨77439101178053651183733707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51626067452035767455822471 77439101178053651183733707)
      ·
        refine ⟨116158651767080476775600561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77439101178053651183733707 116158651767080476775600561)
        ·
          refine ⟨87118988825310357581700421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116158651767080476775600561 87118988825310357581700421)
          ·
            refine ⟨16334810404745692046568829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87118988825310357581700421 16334810404745692046568829)
            ·
              refine ⟨6125553901779634517463311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16334810404745692046568829 6125553901779634517463311)
              ·
                refine ⟨9188330852669451776194967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6125553901779634517463311 9188330852669451776194967)
                ·
                  refine ⟨13782496279004177664292451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9188330852669451776194967 13782496279004177664292451)
                  ·
                    refine ⟨20673744418506266496438677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13782496279004177664292451 20673744418506266496438677)
                    ·
                      refine ⟨969081769617481242020563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20673744418506266496438677 969081769617481242020563)
                      ·
                        rfl

theorem cell23_1887280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_1887280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887280 prefixEnd_1887280 := by exact prefixLift 1887280
  have htrace : WordTrace (prefixWord ++ tailWord_1887280) baseStart_1887280 baseEnd_1887280 := by
    simpa [prefixWord, tailWord_1887280, baseEnd_1887280] using wordTrace_append hprefix tailTrace_1887280
  have hstable : (prefixWord ++ tailWord_1887280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887280).length < 2 ^ (prefixWord ++ tailWord_1887280).sum := by decide
  have hdescent : baseEnd_1887280 < baseStart_1887280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887294 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1887294 : Nat := 118140960795 + 1887294 * 2 ^ 59
def prefixEnd_1887294 : Nat := 4983230072969 + 3 ^ 40 * 1887294 * 2
def baseEnd_1887294 : Nat := 323029652782214729081833

theorem tailTrace_1887294 : CollatzResearch.WordTrace tailWord_1887294 prefixEnd_1887294 323029652782214729081833 := by
  unfold tailWord_1887294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8604408403082954624846617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45890178149775757999181957 8604408403082954624846617)
  ·
    refine ⟨6453306302312215968634963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8604408403082954624846617 6453306302312215968634963)
    ·
      refine ⟨9679959453468323952952445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6453306302312215968634963 9679959453468323952952445)
      ·
        refine ⟨3629984795050621482357167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9679959453468323952952445 3629984795050621482357167)
        ·
          refine ⟨5444977192575932223535751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3629984795050621482357167 5444977192575932223535751)
          ·
            refine ⟨8167465788863898335303627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5444977192575932223535751 8167465788863898335303627)
            ·
              refine ⟨12251198683295847502955441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8167465788863898335303627 12251198683295847502955441)
              ·
                refine ⟨9188399012471885627216581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12251198683295847502955441 9188399012471885627216581)
                ·
                  refine ⟨1722824814838478555103109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9188399012471885627216581 1722824814838478555103109)
                  ·
                    refine ⟨323029652782214729081833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1722824814838478555103109 323029652782214729081833)
                    ·
                      rfl

theorem cell23_1887294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1887294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887294 prefixEnd_1887294 := by exact prefixLift 1887294
  have htrace : WordTrace (prefixWord ++ tailWord_1887294) baseStart_1887294 baseEnd_1887294 := by
    simpa [prefixWord, tailWord_1887294, baseEnd_1887294] using wordTrace_append hprefix tailTrace_1887294
  have hstable : (prefixWord ++ tailWord_1887294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887294).length < 2 ^ (prefixWord ++ tailWord_1887294).sum := by decide
  have hdescent : baseEnd_1887294 < baseStart_1887294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887320 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 2, 7]
def baseStart_1887320 : Nat := 118140960795 + 1887320 * 2 ^ 59
def prefixEnd_1887320 : Nat := 4983230072969 + 3 ^ 40 * 1887320 * 2
def baseEnd_1887320 : Nat := 323034102947887028506793

theorem tailTrace_1887320 : CollatzResearch.WordTrace tailWord_1887320 prefixEnd_1887320 323034102947887028506793 := by
  unfold tailWord_1887320
  simp only [CollatzResearch.WordTrace]
  refine ⟨34418107761284721719609707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45890810348379628959479609 34418107761284721719609707)
  ·
    refine ⟨51627161641927082579414561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34418107761284721719609707 51627161641927082579414561)
    ·
      refine ⟨38720371231445311934560921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51627161641927082579414561 38720371231445311934560921)
      ·
        refine ⟨29040278423583983950920691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38720371231445311934560921 29040278423583983950920691)
        ·
          refine ⟨43560417635375975926381037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29040278423583983950920691 43560417635375975926381037)
          ·
            refine ⟨16335156613265990972392889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43560417635375975926381037 16335156613265990972392889)
            ·
              refine ⟨12251367459949493229294667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16335156613265990972392889 12251367459949493229294667)
              ·
                refine ⟨18377051189924239843942001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12251367459949493229294667 18377051189924239843942001)
                ·
                  refine ⟨13782788392443179882956501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18377051189924239843942001 13782788392443179882956501)
                  ·
                    refine ⟨323034102947887028506793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13782788392443179882956501 323034102947887028506793)
                    ·
                      rfl

theorem cell23_1887320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_1887320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887320 prefixEnd_1887320 := by exact prefixLift 1887320
  have htrace : WordTrace (prefixWord ++ tailWord_1887320) baseStart_1887320 baseEnd_1887320 := by
    simpa [prefixWord, tailWord_1887320, baseEnd_1887320] using wordTrace_append hprefix tailTrace_1887320
  have hstable : (prefixWord ++ tailWord_1887320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887320).length < 2 ^ (prefixWord ++ tailWord_1887320).sum := by decide
  have hdescent : baseEnd_1887320 < baseStart_1887320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887344 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 3, 3, 2]
def baseStart_1887344 : Nat := 118140960795 + 1887344 * 2 ^ 59
def prefixEnd_1887344 : Nat := 4983230072969 + 3 ^ 40 * 1887344 * 2
def baseEnd_1887344 : Nat := 969114632379368991620269

theorem tailTrace_1887344 : CollatzResearch.WordTrace tailWord_1887344 prefixEnd_1887344 969114632379368991620269 := by
  unfold tailWord_1887344
  simp only [CollatzResearch.WordTrace]
  refine ⟨34418545437241247769046543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45891393916321663692062057 34418545437241247769046543)
  ·
    refine ⟨51627818155861871653569815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34418545437241247769046543 51627818155861871653569815)
    ·
      refine ⟨77441727233792807480354723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51627818155861871653569815 77441727233792807480354723)
      ·
        refine ⟨116162590850689211220532085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77441727233792807480354723 116162590850689211220532085)
        ·
          refine ⟨10890242892252113551924883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116162590850689211220532085 10890242892252113551924883)
          ·
            refine ⟨16335364338378170327887325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10890242892252113551924883 16335364338378170327887325)
            ·
              refine ⟨6125761626891813872957747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16335364338378170327887325 6125761626891813872957747)
              ·
                refine ⟨9188642440337720809436621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6125761626891813872957747 9188642440337720809436621)
                ·
                  refine ⟨3445740915126645303538733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9188642440337720809436621 3445740915126645303538733)
                  ·
                    refine ⟨1292152843172491988827025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3445740915126645303538733 1292152843172491988827025)
                    ·
                      refine ⟨969114632379368991620269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292152843172491988827025 969114632379368991620269)
                      ·
                        rfl

theorem cell23_1887344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 3, 2].length) (baseStart_1887344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887344 prefixEnd_1887344 := by exact prefixLift 1887344
  have htrace : WordTrace (prefixWord ++ tailWord_1887344) baseStart_1887344 baseEnd_1887344 := by
    simpa [prefixWord, tailWord_1887344, baseEnd_1887344] using wordTrace_append hprefix tailTrace_1887344
  have hstable : (prefixWord ++ tailWord_1887344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887344).length < 2 ^ (prefixWord ++ tailWord_1887344).sum := by decide
  have hdescent : baseEnd_1887344 < baseStart_1887344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887368 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1887368 : Nat := 118140960795 + 1887368 * 2 ^ 59
def prefixEnd_1887368 : Nat := 4983230072969 + 3 ^ 40 * 1887368 * 2
def baseEnd_1887368 : Nat := 969126955915076897720159

theorem tailTrace_1887368 : CollatzResearch.WordTrace tailWord_1887368 prefixEnd_1887368 969126955915076897720159 := by
  unfold tailWord_1887368
  simp only [CollatzResearch.WordTrace]
  refine ⟨34418983113197773818483379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45891977484263698424644505 34418983113197773818483379)
  ·
    refine ⟨51628474669796660727725069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34418983113197773818483379 51628474669796660727725069)
    ·
      refine ⟨19360678001173747772896901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51628474669796660727725069 19360678001173747772896901)
      ·
        refine ⟨3630127125220077707418169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19360678001173747772896901 3630127125220077707418169)
        ·
          refine ⟨2722595343915058280563627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3630127125220077707418169 2722595343915058280563627)
          ·
            refine ⟨4083893015872587420845441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722595343915058280563627 4083893015872587420845441)
            ·
              refine ⟨3062919761904440565634081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083893015872587420845441 3062919761904440565634081)
              ·
                refine ⟨2297189821428330424225561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3062919761904440565634081 2297189821428330424225561)
                ·
                  refine ⟨1722892366071247818169171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2297189821428330424225561 1722892366071247818169171)
                  ·
                    refine ⟨2584338549106871727253757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1722892366071247818169171 2584338549106871727253757)
                    ·
                      refine ⟨969126955915076897720159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2584338549106871727253757 969126955915076897720159)
                      ·
                        rfl

theorem cell23_1887368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1887368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887368 prefixEnd_1887368 := by exact prefixLift 1887368
  have htrace : WordTrace (prefixWord ++ tailWord_1887368) baseStart_1887368 baseEnd_1887368 := by
    simpa [prefixWord, tailWord_1887368, baseEnd_1887368] using wordTrace_append hprefix tailTrace_1887368
  have hstable : (prefixWord ++ tailWord_1887368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887368).length < 2 ^ (prefixWord ++ tailWord_1887368).sum := by decide
  have hdescent : baseEnd_1887368 < baseStart_1887368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887397 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 7]
def baseStart_1887397 : Nat := 118140960795 + 1887397 * 2 ^ 59
def prefixEnd_1887397 : Nat := 4983230072969 + 3 ^ 40 * 1887397 * 2
def baseEnd_1887397 : Nat := 107682427428228587139725

theorem tailTrace_1887397 : CollatzResearch.WordTrace tailWord_1887397 prefixEnd_1887397 107682427428228587139725 := by
  unfold tailWord_1887397
  simp only [CollatzResearch.WordTrace]
  refine ⟨68839023943290485589772445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45892682628860323726514963 68839023943290485589772445)
  ·
    refine ⟨25814633978733932096164667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68839023943290485589772445 25814633978733932096164667)
    ·
      refine ⟨38721950968100898144247001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25814633978733932096164667 38721950968100898144247001)
      ·
        refine ⟨29041463226075673608185251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38721950968100898144247001 29041463226075673608185251)
        ·
          refine ⟨43562194839113510412277877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29041463226075673608185251 43562194839113510412277877)
          ·
            refine ⟨4083955766166891601151051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43562194839113510412277877 4083955766166891601151051)
            ·
              refine ⟨6125933649250337401726577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4083955766166891601151051 6125933649250337401726577)
              ·
                refine ⟨4594450236937753051294933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6125933649250337401726577 4594450236937753051294933)
                ·
                  refine ⟨107682427428228587139725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4594450236937753051294933 107682427428228587139725)
                  ·
                    rfl

theorem cell23_1887397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_1887397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887397 prefixEnd_1887397 := by exact prefixLift 1887397
  have htrace : WordTrace (prefixWord ++ tailWord_1887397) baseStart_1887397 baseEnd_1887397 := by
    simpa [prefixWord, tailWord_1887397, baseEnd_1887397] using wordTrace_append hprefix tailTrace_1887397
  have hstable : (prefixWord ++ tailWord_1887397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887397).length < 2 ^ (prefixWord ++ tailWord_1887397).sum := by decide
  have hdescent : baseEnd_1887397 < baseStart_1887397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887425 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_1887425 : Nat := 118140960795 + 1887425 * 2 ^ 59
def prefixEnd_1887425 : Nat := 4983230072969 + 3 ^ 40 * 1887425 * 2
def baseEnd_1887425 : Nat := 969156224312383174707397

theorem tailTrace_1887425 : CollatzResearch.WordTrace tailWord_1887425 prefixEnd_1887425 969156224312383174707397 := by
  unfold tailWord_1887425
  simp only [CollatzResearch.WordTrace]
  refine ⟨68840045187189046371791729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45893363458126030914527819 68840045187189046371791729)
  ·
    refine ⟨51630033890391784778843797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68840045187189046371791729 51630033890391784778843797)
    ·
      refine ⟨2420157838612114911508303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51630033890391784778843797 2420157838612114911508303)
      ·
        refine ⟨3630236757918172367262455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420157838612114911508303 3630236757918172367262455)
        ·
          refine ⟨5445355136877258550893683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3630236757918172367262455 5445355136877258550893683)
          ·
            refine ⟨8168032705315887826340525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5445355136877258550893683 8168032705315887826340525)
            ·
              refine ⟨3063012264493457934877697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8168032705315887826340525 3063012264493457934877697)
              ·
                refine ⟨2297259198370093451158273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3063012264493457934877697 2297259198370093451158273)
                ·
                  refine ⟨1722944398777570088368705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2297259198370093451158273 1722944398777570088368705)
                  ·
                    refine ⟨1292208299083177566276529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1722944398777570088368705 1292208299083177566276529)
                    ·
                      refine ⟨969156224312383174707397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292208299083177566276529 969156224312383174707397)
                      ·
                        rfl

theorem cell23_1887425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_1887425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887425 prefixEnd_1887425 := by exact prefixLift 1887425
  have htrace : WordTrace (prefixWord ++ tailWord_1887425) baseStart_1887425 baseEnd_1887425 := by
    simpa [prefixWord, tailWord_1887425, baseEnd_1887425] using wordTrace_append hprefix tailTrace_1887425
  have hstable : (prefixWord ++ tailWord_1887425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887425).length < 2 ^ (prefixWord ++ tailWord_1887425).sum := by decide
  have hdescent : baseEnd_1887425 < baseStart_1887425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887447 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_1887447 : Nat := 118140960795 + 1887447 * 2 ^ 59
def prefixEnd_1887447 : Nat := 4983230072969 + 3 ^ 40 * 1887447 * 2
def baseEnd_1887447 : Nat := 969167520886782088632295

theorem tailTrace_1887447 : CollatzResearch.WordTrace tailWord_1887447 prefixEnd_1887447 969167520886782088632295 := by
  unfold tailWord_1887447
  simp only [CollatzResearch.WordTrace]
  refine ⟨68840847593109344129092595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45893898395406229419395063 68840847593109344129092595)
  ·
    refine ⟨103261271389664016193638893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68840847593109344129092595 103261271389664016193638893)
    ·
      refine ⟨38722976771124006072614585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103261271389664016193638893 38722976771124006072614585)
      ·
        refine ⟨29042232578343004554460939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38722976771124006072614585 29042232578343004554460939)
        ·
          refine ⟨43563348867514506831691409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29042232578343004554460939 43563348867514506831691409)
          ·
            refine ⟨32672511650635880123768557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43563348867514506831691409 32672511650635880123768557)
            ·
              refine ⟨12252191868988455046413209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32672511650635880123768557 12252191868988455046413209)
              ·
                refine ⟨9189143901741341284809907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12252191868988455046413209 9189143901741341284809907)
                ·
                  refine ⟨13783715852612011927214861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9189143901741341284809907 13783715852612011927214861)
                  ·
                    refine ⟨5168893444729504472705573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13783715852612011927214861 5168893444729504472705573)
                    ·
                      refine ⟨969167520886782088632295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5168893444729504472705573 969167520886782088632295)
                      ·
                        rfl

theorem cell23_1887447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_1887447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887447 prefixEnd_1887447 := by exact prefixLift 1887447
  have htrace : WordTrace (prefixWord ++ tailWord_1887447) baseStart_1887447 baseEnd_1887447 := by
    simpa [prefixWord, tailWord_1887447, baseEnd_1887447] using wordTrace_append hprefix tailTrace_1887447
  have hstable : (prefixWord ++ tailWord_1887447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887447).length < 2 ^ (prefixWord ++ tailWord_1887447).sum := by decide
  have hdescent : baseEnd_1887447 < baseStart_1887447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887464 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1887464 : Nat := 118140960795 + 1887464 * 2 ^ 59
def prefixEnd_1887464 : Nat := 4983230072969 + 3 ^ 40 * 1887464 * 2
def baseEnd_1887464 : Nat := 969176250057908522119717

theorem tailTrace_1887464 : CollatzResearch.WordTrace tailWord_1887464 prefixEnd_1887464 969176250057908522119717 := by
  unfold tailWord_1887464
  simp only [CollatzResearch.WordTrace]
  refine ⟨34420733817023878016230723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45894311756031837354974297 34420733817023878016230723)
  ·
    refine ⟨51631100725535817024346085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34420733817023878016230723 51631100725535817024346085)
    ·
      refine ⟨9680831386037965692064891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51631100725535817024346085 9680831386037965692064891)
      ·
        refine ⟨14521247079056948538097337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9680831386037965692064891 14521247079056948538097337)
        ·
          refine ⟨10890935309292711403573003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14521247079056948538097337 10890935309292711403573003)
          ·
            refine ⟨16336402963939067105359505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10890935309292711403573003 16336402963939067105359505)
            ·
              refine ⟨12252302222954300329019629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16336402963939067105359505 12252302222954300329019629)
              ·
                refine ⟨4594613333607862623382361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12252302222954300329019629 4594613333607862623382361)
                ·
                  refine ⟨3445960000205896967536771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4594613333607862623382361 3445960000205896967536771)
                  ·
                    refine ⟨5168940000308845451305157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3445960000205896967536771 5168940000308845451305157)
                    ·
                      refine ⟨969176250057908522119717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5168940000308845451305157 969176250057908522119717)
                      ·
                        rfl

theorem cell23_1887464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1887464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887464 prefixEnd_1887464 := by exact prefixLift 1887464
  have htrace : WordTrace (prefixWord ++ tailWord_1887464) baseStart_1887464 baseEnd_1887464 := by
    simpa [prefixWord, tailWord_1887464, baseEnd_1887464] using wordTrace_append hprefix tailTrace_1887464
  have hstable : (prefixWord ++ tailWord_1887464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887464).length < 2 ^ (prefixWord ++ tailWord_1887464).sum := by decide
  have hdescent : baseEnd_1887464 < baseStart_1887464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887487 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 8]
def baseStart_1887487 : Nat := 118140960795 + 1887487 * 2 ^ 59
def prefixEnd_1887487 : Nat := 4983230072969 + 3 ^ 40 * 1887487 * 2
def baseEnd_1887487 : Nat := 107687562234773548014679

theorem tailTrace_1887487 : CollatzResearch.WordTrace tailWord_1887487 prefixEnd_1887487 107687562234773548014679 := by
  unfold tailWord_1887487
  simp only [CollatzResearch.WordTrace]
  refine ⟨68842306512964430960548715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45894871008642953973699143 68842306512964430960548715)
  ·
    refine ⟨103263459769446646440823073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68842306512964430960548715 103263459769446646440823073)
    ·
      refine ⟨77447594827084984830617305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103263459769446646440823073 77447594827084984830617305)
      ·
        refine ⟨58085696120313738622962979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77447594827084984830617305 58085696120313738622962979)
        ·
          refine ⟨87128544180470607934444469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58085696120313738622962979 87128544180470607934444469)
          ·
            refine ⟨8168301016919119493854169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87128544180470607934444469 8168301016919119493854169)
            ·
              refine ⟨6126225762689339620390627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8168301016919119493854169 6126225762689339620390627)
              ·
                refine ⟨9189338644034009430585941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6126225762689339620390627 9189338644034009430585941)
                ·
                  refine ⟨107687562234773548014679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9189338644034009430585941 107687562234773548014679)
                  ·
                    rfl

theorem cell23_1887487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 8].length) (baseStart_1887487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887487 prefixEnd_1887487 := by exact prefixLift 1887487
  have htrace : WordTrace (prefixWord ++ tailWord_1887487) baseStart_1887487 baseEnd_1887487 := by
    simpa [prefixWord, tailWord_1887487, baseEnd_1887487] using wordTrace_append hprefix tailTrace_1887487
  have hstable : (prefixWord ++ tailWord_1887487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887487).length < 2 ^ (prefixWord ++ tailWord_1887487).sum := by decide
  have hdescent : baseEnd_1887487 < baseStart_1887487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887491 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 3, 4]
def baseStart_1887491 : Nat := 118140960795 + 1887491 * 2 ^ 59
def prefixEnd_1887491 : Nat := 4983230072969 + 3 ^ 40 * 1887491 * 2
def baseEnd_1887491 : Nat := 323063371345193305494031

theorem tailTrace_1887491 : CollatzResearch.WordTrace tailWord_1887491 prefixEnd_1887491 323063371345193305494031 := by
  unfold tailWord_1887491
  simp only [CollatzResearch.WordTrace]
  refine ⟨68842452404949939643694327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45894968269966626429129551 68842452404949939643694327)
  ·
    refine ⟨103263678607424909465541491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68842452404949939643694327 103263678607424909465541491)
    ·
      refine ⟨154895517911137364198312237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103263678607424909465541491 154895517911137364198312237)
      ·
        refine ⟨58085819216676511574367089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154895517911137364198312237 58085819216676511574367089)
        ·
          refine ⟨43564364412507383680775317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58085819216676511574367089 43564364412507383680775317)
          ·
            refine ⟨2042079581836283610036343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43564364412507383680775317 2042079581836283610036343)
            ·
              refine ⟨3063119372754425415054515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2042079581836283610036343 3063119372754425415054515)
              ·
                refine ⟨4594679059131638122581773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063119372754425415054515 4594679059131638122581773)
                ·
                  refine ⟨1723004647174364295968165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4594679059131638122581773 1723004647174364295968165)
                  ·
                    refine ⟨323063371345193305494031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723004647174364295968165 323063371345193305494031)
                    ·
                      rfl

theorem cell23_1887491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 4].length) (baseStart_1887491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887491 prefixEnd_1887491 := by exact prefixLift 1887491
  have htrace : WordTrace (prefixWord ++ tailWord_1887491) baseStart_1887491 baseEnd_1887491 := by
    simpa [prefixWord, tailWord_1887491, baseEnd_1887491] using wordTrace_append hprefix tailTrace_1887491
  have hstable : (prefixWord ++ tailWord_1887491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887491).length < 2 ^ (prefixWord ++ tailWord_1887491).sum := by decide
  have hdescent : baseEnd_1887491 < baseStart_1887491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887542 : List Nat := [5, 1, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_1887542 : Nat := 118140960795 + 1887542 * 2 ^ 59
def prefixEnd_1887542 : Nat := 4983230072969 + 3 ^ 40 * 1887542 * 2
def baseEnd_1887542 : Nat := 323072100516319738981453

theorem tailTrace_1887542 : CollatzResearch.WordTrace tailWord_1887542 prefixEnd_1887542 323072100516319738981453 := by
  unfold tailWord_1887542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4302769532985323459612555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45896208351843450235867253 4302769532985323459612555)
  ·
    refine ⟨6454154299477985189418833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4302769532985323459612555 6454154299477985189418833)
    ·
      refine ⟨4840615724608488892064125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6454154299477985189418833 4840615724608488892064125)
      ·
        refine ⟨1815230896728183334524047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4840615724608488892064125 1815230896728183334524047)
        ·
          refine ⟨2722846345092275001786071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1815230896728183334524047 2722846345092275001786071)
          ·
            refine ⟨4084269517638412502679107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722846345092275001786071 4084269517638412502679107)
            ·
              refine ⟨6126404276457618754018661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084269517638412502679107 6126404276457618754018661)
              ·
                refine ⟨1148700801835803516378499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6126404276457618754018661 1148700801835803516378499)
                ·
                  refine ⟨1723051202753705274567749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1148700801835803516378499 1723051202753705274567749)
                  ·
                    refine ⟨323072100516319738981453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723051202753705274567749 323072100516319738981453)
                    ·
                      rfl

theorem cell23_1887542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_1887542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887542 prefixEnd_1887542 := by exact prefixLift 1887542
  have htrace : WordTrace (prefixWord ++ tailWord_1887542) baseStart_1887542 baseEnd_1887542 := by
    simpa [prefixWord, tailWord_1887542, baseEnd_1887542] using wordTrace_append hprefix tailTrace_1887542
  have hstable : (prefixWord ++ tailWord_1887542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887542).length < 2 ^ (prefixWord ++ tailWord_1887542).sum := by decide
  have hdescent : baseEnd_1887542 < baseStart_1887542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887564 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_1887564 : Nat := 118140960795 + 1887564 * 2 ^ 59
def prefixEnd_1887564 : Nat := 4983230072969 + 3 ^ 40 * 1887564 * 2
def baseEnd_1887564 : Nat := 323075866041119376956419

theorem tailTrace_1887564 : CollatzResearch.WordTrace tailWord_1887564 prefixEnd_1887564 323075866041119376956419 := by
  unfold tailWord_1887564
  simp only [CollatzResearch.WordTrace]
  refine ⟨34422557466842736555550873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45896743289123648740734497 34422557466842736555550873)
  ·
    refine ⟨25816918100132052416663155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34422557466842736555550873 25816918100132052416663155)
    ·
      refine ⟨38725377150198078624994733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25816918100132052416663155 38725377150198078624994733)
      ·
        refine ⟨14522016431324279484373025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38725377150198078624994733 14522016431324279484373025)
        ·
          refine ⟨10891512323493209613279769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14522016431324279484373025 10891512323493209613279769)
          ·
            refine ⟨8168634242619907209959827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10891512323493209613279769 8168634242619907209959827)
            ·
              refine ⟨12252951363929860814939741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8168634242619907209959827 12252951363929860814939741)
              ·
                refine ⟨4594856761473697805602403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12252951363929860814939741 4594856761473697805602403)
                ·
                  refine ⟨6892285142210546708403605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4594856761473697805602403 6892285142210546708403605)
                  ·
                    refine ⟨323075866041119376956419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6892285142210546708403605 323075866041119376956419)
                    ·
                      rfl

theorem cell23_1887564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_1887564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887564 prefixEnd_1887564 := by exact prefixLift 1887564
  have htrace : WordTrace (prefixWord ++ tailWord_1887564) baseStart_1887564 baseEnd_1887564 := by
    simpa [prefixWord, tailWord_1887564, baseEnd_1887564] using wordTrace_append hprefix tailTrace_1887564
  have hstable : (prefixWord ++ tailWord_1887564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887564).length < 2 ^ (prefixWord ++ tailWord_1887564).sum := by decide
  have hdescent : baseEnd_1887564 < baseStart_1887564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887567 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_1887567 : Nat := 118140960795 + 1887567 * 2 ^ 59
def prefixEnd_1887567 : Nat := 4983230072969 + 3 ^ 40 * 1887567 * 2
def baseEnd_1887567 : Nat := 969229138565321619131743

theorem tailTrace_1887567 : CollatzResearch.WordTrace tailWord_1887567 prefixEnd_1887567 969229138565321619131743 := by
  unfold tailWord_1887567
  simp only [CollatzResearch.WordTrace]
  refine ⟨68845224352674604623460955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45896816235116403082307303 68845224352674604623460955)
  ·
    refine ⟨103267836529011906935191433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68845224352674604623460955 103267836529011906935191433)
    ·
      refine ⟨77450877396758930201393575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103267836529011906935191433 77450877396758930201393575)
      ·
        refine ⟨116176316095138395302090363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77450877396758930201393575 116176316095138395302090363)
        ·
          refine ⟨174264474142707592953135545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116176316095138395302090363 174264474142707592953135545)
          ·
            refine ⟨130698355607030694714851659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174264474142707592953135545 130698355607030694714851659)
            ·
              refine ⟨196047533410546042072277489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130698355607030694714851659 196047533410546042072277489)
              ·
                refine ⟨147035650057909531554208117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196047533410546042072277489 147035650057909531554208117)
                ·
                  refine ⟨13784592192929018583207011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147035650057909531554208117 13784592192929018583207011)
                  ·
                    refine ⟨20676888289393527874810517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13784592192929018583207011 20676888289393527874810517)
                    ·
                      refine ⟨969229138565321619131743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20676888289393527874810517 969229138565321619131743)
                      ·
                        rfl

theorem cell23_1887567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_1887567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887567 prefixEnd_1887567 := by exact prefixLift 1887567
  have htrace : WordTrace (prefixWord ++ tailWord_1887567) baseStart_1887567 baseEnd_1887567 := by
    simpa [prefixWord, tailWord_1887567, baseEnd_1887567] using wordTrace_append hprefix tailTrace_1887567
  have hstable : (prefixWord ++ tailWord_1887567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887567).length < 2 ^ (prefixWord ++ tailWord_1887567).sum := by decide
  have hdescent : baseEnd_1887567 < baseStart_1887567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887577 : List Nat := [1, 2, 1, 2, 2, 2, 2, 11]
def baseStart_1887577 : Nat := 118140960795 + 1887577 * 2 ^ 59
def prefixEnd_1887577 : Nat := 4983230072969 + 3 ^ 40 * 1887577 * 2
def baseEnd_1887577 : Nat := 35897565680439502963211

theorem tailTrace_1887577 : CollatzResearch.WordTrace tailWord_1887577 prefixEnd_1887577 35897565680439502963211 := by
  unfold tailWord_1887577
  simp only [CollatzResearch.WordTrace]
  refine ⟨68845589082638376331324985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45897059388425584220883323 68845589082638376331324985)
  ·
    refine ⟨51634191811978782248493739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68845589082638376331324985 51634191811978782248493739)
    ·
      refine ⟨77451287717968173372740609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51634191811978782248493739 77451287717968173372740609)
      ·
        refine ⟨58088465788476130029555457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77451287717968173372740609 58088465788476130029555457)
        ·
          refine ⟨43566349341357097522166593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58088465788476130029555457 43566349341357097522166593)
          ·
            refine ⟨32674762006017823141624945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43566349341357097522166593 32674762006017823141624945)
            ·
              refine ⟨24506071504513367356218709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32674762006017823141624945 24506071504513367356218709)
              ·
                refine ⟨35897565680439502963211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 24506071504513367356218709 35897565680439502963211)
                ·
                  rfl

theorem cell23_1887577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 11].length) (baseStart_1887577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887577 prefixEnd_1887577 := by exact prefixLift 1887577
  have htrace : WordTrace (prefixWord ++ tailWord_1887577) baseStart_1887577 baseEnd_1887577 := by
    simpa [prefixWord, tailWord_1887577, baseEnd_1887577] using wordTrace_append hprefix tailTrace_1887577
  have hstable : (prefixWord ++ tailWord_1887577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887577).length < 2 ^ (prefixWord ++ tailWord_1887577).sum := by decide
  have hdescent : baseEnd_1887577 < baseStart_1887577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887588 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 1, 1, 4]
def baseStart_1887588 : Nat := 118140960795 + 1887588 * 2 ^ 59
def prefixEnd_1887588 : Nat := 4983230072969 + 3 ^ 40 * 1887588 * 2
def baseEnd_1887588 : Nat := 969239921659066036969147

theorem tailTrace_1887588 : CollatzResearch.WordTrace tailWord_1887588 prefixEnd_1887588 969239921659066036969147 := by
  unfold tailWord_1887588
  simp only [CollatzResearch.WordTrace]
  refine ⟨34422995142799262604987709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45897326857065683473316945 34422995142799262604987709)
  ·
    refine ⟨12908623178549723476870391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34422995142799262604987709 12908623178549723476870391)
    ·
      refine ⟨19362934767824585215305587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12908623178549723476870391 19362934767824585215305587)
      ·
        refine ⟨29044402151736877822958381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19362934767824585215305587 29044402151736877822958381)
        ·
          refine ⟨10891650806901329183609393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29044402151736877822958381 10891650806901329183609393)
          ·
            refine ⟨8168738105175996887707045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10891650806901329183609393 8168738105175996887707045)
            ·
              refine ⟨1531638394720499416445071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8168738105175996887707045 1531638394720499416445071)
              ·
                refine ⟨2297457592080749124667607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531638394720499416445071 2297457592080749124667607)
                ·
                  refine ⟨3446186388121123687001411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297457592080749124667607 3446186388121123687001411)
                  ·
                    refine ⟨5169279582181685530502117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3446186388121123687001411 5169279582181685530502117)
                    ·
                      refine ⟨969239921659066036969147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5169279582181685530502117 969239921659066036969147)
                      ·
                        rfl

theorem cell23_1887588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_1887588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887588 prefixEnd_1887588 := by exact prefixLift 1887588
  have htrace : WordTrace (prefixWord ++ tailWord_1887588) baseStart_1887588 baseEnd_1887588 := by
    simpa [prefixWord, tailWord_1887588, baseEnd_1887588] using wordTrace_append hprefix tailTrace_1887588
  have hstable : (prefixWord ++ tailWord_1887588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887588).length < 2 ^ (prefixWord ++ tailWord_1887588).sum := by decide
  have hdescent : baseEnd_1887588 < baseStart_1887588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887618 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1887618 : Nat := 118140960795 + 1887618 * 2 ^ 59
def prefixEnd_1887618 : Nat := 4983230072969 + 3 ^ 40 * 1887618 * 2
def baseEnd_1887618 : Nat := 969255326078700919594009

theorem tailTrace_1887618 : CollatzResearch.WordTrace tailWord_1887618 prefixEnd_1887618 969255326078700919594009 := by
  unfold tailWord_1887618
  simp only [CollatzResearch.WordTrace]
  refine ⟨17211771118872460083391877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45898056316993226889045005 17211771118872460083391877)
  ·
    refine ⟨3227207084788586265635977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17211771118872460083391877 3227207084788586265635977)
    ·
      refine ⟨2420405313591439699226983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3227207084788586265635977 2420405313591439699226983)
      ·
        refine ⟨3630607970387159548840475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420405313591439699226983 3630607970387159548840475)
        ·
          refine ⟨5445911955580739323260713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3630607970387159548840475 5445911955580739323260713)
          ·
            refine ⟨4084433966685554492445535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5445911955580739323260713 4084433966685554492445535)
            ·
              refine ⟨6126650950028331738668303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084433966685554492445535 6126650950028331738668303)
              ·
                refine ⟨9189976425042497608002455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6126650950028331738668303 9189976425042497608002455)
                ·
                  refine ⟨13784964637563746412003683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9189976425042497608002455 13784964637563746412003683)
                  ·
                    refine ⟨20677446956345619618005525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13784964637563746412003683 20677446956345619618005525)
                    ·
                      refine ⟨969255326078700919594009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20677446956345619618005525 969255326078700919594009)
                      ·
                        rfl

theorem cell23_1887618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1887618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887618 prefixEnd_1887618 := by exact prefixLift 1887618
  have htrace : WordTrace (prefixWord ++ tailWord_1887618) baseStart_1887618 baseEnd_1887618 := by
    simpa [prefixWord, tailWord_1887618, baseEnd_1887618] using wordTrace_append hprefix tailTrace_1887618
  have hstable : (prefixWord ++ tailWord_1887618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887618).length < 2 ^ (prefixWord ++ tailWord_1887618).sum := by decide
  have hdescent : baseEnd_1887618 < baseStart_1887618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887621 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 1, 3, 3]
def baseStart_1887621 : Nat := 118140960795 + 1887621 * 2 ^ 59
def prefixEnd_1887621 : Nat := 4983230072969 + 3 ^ 40 * 1887621 * 2
def baseEnd_1887621 : Nat := 969256866520664407856495

theorem tailTrace_1887621 : CollatzResearch.WordTrace tailWord_1887621 prefixEnd_1887621 969256866520664407856495 := by
  unfold tailWord_1887621
  simp only [CollatzResearch.WordTrace]
  refine ⟨68847193894478971845926717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45898129262985981230617811 68847193894478971845926717)
  ·
    refine ⟨25817697710429614442222519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68847193894478971845926717 25817697710429614442222519)
    ·
      refine ⟨38726546565644421663333779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25817697710429614442222519 38726546565644421663333779)
      ·
        refine ⟨58089819848466632495000669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38726546565644421663333779 58089819848466632495000669)
        ·
          refine ⟨21783682443174987185625251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58089819848466632495000669 21783682443174987185625251)
          ·
            refine ⟨32675523664762480778437877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21783682443174987185625251 32675523664762480778437877)
            ·
              refine ⟨3063330343571482572978551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32675523664762480778437877 3063330343571482572978551)
              ·
                refine ⟨4594995515357223859467827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063330343571482572978551 4594995515357223859467827)
                ·
                  refine ⟨6892493273035835789201741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4594995515357223859467827 6892493273035835789201741)
                  ·
                    refine ⟨2584684977388438420950653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6892493273035835789201741 2584684977388438420950653)
                    ·
                      refine ⟨969256866520664407856495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2584684977388438420950653 969256866520664407856495)
                      ·
                        rfl

theorem cell23_1887621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_1887621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887621 prefixEnd_1887621 := by exact prefixLift 1887621
  have htrace : WordTrace (prefixWord ++ tailWord_1887621) baseStart_1887621 baseEnd_1887621 := by
    simpa [prefixWord, tailWord_1887621, baseEnd_1887621] using wordTrace_append hprefix tailTrace_1887621
  have hstable : (prefixWord ++ tailWord_1887621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887621).length < 2 ^ (prefixWord ++ tailWord_1887621).sum := by decide
  have hdescent : baseEnd_1887621 < baseStart_1887621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887648 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 1, 3, 2]
def baseStart_1887648 : Nat := 118140960795 + 1887648 * 2 ^ 59
def prefixEnd_1887648 : Nat := 4983230072969 + 3 ^ 40 * 1887648 * 2
def baseEnd_1887648 : Nat := 969270730498335802218871

theorem tailTrace_1887648 : CollatzResearch.WordTrace tailWord_1887648 prefixEnd_1887648 969270730498335802218871 := by
  unfold tailWord_1887648
  simp only [CollatzResearch.WordTrace]
  refine ⟨34424089332690577728579799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45898785776920770304773065 34424089332690577728579799)
  ·
    refine ⟨51636133999035866592869699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34424089332690577728579799 51636133999035866592869699)
    ·
      refine ⟨77454200998553799889304549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51636133999035866592869699 77454200998553799889304549)
      ·
        refine ⟨14522662687228837479244603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77454200998553799889304549 14522662687228837479244603)
        ·
          refine ⟨21783994030843256218866905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14522662687228837479244603 21783994030843256218866905)
          ·
            refine ⟨16337995523132442164150179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21783994030843256218866905 16337995523132442164150179)
            ·
              refine ⟨24506993284698663246225269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16337995523132442164150179 24506993284698663246225269)
              ·
                refine ⟨2297530620440499679333619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24506993284698663246225269 2297530620440499679333619)
                ·
                  refine ⟨3446295930660749519000429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297530620440499679333619 3446295930660749519000429)
                  ·
                    refine ⟨1292360973997781069625161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3446295930660749519000429 1292360973997781069625161)
                    ·
                      refine ⟨969270730498335802218871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292360973997781069625161 969270730498335802218871)
                      ·
                        rfl

theorem cell23_1887648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_1887648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887648 prefixEnd_1887648 := by exact prefixLift 1887648
  have htrace : WordTrace (prefixWord ++ tailWord_1887648) baseStart_1887648 baseEnd_1887648 := by
    simpa [prefixWord, tailWord_1887648, baseEnd_1887648] using wordTrace_append hprefix tailTrace_1887648
  have hstable : (prefixWord ++ tailWord_1887648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887648).length < 2 ^ (prefixWord ++ tailWord_1887648).sum := by decide
  have hdescent : baseEnd_1887648 < baseStart_1887648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887656 : List Nat := [2, 1, 6, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_1887656 : Nat := 118140960795 + 1887656 * 2 ^ 59
def prefixEnd_1887656 : Nat := 4983230072969 + 3 ^ 40 * 1887656 * 2
def baseEnd_1887656 : Nat := 969274838343571770918835

theorem tailTrace_1887656 : CollatzResearch.WordTrace tailWord_1887656 prefixEnd_1887656 969274838343571770918835 := by
  unfold tailWord_1887656
  simp only [CollatzResearch.WordTrace]
  refine ⟨34424235224676086411725411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45898980299568115215633881 34424235224676086411725411)
  ·
    refine ⟨51636352837014129617588117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34424235224676086411725411 51636352837014129617588117)
    ·
      refine ⟨2420454039235037325824443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51636352837014129617588117 2420454039235037325824443)
      ·
        refine ⟨3630681058852555988736665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420454039235037325824443 3630681058852555988736665)
        ·
          refine ⟨2723010794139416991552499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3630681058852555988736665 2723010794139416991552499)
          ·
            refine ⟨4084516191209125487328749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723010794139416991552499 4084516191209125487328749)
            ·
              refine ⟨1531693571703422057748281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4084516191209125487328749 1531693571703422057748281)
              ·
                refine ⟨1148770178777566543311211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531693571703422057748281 1148770178777566543311211)
                ·
                  refine ⟨1723155268166349814966817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1148770178777566543311211 1723155268166349814966817)
                  ·
                    refine ⟨1292366451124762361225113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1723155268166349814966817 1292366451124762361225113)
                    ·
                      refine ⟨969274838343571770918835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292366451124762361225113 969274838343571770918835)
                      ·
                        rfl

theorem cell23_1887656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_1887656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887656 prefixEnd_1887656 := by exact prefixLift 1887656
  have htrace : WordTrace (prefixWord ++ tailWord_1887656) baseStart_1887656 baseEnd_1887656 := by
    simpa [prefixWord, tailWord_1887656, baseEnd_1887656] using wordTrace_append hprefix tailTrace_1887656
  have hstable : (prefixWord ++ tailWord_1887656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887656).length < 2 ^ (prefixWord ++ tailWord_1887656).sum := by decide
  have hdescent : baseEnd_1887656 < baseStart_1887656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887678 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_1887678 : Nat := 118140960795 + 1887678 * 2 ^ 59
def prefixEnd_1887678 : Nat := 4983230072969 + 3 ^ 40 * 1887678 * 2
def baseEnd_1887678 : Nat := 969286134917970684843733

theorem tailTrace_1887678 : CollatzResearch.WordTrace tailWord_1887678 prefixEnd_1887678 969286134917970684843733 := by
  unfold tailWord_1887678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8606159106909058822593961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45899515236848313720501125 8606159106909058822593961)
  ·
    refine ⟨6454619330181794116945471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8606159106909058822593961 6454619330181794116945471)
    ·
      refine ⟨9681928995272691175418207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6454619330181794116945471 9681928995272691175418207)
      ·
        refine ⟨14522893492909036763127311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9681928995272691175418207 14522893492909036763127311)
        ·
          refine ⟨21784340239363555144690967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14522893492909036763127311 21784340239363555144690967)
          ·
            refine ⟨32676510359045332717036451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21784340239363555144690967 32676510359045332717036451)
            ·
              refine ⟨49014765538567999075554677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32676510359045332717036451 49014765538567999075554677)
              ·
                refine ⟨4595134269240749913333251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49014765538567999075554677 4595134269240749913333251)
                ·
                  refine ⟨6892701403861124869999877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595134269240749913333251 6892701403861124869999877)
                  ·
                    refine ⟨1292381513223960913124977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6892701403861124869999877 1292381513223960913124977)
                    ·
                      refine ⟨969286134917970684843733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292381513223960913124977 969286134917970684843733)
                      ·
                        rfl

theorem cell23_1887678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_1887678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887678 prefixEnd_1887678 := by exact prefixLift 1887678
  have htrace : WordTrace (prefixWord ++ tailWord_1887678) baseStart_1887678 baseEnd_1887678 := by
    simpa [prefixWord, tailWord_1887678, baseEnd_1887678] using wordTrace_append hprefix tailTrace_1887678
  have hstable : (prefixWord ++ tailWord_1887678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887678).length < 2 ^ (prefixWord ++ tailWord_1887678).sum := by decide
  have hdescent : baseEnd_1887678 < baseStart_1887678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887711 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 3]
def baseStart_1887711 : Nat := 118140960795 + 1887711 * 2 ^ 59
def prefixEnd_1887711 : Nat := 4983230072969 + 3 ^ 40 * 1887711 * 2
def baseEnd_1887711 : Nat := 969303079779569055731081

theorem tailTrace_1887711 : CollatzResearch.WordTrace tailWord_1887711 prefixEnd_1887711 969303079779569055731081 := by
  unfold tailWord_1887711
  simp only [CollatzResearch.WordTrace]
  refine ⟨68850476464152917216702987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45900317642768611477801991 68850476464152917216702987)
  ·
    refine ⟨103275714696229375825054481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68850476464152917216702987 103275714696229375825054481)
    ·
      refine ⟨77456786022172031868790861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103275714696229375825054481 77456786022172031868790861)
      ·
        refine ⟨29046294758314511950796573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77456786022172031868790861 29046294758314511950796573)
        ·
          refine ⟨10892360534367941981548715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29046294758314511950796573 10892360534367941981548715)
          ·
            refine ⟨16338540801551912972323073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10892360534367941981548715 16338540801551912972323073)
            ·
              refine ⟨12253905601163934729242305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16338540801551912972323073 12253905601163934729242305)
              ·
                refine ⟨9190429200872951046931729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12253905601163934729242305 9190429200872951046931729)
                ·
                  refine ⟨6892821900654713285198797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9190429200872951046931729 6892821900654713285198797)
                  ·
                    refine ⟨2584808212745517481949549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6892821900654713285198797 2584808212745517481949549)
                    ·
                      refine ⟨969303079779569055731081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2584808212745517481949549 969303079779569055731081)
                      ·
                        rfl

theorem cell23_1887711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_1887711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887711 prefixEnd_1887711 := by exact prefixLift 1887711
  have htrace : WordTrace (prefixWord ++ tailWord_1887711) baseStart_1887711 baseEnd_1887711 := by
    simpa [prefixWord, tailWord_1887711, baseEnd_1887711] using wordTrace_append hprefix tailTrace_1887711
  have hstable : (prefixWord ++ tailWord_1887711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887711).length < 2 ^ (prefixWord ++ tailWord_1887711).sum := by decide
  have hdescent : baseEnd_1887711 < baseStart_1887711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887724 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_1887724 : Nat := 118140960795 + 1887724 * 2 ^ 59
def prefixEnd_1887724 : Nat := 4983230072969 + 3 ^ 40 * 1887724 * 2
def baseEnd_1887724 : Nat := 969309755028077504868521

theorem tailTrace_1887724 : CollatzResearch.WordTrace tailWord_1887724 prefixEnd_1887724 969309755028077504868521 := by
  unfold tailWord_1887724
  simp only [CollatzResearch.WordTrace]
  refine ⟨34425475306552910218463113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45900633742070546957950817 34425475306552910218463113)
  ·
    refine ⟨25819106479914682663847335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34425475306552910218463113 25819106479914682663847335)
    ·
      refine ⟨38728659719872023995771003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25819106479914682663847335 38728659719872023995771003)
      ·
        refine ⟨58092989579808035993656505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38728659719872023995771003 58092989579808035993656505)
        ·
          refine ⟨43569742184856026995242379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58092989579808035993656505 43569742184856026995242379)
          ·
            refine ⟨65354613277284040492863569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43569742184856026995242379 65354613277284040492863569)
            ·
              refine ⟨49015959957963030369647677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65354613277284040492863569 49015959957963030369647677)
              ·
                refine ⟨18380984984236136388617879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49015959957963030369647677 18380984984236136388617879)
                ·
                  refine ⟨27571477476354204582926819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18380984984236136388617879 27571477476354204582926819)
                  ·
                    refine ⟨41357216214531306874390229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27571477476354204582926819 41357216214531306874390229)
                    ·
                      refine ⟨969309755028077504868521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41357216214531306874390229 969309755028077504868521)
                      ·
                        rfl

theorem cell23_1887724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_1887724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887724 prefixEnd_1887724 := by exact prefixLift 1887724
  have htrace : WordTrace (prefixWord ++ tailWord_1887724) baseStart_1887724 baseEnd_1887724 := by
    simpa [prefixWord, tailWord_1887724, baseEnd_1887724] using wordTrace_append hprefix tailTrace_1887724
  have hstable : (prefixWord ++ tailWord_1887724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887724).length < 2 ^ (prefixWord ++ tailWord_1887724).sum := by decide
  have hdescent : baseEnd_1887724 < baseStart_1887724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887748 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1887748 : Nat := 118140960795 + 1887748 * 2 ^ 59
def prefixEnd_1887748 : Nat := 4983230072969 + 3 ^ 40 * 1887748 * 2
def baseEnd_1887748 : Nat := 323107359521261803656137

theorem tailTrace_1887748 : CollatzResearch.WordTrace tailWord_1887748 prefixEnd_1887748 323107359521261803656137 := by
  unfold tailWord_1887748
  simp only [CollatzResearch.WordTrace]
  refine ⟨34425912982509436267899949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45901217310012581690533265 34425912982509436267899949)
  ·
    refine ⟨12909717368441038600462481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34425912982509436267899949 12909717368441038600462481)
    ·
      refine ⟨9682288026330778950346861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12909717368441038600462481 9682288026330778950346861)
      ·
        refine ⟨3630858009874042106380073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9682288026330778950346861 3630858009874042106380073)
        ·
          refine ⟨2723143507405531579785055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3630858009874042106380073 2723143507405531579785055)
          ·
            refine ⟨4084715261108297369677583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723143507405531579785055 4084715261108297369677583)
            ·
              refine ⟨6127072891662446054516375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084715261108297369677583 6127072891662446054516375)
              ·
                refine ⟨9190609337493669081774563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6127072891662446054516375 9190609337493669081774563)
                ·
                  refine ⟨13785914006240503622661845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9190609337493669081774563 13785914006240503622661845)
                  ·
                    refine ⟨323107359521261803656137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13785914006240503622661845 323107359521261803656137)
                    ·
                      rfl

theorem cell23_1887748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1887748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887748 prefixEnd_1887748 := by exact prefixLift 1887748
  have htrace : WordTrace (prefixWord ++ tailWord_1887748) baseStart_1887748 baseEnd_1887748 := by
    simpa [prefixWord, tailWord_1887748, baseEnd_1887748] using wordTrace_append hprefix tailTrace_1887748
  have hstable : (prefixWord ++ tailWord_1887748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887748).length < 2 ^ (prefixWord ++ tailWord_1887748).sum := by decide
  have hdescent : baseEnd_1887748 < baseStart_1887748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887750 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_1887750 : Nat := 118140960795 + 1887750 * 2 ^ 59
def prefixEnd_1887750 : Nat := 4983230072969 + 3 ^ 40 * 1887750 * 2
def baseEnd_1887750 : Nat := 969323105525094403143403

theorem tailTrace_1887750 : CollatzResearch.WordTrace tailWord_1887750 prefixEnd_1887750 969323105525094403143403 := by
  unfold tailWord_1887750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2151621840969113339917897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45901265940674417918248469 2151621840969113339917897)
  ·
    refine ⟨1613716380726835004938423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2151621840969113339917897 1613716380726835004938423)
    ·
      refine ⟨2420574571090252507407635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1613716380726835004938423 2420574571090252507407635)
      ·
        refine ⟨3630861856635378761111453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420574571090252507407635 3630861856635378761111453)
        ·
          refine ⟨1361573196238267035416795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3630861856635378761111453 1361573196238267035416795)
          ·
            refine ⟨2042359794357400553125193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361573196238267035416795 2042359794357400553125193)
            ·
              refine ⟨1531769845768050414843895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2042359794357400553125193 1531769845768050414843895)
              ·
                refine ⟨2297654768652075622265843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531769845768050414843895 2297654768652075622265843)
                ·
                  refine ⟨3446482152978113433398765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297654768652075622265843 3446482152978113433398765)
                  ·
                    refine ⟨1292430807366792537524537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3446482152978113433398765 1292430807366792537524537)
                    ·
                      refine ⟨969323105525094403143403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292430807366792537524537 969323105525094403143403)
                      ·
                        rfl

theorem cell23_1887750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_1887750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887750 prefixEnd_1887750 := by exact prefixLift 1887750
  have htrace : WordTrace (prefixWord ++ tailWord_1887750) baseStart_1887750 baseEnd_1887750 := by
    simpa [prefixWord, tailWord_1887750, baseEnd_1887750] using wordTrace_append hprefix tailTrace_1887750
  have hstable : (prefixWord ++ tailWord_1887750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887750).length < 2 ^ (prefixWord ++ tailWord_1887750).sum := by decide
  have hdescent : baseEnd_1887750 < baseStart_1887750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887761 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 5, 4]
def baseStart_1887761 : Nat := 118140960795 + 1887761 * 2 ^ 59
def prefixEnd_1887761 : Nat := 4983230072969 + 3 ^ 40 * 1887761 * 2
def baseEnd_1887761 : Nat := 323109584604097953368617

theorem tailTrace_1887761 : CollatzResearch.WordTrace tailWord_1887761 prefixEnd_1887761 323109584604097953368617 := by
  unfold tailWord_1887761
  simp only [CollatzResearch.WordTrace]
  refine ⟨68852300113971775756023137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45901533409314517170682091 68852300113971775756023137)
  ·
    refine ⟨51639225085478831817017353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68852300113971775756023137 51639225085478831817017353)
    ·
      refine ⟨38729418814109123862763015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51639225085478831817017353 38729418814109123862763015)
      ·
        refine ⟨58094128221163685794144523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38729418814109123862763015 58094128221163685794144523)
        ·
          refine ⟨87141192331745528691216785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58094128221163685794144523 87141192331745528691216785)
          ·
            refine ⟨65355894248809146518412589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87141192331745528691216785 65355894248809146518412589)
            ·
              refine ⟨24508460343303429944404721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65355894248809146518412589 24508460343303429944404721)
              ·
                refine ⟨18381345257477572458303541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24508460343303429944404721 18381345257477572458303541)
                ·
                  refine ⟨1723251117888522417965957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18381345257477572458303541 1723251117888522417965957)
                  ·
                    refine ⟨323109584604097953368617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723251117888522417965957 323109584604097953368617)
                    ·
                      rfl

theorem cell23_1887761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_1887761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887761 prefixEnd_1887761 := by exact prefixLift 1887761
  have htrace : WordTrace (prefixWord ++ tailWord_1887761) baseStart_1887761 baseEnd_1887761 := by
    simpa [prefixWord, tailWord_1887761, baseEnd_1887761] using wordTrace_append hprefix tailTrace_1887761
  have hstable : (prefixWord ++ tailWord_1887761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887761).length < 2 ^ (prefixWord ++ tailWord_1887761).sum := by decide
  have hdescent : baseEnd_1887761 < baseStart_1887761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887778 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_1887778 : Nat := 118140960795 + 1887778 * 2 ^ 59
def prefixEnd_1887778 : Nat := 4983230072969 + 3 ^ 40 * 1887778 * 2
def baseEnd_1887778 : Nat := 323112494327806764531091

theorem tailTrace_1887778 : CollatzResearch.WordTrace tailWord_1887778 prefixEnd_1887778 323112494327806764531091 := by
  unfold tailWord_1887778
  simp only [CollatzResearch.WordTrace]
  refine ⟨17213230038727546914847997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45901946769940125106261325 17213230038727546914847997)
  ·
    refine ⟨6454961264522830093067999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17213230038727546914847997 6454961264522830093067999)
    ·
      refine ⟨9682441896784245139601999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6454961264522830093067999 9682441896784245139601999)
      ·
        refine ⟨14523662845176367709402999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9682441896784245139601999 14523662845176367709402999)
        ·
          refine ⟨21785494267764551564104499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14523662845176367709402999 21785494267764551564104499)
          ·
            refine ⟨32678241401646827346156749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21785494267764551564104499 32678241401646827346156749)
            ·
              refine ⟨12254340525617560254808781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32678241401646827346156749 12254340525617560254808781)
              ·
                refine ⟨4595377697106585095553293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12254340525617560254808781 4595377697106585095553293)
                ·
                  refine ⟨1723266636414969410832485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4595377697106585095553293 1723266636414969410832485)
                  ·
                    refine ⟨323112494327806764531091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723266636414969410832485 323112494327806764531091)
                    ·
                      rfl

theorem cell23_1887778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_1887778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887778 prefixEnd_1887778 := by exact prefixLift 1887778
  have htrace : WordTrace (prefixWord ++ tailWord_1887778) baseStart_1887778 baseEnd_1887778 := by
    simpa [prefixWord, tailWord_1887778, baseEnd_1887778] using wordTrace_append hprefix tailTrace_1887778
  have hstable : (prefixWord ++ tailWord_1887778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887778).length < 2 ^ (prefixWord ++ tailWord_1887778).sum := by decide
  have hdescent : baseEnd_1887778 < baseStart_1887778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887862 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_1887862 : Nat := 118140960795 + 1887862 * 2 ^ 59
def prefixEnd_1887862 : Nat := 4983230072969 + 3 ^ 40 * 1887862 * 2
def baseEnd_1887862 : Nat := 969380615358397964942887

theorem tailTrace_1887862 : CollatzResearch.WordTrace tailWord_1887862 prefixEnd_1887862 969380615358397964942887 := by
  unfold tailWord_1887862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4303498992912866875340615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45903989257737246670299893 4303498992912866875340615)
  ·
    refine ⟨6455248489369300313010923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4303498992912866875340615 6455248489369300313010923)
    ·
      refine ⟨9682872734053950469516385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6455248489369300313010923 9682872734053950469516385)
      ·
        refine ⟨7262154550540462852137289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9682872734053950469516385 7262154550540462852137289)
        ·
          refine ⟨5446615912905347139102967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7262154550540462852137289 5446615912905347139102967)
          ·
            refine ⟨8169923869358020708654451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5446615912905347139102967 8169923869358020708654451)
            ·
              refine ⟨12254885804037031062981677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8169923869358020708654451 12254885804037031062981677)
              ·
                refine ⟨4595582176513886648618129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12254885804037031062981677 4595582176513886648618129)
                ·
                  refine ⟨3446686632385414986463597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4595582176513886648618129 3446686632385414986463597)
                  ·
                    refine ⟨1292507487144530619923849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3446686632385414986463597 1292507487144530619923849)
                    ·
                      refine ⟨969380615358397964942887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292507487144530619923849 969380615358397964942887)
                      ·
                        rfl

theorem cell23_1887862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_1887862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887862 prefixEnd_1887862 := by exact prefixLift 1887862
  have htrace : WordTrace (prefixWord ++ tailWord_1887862) baseStart_1887862 baseEnd_1887862 := by
    simpa [prefixWord, tailWord_1887862, baseEnd_1887862] using wordTrace_append hprefix tailTrace_1887862
  have hstable : (prefixWord ++ tailWord_1887862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887862).length < 2 ^ (prefixWord ++ tailWord_1887862).sum := by decide
  have hdescent : baseEnd_1887862 < baseStart_1887862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887886 : List Nat := [4, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3]
def baseStart_1887886 : Nat := 118140960795 + 1887886 * 2 ^ 59
def prefixEnd_1887886 : Nat := 4983230072969 + 3 ^ 40 * 1887886 * 2
def baseEnd_1887886 : Nat := 969392938894105871042777

theorem tailTrace_1887886 : CollatzResearch.WordTrace tailWord_1887886 prefixEnd_1887886 969392938894105871042777 := by
  unfold tailWord_1887886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8607107404814865263040439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45904572825679281402882341 8607107404814865263040439)
  ·
    refine ⟨12910661107222297894560659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8607107404814865263040439 12910661107222297894560659)
    ·
      refine ⟨19365991660833446841840989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12910661107222297894560659 19365991660833446841840989)
      ·
        refine ⟨7262246872812542565690371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19365991660833446841840989 7262246872812542565690371)
        ·
          refine ⟨10893370309218813848535557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7262246872812542565690371 10893370309218813848535557)
          ·
            refine ⟨2042506932978527596600417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10893370309218813848535557 2042506932978527596600417)
            ·
              refine ⟨1531880199733895697450313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2042506932978527596600417 1531880199733895697450313)
              ·
                refine ⟨1148910149800421773087735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531880199733895697450313 1148910149800421773087735)
                ·
                  refine ⟨1723365224700632659631603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1148910149800421773087735 1723365224700632659631603)
                  ·
                    refine ⟨2585047837050948989447405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1723365224700632659631603 2585047837050948989447405)
                    ·
                      refine ⟨969392938894105871042777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2585047837050948989447405 969392938894105871042777)
                      ·
                        rfl

theorem cell23_1887886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_1887886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887886 prefixEnd_1887886 := by exact prefixLift 1887886
  have htrace : WordTrace (prefixWord ++ tailWord_1887886) baseStart_1887886 baseEnd_1887886 := by
    simpa [prefixWord, tailWord_1887886, baseEnd_1887886] using wordTrace_append hprefix tailTrace_1887886
  have hstable : (prefixWord ++ tailWord_1887886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887886).length < 2 ^ (prefixWord ++ tailWord_1887886).sum := by decide
  have hdescent : baseEnd_1887886 < baseStart_1887886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887902 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1887902 : Nat := 118140960795 + 1887902 * 2 ^ 59
def prefixEnd_1887902 : Nat := 4983230072969 + 3 ^ 40 * 1887902 * 2
def baseEnd_1887902 : Nat := 323133718194859269480901

theorem tailTrace_1887902 : CollatzResearch.WordTrace tailWord_1887902 prefixEnd_1887902 323133718194859269480901 := by
  unfold tailWord_1887902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8607180350807619604613245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45904961870973971224603973 8607180350807619604613245)
  ·
    refine ⟨3227692631552857351729967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8607180350807619604613245 3227692631552857351729967)
    ·
      refine ⟨4841538947329286027594951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3227692631552857351729967 4841538947329286027594951)
      ·
        refine ⟨7262308420993929041392427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4841538947329286027594951 7262308420993929041392427)
        ·
          refine ⟨10893462631490893562088641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7262308420993929041392427 10893462631490893562088641)
          ·
            refine ⟨8170096973618170171566481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10893462631490893562088641 8170096973618170171566481)
            ·
              refine ⟨6127572730213627628674861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8170096973618170171566481 6127572730213627628674861)
              ·
                refine ⟨2297839773830110360753073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6127572730213627628674861 2297839773830110360753073)
                ·
                  refine ⟨1723379830372582770564805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2297839773830110360753073 1723379830372582770564805)
                  ·
                    refine ⟨323133718194859269480901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723379830372582770564805 323133718194859269480901)
                    ·
                      rfl

theorem cell23_1887902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1887902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887902 prefixEnd_1887902 := by exact prefixLift 1887902
  have htrace : WordTrace (prefixWord ++ tailWord_1887902) baseStart_1887902 baseEnd_1887902 := by
    simpa [prefixWord, tailWord_1887902, baseEnd_1887902] using wordTrace_append hprefix tailTrace_1887902
  have hstable : (prefixWord ++ tailWord_1887902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887902).length < 2 ^ (prefixWord ++ tailWord_1887902).sum := by decide
  have hdescent : baseEnd_1887902 < baseStart_1887902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887905 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1887905 : Nat := 118140960795 + 1887905 * 2 ^ 59
def prefixEnd_1887905 : Nat := 4983230072969 + 3 ^ 40 * 1887905 * 2
def baseEnd_1887905 : Nat := 969402695026541296705189

theorem tailTrace_1887905 : CollatzResearch.WordTrace tailWord_1887905 prefixEnd_1887905 969402695026541296705189 := by
  unfold tailWord_1887905
  simp only [CollatzResearch.WordTrace]
  refine ⟨68857552225450088349265169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45905034816966725566176779 68857552225450088349265169)
  ·
    refine ⟨51643164169087566261948877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68857552225450088349265169 51643164169087566261948877)
    ·
      refine ⟨19366186563407837348230829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51643164169087566261948877 19366186563407837348230829)
      ·
        refine ⟨7262319961277939005586561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19366186563407837348230829 7262319961277939005586561)
        ·
          refine ⟨5446739970958454254189921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7262319961277939005586561 5446739970958454254189921)
          ·
            refine ⟨4085054978218840690642441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5446739970958454254189921 4085054978218840690642441)
            ·
              refine ⟨3063791233664130517981831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4085054978218840690642441 3063791233664130517981831)
              ·
                refine ⟨4595686850496195776972747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063791233664130517981831 4595686850496195776972747)
                ·
                  refine ⟨6893530275744293665459121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595686850496195776972747 6893530275744293665459121)
                  ·
                    refine ⟨5170147706808220249094341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6893530275744293665459121 5170147706808220249094341)
                    ·
                      refine ⟨969402695026541296705189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5170147706808220249094341 969402695026541296705189)
                      ·
                        rfl

theorem cell23_1887905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1887905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887905 prefixEnd_1887905 := by exact prefixLift 1887905
  have htrace : WordTrace (prefixWord ++ tailWord_1887905) baseStart_1887905 baseEnd_1887905 := by
    simpa [prefixWord, tailWord_1887905, baseEnd_1887905] using wordTrace_append hprefix tailTrace_1887905
  have hstable : (prefixWord ++ tailWord_1887905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887905).length < 2 ^ (prefixWord ++ tailWord_1887905).sum := by decide
  have hdescent : baseEnd_1887905 < baseStart_1887905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887926 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_1887926 : Nat := 118140960795 + 1887926 * 2 ^ 59
def prefixEnd_1887926 : Nat := 4983230072969 + 3 ^ 40 * 1887926 * 2
def baseEnd_1887926 : Nat := 969413478120285714542593

theorem tailTrace_1887926 : CollatzResearch.WordTrace tailWord_1887926 prefixEnd_1887926 969413478120285714542593 := by
  unfold tailWord_1887926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4303644884898375558486227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45905545438916005957186421 4303644884898375558486227)
  ·
    refine ⟨6455467327347563337729341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4303644884898375558486227 6455467327347563337729341)
    ·
      refine ⟨2420800247755336251648503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6455467327347563337729341 2420800247755336251648503)
      ·
        refine ⟨3631200371633004377472755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420800247755336251648503 3631200371633004377472755)
        ·
          refine ⟨5446800557449506566209133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3631200371633004377472755 5446800557449506566209133)
          ·
            refine ⟨2042550209043564962328425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5446800557449506566209133 2042550209043564962328425)
            ·
              refine ⟨1531912656782673721746319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2042550209043564962328425 1531912656782673721746319)
              ·
                refine ⟨2297868985174010582619479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531912656782673721746319 2297868985174010582619479)
                ·
                  refine ⟨3446803477761015873929219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297868985174010582619479 3446803477761015873929219)
                  ·
                    refine ⟨5170205216641523810893829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3446803477761015873929219 5170205216641523810893829)
                    ·
                      refine ⟨969413478120285714542593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5170205216641523810893829 969413478120285714542593)
                      ·
                        rfl

theorem cell23_1887926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_1887926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887926 prefixEnd_1887926 := by exact prefixLift 1887926
  have htrace : WordTrace (prefixWord ++ tailWord_1887926) baseStart_1887926 baseEnd_1887926 := by
    simpa [prefixWord, tailWord_1887926, baseEnd_1887926] using wordTrace_append hprefix tailTrace_1887926
  have hstable : (prefixWord ++ tailWord_1887926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887926).length < 2 ^ (prefixWord ++ tailWord_1887926).sum := by decide
  have hdescent : baseEnd_1887926 < baseStart_1887926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887941 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_1887941 : Nat := 118140960795 + 1887941 * 2 ^ 59
def prefixEnd_1887941 : Nat := 4983230072969 + 3 ^ 40 * 1887941 * 2
def baseEnd_1887941 : Nat := 323140393443367718618341

theorem tailTrace_1887941 : CollatzResearch.WordTrace tailWord_1887941 prefixEnd_1887941 323140393443367718618341 := by
  unfold tailWord_1887941
  simp only [CollatzResearch.WordTrace]
  refine ⟨68858865253319666497575677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45905910168879777665050451 68858865253319666497575677)
  ·
    refine ⟨25822074469994874936590879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68858865253319666497575677 25822074469994874936590879)
    ·
      refine ⟨38733111704992312404886319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25822074469994874936590879 38733111704992312404886319)
      ·
        refine ⟨58099667557488468607329479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38733111704992312404886319 58099667557488468607329479)
        ·
          refine ⟨87149501336232702910994219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58099667557488468607329479 87149501336232702910994219)
          ·
            refine ⟨130724252004349054366491329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87149501336232702910994219 130724252004349054366491329)
            ·
              refine ⟨98043189003261790774868497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130724252004349054366491329 98043189003261790774868497)
              ·
                refine ⟨73532391752446343081151373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98043189003261790774868497 73532391752446343081151373)
                ·
                  refine ⟨27574646907167378655431765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73532391752446343081151373 27574646907167378655431765)
                  ·
                    refine ⟨323140393443367718618341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27574646907167378655431765 323140393443367718618341)
                    ·
                      rfl

theorem cell23_1887941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_1887941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887941 prefixEnd_1887941 := by exact prefixLift 1887941
  have htrace : WordTrace (prefixWord ++ tailWord_1887941) baseStart_1887941 baseEnd_1887941 := by
    simpa [prefixWord, tailWord_1887941, baseEnd_1887941] using wordTrace_append hprefix tailTrace_1887941
  have hstable : (prefixWord ++ tailWord_1887941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887941).length < 2 ^ (prefixWord ++ tailWord_1887941).sum := by decide
  have hdescent : baseEnd_1887941 < baseStart_1887941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887968 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 3]
def baseStart_1887968 : Nat := 118140960795 + 1887968 * 2 ^ 59
def prefixEnd_1887968 : Nat := 4983230072969 + 3 ^ 40 * 1887968 * 2
def baseEnd_1887968 : Nat := 969435044307774550217399

theorem tailTrace_1887968 : CollatzResearch.WordTrace tailWord_1887968 prefixEnd_1887968 969435044307774550217399 := by
  unfold tailWord_1887968
  simp only [CollatzResearch.WordTrace]
  refine ⟨34429925012110925054404279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45906566682814566739205705 34429925012110925054404279)
  ·
    refine ⟨51644887518166387581606419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34429925012110925054404279 51644887518166387581606419)
    ·
      refine ⟨77467331277249581372409629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51644887518166387581606419 77467331277249581372409629)
      ·
        refine ⟨29050249228968593014653611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77467331277249581372409629 29050249228968593014653611)
        ·
          refine ⟨43575373843452889521980417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29050249228968593014653611 43575373843452889521980417)
          ·
            refine ⟨32681530382589667141485313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43575373843452889521980417 32681530382589667141485313)
            ·
              refine ⟨24511147786942250356113985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32681530382589667141485313 24511147786942250356113985)
              ·
                refine ⟨18383360840206687767085489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24511147786942250356113985 18383360840206687767085489)
                ·
                  refine ⟨13787520630155015825314117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18383360840206687767085489 13787520630155015825314117)
                  ·
                    refine ⟨2585160118154065467246397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13787520630155015825314117 2585160118154065467246397)
                    ·
                      refine ⟨969435044307774550217399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2585160118154065467246397 969435044307774550217399)
                      ·
                        rfl

theorem cell23_1887968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_1887968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887968 prefixEnd_1887968 := by exact prefixLift 1887968
  have htrace : WordTrace (prefixWord ++ tailWord_1887968) baseStart_1887968 baseEnd_1887968 := by
    simpa [prefixWord, tailWord_1887968, baseEnd_1887968] using wordTrace_append hprefix tailTrace_1887968
  have hstable : (prefixWord ++ tailWord_1887968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887968).length < 2 ^ (prefixWord ++ tailWord_1887968).sum := by decide
  have hdescent : baseEnd_1887968 < baseStart_1887968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887969 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 1, 3, 2]
def baseStart_1887969 : Nat := 118140960795 + 1887969 * 2 ^ 59
def prefixEnd_1887969 : Nat := 4983230072969 + 3 ^ 40 * 1887969 * 2
def baseEnd_1887969 : Nat := 969435557788429046304895

theorem tailTrace_1887969 : CollatzResearch.WordTrace tailWord_1887969 prefixEnd_1887969 969435557788429046304895 := by
  unfold tailWord_1887969
  simp only [CollatzResearch.WordTrace]
  refine ⟨68859886497218227279594961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45906590998145484853063307 68859886497218227279594961)
  ·
    refine ⟨51644914872913670459696221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68859886497218227279594961 51644914872913670459696221)
    ·
      refine ⟨19366843077342626422386083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51644914872913670459696221 19366843077342626422386083)
      ·
        refine ⟨29050264616013939633579125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19366843077342626422386083 29050264616013939633579125)
        ·
          refine ⟨2723462307751306840648043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29050264616013939633579125 2723462307751306840648043)
          ·
            refine ⟨4085193461626960260972065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723462307751306840648043 4085193461626960260972065)
            ·
              refine ⟨3063895096220220195729049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4085193461626960260972065 3063895096220220195729049)
              ·
                refine ⟨2297921322165165146796787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3063895096220220195729049 2297921322165165146796787)
                ·
                  refine ⟨3446881983247747720195181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297921322165165146796787 3446881983247747720195181)
                  ·
                    refine ⟨1292580743717905395073193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3446881983247747720195181 1292580743717905395073193)
                    ·
                      refine ⟨969435557788429046304895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292580743717905395073193 969435557788429046304895)
                      ·
                        rfl

theorem cell23_1887969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_1887969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887969 prefixEnd_1887969 := by exact prefixLift 1887969
  have htrace : WordTrace (prefixWord ++ tailWord_1887969) baseStart_1887969 baseEnd_1887969 := by
    simpa [prefixWord, tailWord_1887969, baseEnd_1887969] using wordTrace_append hprefix tailTrace_1887969
  have hstable : (prefixWord ++ tailWord_1887969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887969).length < 2 ^ (prefixWord ++ tailWord_1887969).sum := by decide
  have hdescent : baseEnd_1887969 < baseStart_1887969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887978 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1887978 : Nat := 118140960795 + 1887978 * 2 ^ 59
def prefixEnd_1887978 : Nat := 4983230072969 + 3 ^ 40 * 1887978 * 2
def baseEnd_1887978 : Nat := 969440179114319511092353

theorem tailTrace_1887978 : CollatzResearch.WordTrace tailWord_1887978 prefixEnd_1887978 969440179114319511092353 := by
  unfold tailWord_1887978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17215053688546405454168147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45906809836123747877781725 17215053688546405454168147)
  ·
    refine ⟨25822580532819608181252221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17215053688546405454168147 25822580532819608181252221)
    ·
      refine ⟨9683467699807353067969583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25822580532819608181252221 9683467699807353067969583)
      ·
        refine ⟨14525201549711029601954375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9683467699807353067969583 14525201549711029601954375)
        ·
          refine ⟨21787802324566544402931563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14525201549711029601954375 21787802324566544402931563)
          ·
            refine ⟨32681703486849816604397345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21787802324566544402931563 32681703486849816604397345)
            ·
              refine ⟨24511277615137362453298009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32681703486849816604397345 24511277615137362453298009)
              ·
                refine ⟨18383458211353021839973507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24511277615137362453298009 18383458211353021839973507)
                ·
                  refine ⟨27575187317029532759960261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18383458211353021839973507 27575187317029532759960261)
                  ·
                    refine ⟨5170347621943037392492549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27575187317029532759960261 5170347621943037392492549)
                    ·
                      refine ⟨969440179114319511092353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5170347621943037392492549 969440179114319511092353)
                      ·
                        rfl

theorem cell23_1887978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1887978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887978 prefixEnd_1887978 := by exact prefixLift 1887978
  have htrace : WordTrace (prefixWord ++ tailWord_1887978) baseStart_1887978 baseEnd_1887978 := by
    simpa [prefixWord, tailWord_1887978, baseEnd_1887978] using wordTrace_append hprefix tailTrace_1887978
  have hstable : (prefixWord ++ tailWord_1887978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887978).length < 2 ^ (prefixWord ++ tailWord_1887978).sum := by decide
  have hdescent : baseEnd_1887978 < baseStart_1887978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887982 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_1887982 : Nat := 118140960795 + 1887982 * 2 ^ 59
def prefixEnd_1887982 : Nat := 4983230072969 + 3 ^ 40 * 1887982 * 2
def baseEnd_1887982 : Nat := 969442233036937495442335

theorem tailTrace_1887982 : CollatzResearch.WordTrace tailWord_1887982 prefixEnd_1887982 969442233036937495442335 := by
  unfold tailWord_1887982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8607545080771391312477275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45906907097447420333212133 8607545080771391312477275)
  ·
    refine ⟨12911317621157086968715913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8607545080771391312477275 12911317621157086968715913)
    ·
      refine ⟨9683488215867815226536935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12911317621157086968715913 9683488215867815226536935)
      ·
        refine ⟨14525232323801722839805403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9683488215867815226536935 14525232323801722839805403)
        ·
          refine ⟨21787848485702584259708105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14525232323801722839805403 21787848485702584259708105)
          ·
            refine ⟨16340886364276938194781079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21787848485702584259708105 16340886364276938194781079)
            ·
              refine ⟨24511329546415407292171619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16340886364276938194781079 24511329546415407292171619)
              ·
                refine ⟨36766994319623110938257429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24511329546415407292171619 36766994319623110938257429)
                ·
                  refine ⟨1723452858732333325230817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36766994319623110938257429 1723452858732333325230817)
                  ·
                    refine ⟨1292589644049249993923113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1723452858732333325230817 1292589644049249993923113)
                    ·
                      refine ⟨969442233036937495442335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292589644049249993923113 969442233036937495442335)
                      ·
                        rfl

theorem cell23_1887982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_1887982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1887982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1887982 prefixEnd_1887982 := by exact prefixLift 1887982
  have htrace : WordTrace (prefixWord ++ tailWord_1887982) baseStart_1887982 baseEnd_1887982 := by
    simpa [prefixWord, tailWord_1887982, baseEnd_1887982] using wordTrace_append hprefix tailTrace_1887982
  have hstable : (prefixWord ++ tailWord_1887982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887982).length < 2 ^ (prefixWord ++ tailWord_1887982).sum := by decide
  have hdescent : baseEnd_1887982 < baseStart_1887982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888020 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1888020 : Nat := 118140960795 + 1888020 * 2 ^ 59
def prefixEnd_1888020 : Nat := 4983230072969 + 3 ^ 40 * 1888020 * 2
def baseEnd_1888020 : Nat := 969461745301808346767161

theorem tailTrace_1888020 : CollatzResearch.WordTrace tailWord_1888020 prefixEnd_1888020 969461745301808346767161 := by
  unfold tailWord_1888020
  simp only [CollatzResearch.WordTrace]
  refine ⟨34430873310016731494850757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45907831080022308659801009 34430873310016731494850757)
  ·
    refine ⟨6455788745628137155284517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34430873310016731494850757 6455788745628137155284517)
    ·
      refine ⟨1210460389805275716615847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6455788745628137155284517 1210460389805275716615847)
      ·
        refine ⟨1815690584707913574923771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210460389805275716615847 1815690584707913574923771)
        ·
          refine ⟨2723535877061870362385657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1815690584707913574923771 2723535877061870362385657)
          ·
            refine ⟨2042651907796402771789243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2723535877061870362385657 2042651907796402771789243)
            ·
              refine ⟨3063977861694604157683865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2042651907796402771789243 3063977861694604157683865)
              ·
                refine ⟨2297983396270953118262899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3063977861694604157683865 2297983396270953118262899)
                ·
                  refine ⟨3446975094406429677394349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297983396270953118262899 3446975094406429677394349)
                  ·
                    refine ⟨1292615660402411129022881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3446975094406429677394349 1292615660402411129022881)
                    ·
                      refine ⟨969461745301808346767161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292615660402411129022881 969461745301808346767161)
                      ·
                        rfl

theorem cell23_1888020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1888020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888020 prefixEnd_1888020 := by exact prefixLift 1888020
  have htrace : WordTrace (prefixWord ++ tailWord_1888020) baseStart_1888020 baseEnd_1888020 := by
    simpa [prefixWord, tailWord_1888020, baseEnd_1888020] using wordTrace_append hprefix tailTrace_1888020
  have hstable : (prefixWord ++ tailWord_1888020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888020).length < 2 ^ (prefixWord ++ tailWord_1888020).sum := by decide
  have hdescent : baseEnd_1888020 < baseStart_1888020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888028 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1888028 : Nat := 118140960795 + 1888028 * 2 ^ 59
def prefixEnd_1888028 : Nat := 4983230072969 + 3 ^ 40 * 1888028 * 2
def baseEnd_1888028 : Nat := 969465853147044315467123

theorem tailTrace_1888028 : CollatzResearch.WordTrace tailWord_1888028 prefixEnd_1888028 969465853147044315467123 := by
  unfold tailWord_1888028
  simp only [CollatzResearch.WordTrace]
  refine ⟨34431019202002240177996369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45908025602669653570661825 34431019202002240177996369)
  ·
    refine ⟨25823264401501680133497277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34431019202002240177996369 25823264401501680133497277)
    ·
      refine ⟨9683724150563130050061479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25823264401501680133497277 9683724150563130050061479)
      ·
        refine ⟨14525586225844695075092219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9683724150563130050061479 14525586225844695075092219)
        ·
          refine ⟨21788379338767042612638329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14525586225844695075092219 21788379338767042612638329)
          ·
            refine ⟨16341284504075281959478747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21788379338767042612638329 16341284504075281959478747)
            ·
              refine ⟨24511926756112922939218121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16341284504075281959478747 24511926756112922939218121)
              ·
                refine ⟨18383945067084692204413591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24511926756112922939218121 18383945067084692204413591)
                ·
                  refine ⟨27575917600627038306620387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18383945067084692204413591 27575917600627038306620387)
                  ·
                    refine ⟨41363876400940557459930581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27575917600627038306620387 41363876400940557459930581)
                    ·
                      refine ⟨969465853147044315467123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41363876400940557459930581 969465853147044315467123)
                      ·
                        rfl

theorem cell23_1888028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1888028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888028 prefixEnd_1888028 := by exact prefixLift 1888028
  have htrace : WordTrace (prefixWord ++ tailWord_1888028) baseStart_1888028 baseEnd_1888028 := by
    simpa [prefixWord, tailWord_1888028, baseEnd_1888028] using wordTrace_append hprefix tailTrace_1888028
  have hstable : (prefixWord ++ tailWord_1888028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888028).length < 2 ^ (prefixWord ++ tailWord_1888028).sum := by decide
  have hdescent : baseEnd_1888028 < baseStart_1888028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888052 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_1888052 : Nat := 118140960795 + 1888052 * 2 ^ 59
def prefixEnd_1888052 : Nat := 4983230072969 + 3 ^ 40 * 1888052 * 2
def baseEnd_1888052 : Nat := 323159392227584073855671

theorem tailTrace_1888052 : CollatzResearch.WordTrace tailWord_1888052 prefixEnd_1888052 323159392227584073855671 := by
  unfold tailWord_1888052
  simp only [CollatzResearch.WordTrace]
  refine ⟨34431456877958766227433205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45908609170611688303244273 34431456877958766227433205)
  ·
    refine ⟨3227949082308634333821863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34431456877958766227433205 3227949082308634333821863)
    ·
      refine ⟨4841923623462951500732795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3227949082308634333821863 4841923623462951500732795)
      ·
        refine ⟨7262885435194427251099193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4841923623462951500732795 7262885435194427251099193)
        ·
          refine ⟨5447164076395820438324395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7262885435194427251099193 5447164076395820438324395)
          ·
            refine ⟨8170746114593730657486593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447164076395820438324395 8170746114593730657486593)
            ·
              refine ⟨6128059585945297993114945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8170746114593730657486593 6128059585945297993114945)
              ·
                refine ⟨4596044689458973494836209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6128059585945297993114945 4596044689458973494836209)
                ·
                  refine ⟨3447033517094230121127157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4596044689458973494836209 3447033517094230121127157)
                  ·
                    refine ⟨323159392227584073855671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3447033517094230121127157 323159392227584073855671)
                    ·
                      rfl

theorem cell23_1888052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_1888052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888052 prefixEnd_1888052 := by exact prefixLift 1888052
  have htrace : WordTrace (prefixWord ++ tailWord_1888052) baseStart_1888052 baseEnd_1888052 := by
    simpa [prefixWord, tailWord_1888052, baseEnd_1888052] using wordTrace_append hprefix tailTrace_1888052
  have hstable : (prefixWord ++ tailWord_1888052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888052).length < 2 ^ (prefixWord ++ tailWord_1888052).sum := by decide
  have hdescent : baseEnd_1888052 < baseStart_1888052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888072 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 2, 4, 2]
def baseStart_1888072 : Nat := 118140960795 + 1888072 * 2 ^ 59
def prefixEnd_1888072 : Nat := 4983230072969 + 3 ^ 40 * 1888072 * 2
def baseEnd_1888072 : Nat := 969488446295842143316921

theorem tailTrace_1888072 : CollatzResearch.WordTrace tailWord_1888072 prefixEnd_1888072 969488446295842143316921 := by
  unfold tailWord_1888072
  simp only [CollatzResearch.WordTrace]
  refine ⟨34431821607922537935297235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45909095477230050580396313 34431821607922537935297235)
  ·
    refine ⟨51647732411883806902945853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34431821607922537935297235 51647732411883806902945853)
    ·
      refine ⟨19367899654456427588604695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51647732411883806902945853 19367899654456427588604695)
      ·
        refine ⟨29051849481684641382907043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19367899654456427588604695 29051849481684641382907043)
        ·
          refine ⟨43577774222526962074360565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29051849481684641382907043 43577774222526962074360565)
          ·
            refine ⟨4085416333361902694471303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43577774222526962074360565 4085416333361902694471303)
            ·
              refine ⟨6128124500042854041706955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085416333361902694471303 6128124500042854041706955)
              ·
                refine ⟨9192186750064281062560433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128124500042854041706955 9192186750064281062560433)
                ·
                  refine ⟨6894140062548210796920325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9192186750064281062560433 6894140062548210796920325)
                  ·
                    refine ⟨1292651261727789524422561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6894140062548210796920325 1292651261727789524422561)
                    ·
                      refine ⟨969488446295842143316921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292651261727789524422561 969488446295842143316921)
                      ·
                        rfl

theorem cell23_1888072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_1888072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888072 prefixEnd_1888072 := by exact prefixLift 1888072
  have htrace : WordTrace (prefixWord ++ tailWord_1888072) baseStart_1888072 baseEnd_1888072 := by
    simpa [prefixWord, tailWord_1888072, baseEnd_1888072] using wordTrace_append hprefix tailTrace_1888072
  have hstable : (prefixWord ++ tailWord_1888072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888072).length < 2 ^ (prefixWord ++ tailWord_1888072).sum := by decide
  have hdescent : baseEnd_1888072 < baseStart_1888072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888078 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_1888078 : Nat := 118140960795 + 1888078 * 2 ^ 59
def prefixEnd_1888078 : Nat := 4983230072969 + 3 ^ 40 * 1888078 * 2
def baseEnd_1888078 : Nat := 107721280797752124426877

theorem tailTrace_1888078 : CollatzResearch.WordTrace tailWord_1888078 prefixEnd_1888078 107721280797752124426877 := by
  unfold tailWord_1888078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8607982756727917361914111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45909241369215559263541925 8607982756727917361914111)
  ·
    refine ⟨12911974135091876042871167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8607982756727917361914111 12911974135091876042871167)
    ·
      refine ⟨19367961202637814064306751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12911974135091876042871167 19367961202637814064306751)
      ·
        refine ⟨29051941803956721096460127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19367961202637814064306751 29051941803956721096460127)
        ·
          refine ⟨43577912705935081644690191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29051941803956721096460127 43577912705935081644690191)
          ·
            refine ⟨65366869058902622467035287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43577912705935081644690191 65366869058902622467035287)
            ·
              refine ⟨98050303588353933700552931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65366869058902622467035287 98050303588353933700552931)
              ·
                refine ⟨147075455382530900550829397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98050303588353933700552931 147075455382530900550829397)
                ·
                  refine ⟨107721280797752124426877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 147075455382530900550829397 107721280797752124426877)
                  ·
                    rfl

theorem cell23_1888078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_1888078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888078 prefixEnd_1888078 := by exact prefixLift 1888078
  have htrace : WordTrace (prefixWord ++ tailWord_1888078) baseStart_1888078 baseEnd_1888078 := by
    simpa [prefixWord, tailWord_1888078, baseEnd_1888078] using wordTrace_append hprefix tailTrace_1888078
  have hstable : (prefixWord ++ tailWord_1888078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888078).length < 2 ^ (prefixWord ++ tailWord_1888078).sum := by decide
  have hdescent : baseEnd_1888078 < baseStart_1888078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888082 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1888082 : Nat := 118140960795 + 1888082 * 2 ^ 59
def prefixEnd_1888082 : Nat := 4983230072969 + 3 ^ 40 * 1888082 * 2
def baseEnd_1888082 : Nat := 323164527034129034730625

theorem tailTrace_1888082 : CollatzResearch.WordTrace tailWord_1888082 prefixEnd_1888082 323164527034129034730625 := by
  unfold tailWord_1888082
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216001986452211894614625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45909338630539231718972333 17216001986452211894614625)
  ·
    refine ⟨12912001489839158920960969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17216001986452211894614625 12912001489839158920960969)
    ·
      refine ⟨9684001117379369190720727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12912001489839158920960969 9684001117379369190720727)
      ·
        refine ⟨14526001676069053786081091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9684001117379369190720727 14526001676069053786081091)
        ·
          refine ⟨21789002514103580679121637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14526001676069053786081091 21789002514103580679121637)
          ·
            refine ⟨4085437971394421377335307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21789002514103580679121637 4085437971394421377335307)
            ·
              refine ⟨6128156957091632066002961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085437971394421377335307 6128156957091632066002961)
              ·
                refine ⟨4596117717818724049502221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6128156957091632066002961 4596117717818724049502221)
                ·
                  refine ⟨1723544144182021518563333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4596117717818724049502221 1723544144182021518563333)
                  ·
                    refine ⟨323164527034129034730625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723544144182021518563333 323164527034129034730625)
                    ·
                      rfl

theorem cell23_1888082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1888082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888082 prefixEnd_1888082 := by exact prefixLift 1888082
  have htrace : WordTrace (prefixWord ++ tailWord_1888082) baseStart_1888082 baseEnd_1888082 := by
    simpa [prefixWord, tailWord_1888082, baseEnd_1888082] using wordTrace_append hprefix tailTrace_1888082
  have hstable : (prefixWord ++ tailWord_1888082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888082).length < 2 ^ (prefixWord ++ tailWord_1888082).sum := by decide
  have hdescent : baseEnd_1888082 < baseStart_1888082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888122 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3]
def baseStart_1888122 : Nat := 118140960795 + 1888122 * 2 ^ 59
def prefixEnd_1888122 : Nat := 4983230072969 + 3 ^ 40 * 1888122 * 2
def baseEnd_1888122 : Nat := 969514120328566947691691

theorem tailTrace_1888122 : CollatzResearch.WordTrace tailWord_1888122 prefixEnd_1888122 969514120328566947691691 := by
  unfold tailWord_1888122
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216366716415983602478655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45910311243775956273276413 17216366716415983602478655)
  ·
    refine ⟨25824550074623975403717983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17216366716415983602478655 25824550074623975403717983)
    ·
      refine ⟨38736825111935963105576975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25824550074623975403717983 38736825111935963105576975)
      ·
        refine ⟨58105237667903944658365463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38736825111935963105576975 58105237667903944658365463)
        ·
          refine ⟨87157856501855916987548195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58105237667903944658365463 87157856501855916987548195)
          ·
            refine ⟨130736784752783875481322293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87157856501855916987548195 130736784752783875481322293)
            ·
              refine ⟨12256573570573488326373965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130736784752783875481322293 12256573570573488326373965)
              ·
                refine ⟨4596215088965058122390237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12256573570573488326373965 4596215088965058122390237)
                ·
                  refine ⟨1723580658361896795896339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4596215088965058122390237 1723580658361896795896339)
                  ·
                    refine ⟨2585370987542845193844509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1723580658361896795896339 2585370987542845193844509)
                    ·
                      refine ⟨969514120328566947691691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2585370987542845193844509 969514120328566947691691)
                      ·
                        rfl

theorem cell23_1888122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_1888122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888122 prefixEnd_1888122 := by exact prefixLift 1888122
  have htrace : WordTrace (prefixWord ++ tailWord_1888122) baseStart_1888122 baseEnd_1888122 := by
    simpa [prefixWord, tailWord_1888122, baseEnd_1888122] using wordTrace_append hprefix tailTrace_1888122
  have hstable : (prefixWord ++ tailWord_1888122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888122).length < 2 ^ (prefixWord ++ tailWord_1888122).sum := by decide
  have hdescent : baseEnd_1888122 < baseStart_1888122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888132 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_1888132 : Nat := 118140960795 + 1888132 * 2 ^ 59
def prefixEnd_1888132 : Nat := 4983230072969 + 3 ^ 40 * 1888132 * 2
def baseEnd_1888132 : Nat := 969519255135111908566645

theorem tailTrace_1888132 : CollatzResearch.WordTrace tailWord_1888132 prefixEnd_1888132 969519255135111908566645 := by
  unfold tailWord_1888132
  simp only [CollatzResearch.WordTrace]
  refine ⟨34432915797813853058889325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45910554397085137411852433 34432915797813853058889325)
  ·
    refine ⟨12912343424180194897083497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34432915797813853058889325 12912343424180194897083497)
    ·
      refine ⟨9684257568135146172812623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12912343424180194897083497 9684257568135146172812623)
      ·
        refine ⟨14526386352202719259218935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9684257568135146172812623 14526386352202719259218935)
        ·
          refine ⟨21789579528304078888828403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14526386352202719259218935 21789579528304078888828403)
          ·
            refine ⟨32684369292456118333242605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21789579528304078888828403 32684369292456118333242605)
            ·
              refine ⟨12256638484671044374965977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32684369292456118333242605 12256638484671044374965977)
              ·
                refine ⟨9192478863503283281224483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12256638484671044374965977 9192478863503283281224483)
                ·
                  refine ⟨13788718295254924921836725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9192478863503283281224483 13788718295254924921836725)
                  ·
                    refine ⟨1292692340180149211422193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13788718295254924921836725 1292692340180149211422193)
                    ·
                      refine ⟨969519255135111908566645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292692340180149211422193 969519255135111908566645)
                      ·
                        rfl

theorem cell23_1888132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_1888132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888132 prefixEnd_1888132 := by exact prefixLift 1888132
  have htrace : WordTrace (prefixWord ++ tailWord_1888132) baseStart_1888132 baseEnd_1888132 := by
    simpa [prefixWord, tailWord_1888132, baseEnd_1888132] using wordTrace_append hprefix tailTrace_1888132
  have hstable : (prefixWord ++ tailWord_1888132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888132).length < 2 ^ (prefixWord ++ tailWord_1888132).sum := by decide
  have hdescent : baseEnd_1888132 < baseStart_1888132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888145 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_1888145 : Nat := 118140960795 + 1888145 * 2 ^ 59
def prefixEnd_1888145 : Nat := 4983230072969 + 3 ^ 40 * 1888145 * 2
def baseEnd_1888145 : Nat := 969525930383620357704085

theorem tailTrace_1888145 : CollatzResearch.WordTrace tailWord_1888145 prefixEnd_1888145 969525930383620357704085 := by
  unfold tailWord_1888145
  simp only [CollatzResearch.WordTrace]
  refine ⟨68866305744580609338001889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45910870496387072892001259 68866305744580609338001889)
  ·
    refine ⟨51649729308435457003501417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68866305744580609338001889 51649729308435457003501417)
    ·
      refine ⟨38737296981326592752626063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51649729308435457003501417 38737296981326592752626063)
      ·
        refine ⟨58105945471989889128939095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38737296981326592752626063 58105945471989889128939095)
        ·
          refine ⟨87158918207984833693408643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58105945471989889128939095 87158918207984833693408643)
          ·
            refine ⟨130738377311977250540112965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87158918207984833693408643 130738377311977250540112965)
            ·
              refine ⟨24513445745995734476271181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130738377311977250540112965 24513445745995734476271181)
              ·
                refine ⟨9192542154748400428601693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24513445745995734476271181 9192542154748400428601693)
                ·
                  refine ⟨3447203308030650160725635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9192542154748400428601693 3447203308030650160725635)
                  ·
                    refine ⟨5170804962045975241088453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3447203308030650160725635 5170804962045975241088453)
                    ·
                      refine ⟨969525930383620357704085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5170804962045975241088453 969525930383620357704085)
                      ·
                        rfl

theorem cell23_1888145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_1888145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888145 prefixEnd_1888145 := by exact prefixLift 1888145
  have htrace : WordTrace (prefixWord ++ tailWord_1888145) baseStart_1888145 baseEnd_1888145 := by
    simpa [prefixWord, tailWord_1888145, baseEnd_1888145] using wordTrace_append hprefix tailTrace_1888145
  have hstable : (prefixWord ++ tailWord_1888145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888145).length < 2 ^ (prefixWord ++ tailWord_1888145).sum := by decide
  have hdescent : baseEnd_1888145 < baseStart_1888145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888185 : List Nat := [1, 2, 1, 4, 2, 1, 4, 8]
def baseStart_1888185 : Nat := 118140960795 + 1888185 * 2 ^ 59
def prefixEnd_1888185 : Nat := 4983230072969 + 3 ^ 40 * 1888185 * 2
def baseEnd_1888185 : Nat := 35909128504066674118663

theorem tailTrace_1888185 : CollatzResearch.WordTrace tailWord_1888185 prefixEnd_1888185 35909128504066674118663 := by
  unfold tailWord_1888185
  simp only [CollatzResearch.WordTrace]
  refine ⟨68867764664435696169458009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45911843109623797446305339 68867764664435696169458009)
  ·
    refine ⟨51650823498326772127093507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68867764664435696169458009 51650823498326772127093507)
    ·
      refine ⟨77476235247490158190640261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51650823498326772127093507 77476235247490158190640261)
      ·
        refine ⟨14526794108904404660745049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77476235247490158190640261 14526794108904404660745049)
        ·
          refine ⟨10895095581678303495558787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14526794108904404660745049 10895095581678303495558787)
          ·
            refine ⟨16342643372517455243338181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10895095581678303495558787 16342643372517455243338181)
            ·
              refine ⟨3064245632347022858125909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16342643372517455243338181 3064245632347022858125909)
              ·
                refine ⟨35909128504066674118663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3064245632347022858125909 35909128504066674118663)
                ·
                  rfl

theorem cell23_1888185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 8].length) (baseStart_1888185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888185 prefixEnd_1888185 := by exact prefixLift 1888185
  have htrace : WordTrace (prefixWord ++ tailWord_1888185) baseStart_1888185 baseEnd_1888185 := by
    simpa [prefixWord, tailWord_1888185, baseEnd_1888185] using wordTrace_append hprefix tailTrace_1888185
  have hstable : (prefixWord ++ tailWord_1888185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888185).length < 2 ^ (prefixWord ++ tailWord_1888185).sum := by decide
  have hdescent : baseEnd_1888185 < baseStart_1888185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888189 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_1888189 : Nat := 118140960795 + 1888189 * 2 ^ 59
def prefixEnd_1888189 : Nat := 4983230072969 + 3 ^ 40 * 1888189 * 2
def baseEnd_1888189 : Nat := 323182841177472728517961

theorem tailTrace_1888189 : CollatzResearch.WordTrace tailWord_1888189 prefixEnd_1888189 323182841177472728517961 := by
  unfold tailWord_1888189
  simp only [CollatzResearch.WordTrace]
  refine ⟨68867910556421204852603621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45911940370947469901735747 68867910556421204852603621)
  ·
    refine ⟨12912733229328975909863179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68867910556421204852603621 12912733229328975909863179)
    ·
      refine ⟨19369099843993463864794769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12912733229328975909863179 19369099843993463864794769)
      ·
        refine ⟨14526824882995097898596077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19369099843993463864794769 14526824882995097898596077)
        ·
          refine ⟨5447559331123161711973529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14526824882995097898596077 5447559331123161711973529)
          ·
            refine ⟨4085669498342371283980147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5447559331123161711973529 4085669498342371283980147)
            ·
              refine ⟨6128504247513556925970221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085669498342371283980147 6128504247513556925970221)
              ·
                refine ⟨2298189092817583847238833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6128504247513556925970221 2298189092817583847238833)
                ·
                  refine ⟨1723641819613187885429125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2298189092817583847238833 1723641819613187885429125)
                  ·
                    refine ⟨323182841177472728517961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723641819613187885429125 323182841177472728517961)
                    ·
                      rfl

theorem cell23_1888189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_1888189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888189 prefixEnd_1888189 := by exact prefixLift 1888189
  have htrace : WordTrace (prefixWord ++ tailWord_1888189) baseStart_1888189 baseEnd_1888189 := by
    simpa [prefixWord, tailWord_1888189, baseEnd_1888189] using wordTrace_append hprefix tailTrace_1888189
  have hstable : (prefixWord ++ tailWord_1888189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888189).length < 2 ^ (prefixWord ++ tailWord_1888189).sum := by decide
  have hdescent : baseEnd_1888189 < baseStart_1888189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888225 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_1888225 : Nat := 118140960795 + 1888225 * 2 ^ 59
def prefixEnd_1888225 : Nat := 4983230072969 + 3 ^ 40 * 1888225 * 2
def baseEnd_1888225 : Nat := 969567008835980044703717

theorem tailTrace_1888225 : CollatzResearch.WordTrace tailWord_1888225 prefixEnd_1888225 969567008835980044703717 := by
  unfold tailWord_1888225
  simp only [CollatzResearch.WordTrace]
  refine ⟨68869223584290783000914129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45912815722860522000609419 68869223584290783000914129)
  ·
    refine ⟨51651917688218087250685597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68869223584290783000914129 51651917688218087250685597)
    ·
      refine ⟨19369469133081782719007099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51651917688218087250685597 19369469133081782719007099)
      ·
        refine ⟨29054203699622674078510649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19369469133081782719007099 29054203699622674078510649)
        ·
          refine ⟨21790652774717005558882987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29054203699622674078510649 21790652774717005558882987)
          ·
            refine ⟨32685979162075508338324481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21790652774717005558882987 32685979162075508338324481)
            ·
              refine ⟨24514484371556631253743361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32685979162075508338324481 24514484371556631253743361)
              ·
                refine ⟨18385863278667473440307521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24514484371556631253743361 18385863278667473440307521)
                ·
                  refine ⟨13789397459000605080230641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18385863278667473440307521 13789397459000605080230641)
                  ·
                    refine ⟨10342048094250453810172981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13789397459000605080230641 10342048094250453810172981)
                    ·
                      refine ⟨969567008835980044703717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10342048094250453810172981 969567008835980044703717)
                      ·
                        rfl

theorem cell23_1888225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_1888225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888225 prefixEnd_1888225 := by exact prefixLift 1888225
  have htrace : WordTrace (prefixWord ++ tailWord_1888225) baseStart_1888225 baseEnd_1888225 := by
    simpa [prefixWord, tailWord_1888225, baseEnd_1888225] using wordTrace_append hprefix tailTrace_1888225
  have hstable : (prefixWord ++ tailWord_1888225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888225).length < 2 ^ (prefixWord ++ tailWord_1888225).sum := by decide
  have hdescent : baseEnd_1888225 < baseStart_1888225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888246 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_1888246 : Nat := 118140960795 + 1888246 * 2 ^ 59
def prefixEnd_1888246 : Nat := 4983230072969 + 3 ^ 40 * 1888246 * 2
def baseEnd_1888246 : Nat := 969577791929724462541121

theorem tailTrace_1888246 : CollatzResearch.WordTrace tailWord_1888246 prefixEnd_1888246 969577791929724462541121 := by
  unfold tailWord_1888246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4304374344825918974214287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45913326344809802391619061 4304374344825918974214287)
  ·
    refine ⟨6456561517238878461321431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4304374344825918974214287 6456561517238878461321431)
    ·
      refine ⟨9684842275858317691982147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6456561517238878461321431 9684842275858317691982147)
      ·
        refine ⟨14527263413787476537973221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9684842275858317691982147 14527263413787476537973221)
        ·
          refine ⟨2723861890085151850869979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14527263413787476537973221 2723861890085151850869979)
          ·
            refine ⟨4085792835127727776304969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723861890085151850869979 4085792835127727776304969)
            ·
              refine ⟨3064344626345795832228727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4085792835127727776304969 3064344626345795832228727)
              ·
                refine ⟨4596516939518693748343091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064344626345795832228727 4596516939518693748343091)
                ·
                  refine ⟨6894775409278040622514637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596516939518693748343091 6894775409278040622514637)
                  ·
                    refine ⟨2585540778479265233442989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6894775409278040622514637 2585540778479265233442989)
                    ·
                      refine ⟨969577791929724462541121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2585540778479265233442989 969577791929724462541121)
                      ·
                        rfl

theorem cell23_1888246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_1888246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888246 prefixEnd_1888246 := by exact prefixLift 1888246
  have htrace : WordTrace (prefixWord ++ tailWord_1888246) baseStart_1888246 baseEnd_1888246 := by
    simpa [prefixWord, tailWord_1888246, baseEnd_1888246] using wordTrace_append hprefix tailTrace_1888246
  have hstable : (prefixWord ++ tailWord_1888246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888246).length < 2 ^ (prefixWord ++ tailWord_1888246).sum := by decide
  have hdescent : baseEnd_1888246 < baseStart_1888246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888255 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 5]
def baseStart_1888255 : Nat := 118140960795 + 1888255 * 2 ^ 59
def prefixEnd_1888255 : Nat := 4983230072969 + 3 ^ 40 * 1888255 * 2
def baseEnd_1888255 : Nat := 969582413255614927328579

theorem tailTrace_1888255 : CollatzResearch.WordTrace tailWord_1888255 prefixEnd_1888255 969582413255614927328579 := by
  unfold tailWord_1888255
  simp only [CollatzResearch.WordTrace]
  refine ⟨68870317774182098124506219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45913545182788065416337479 68870317774182098124506219)
  ·
    refine ⟨103305476661273147186759329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68870317774182098124506219 103305476661273147186759329)
    ·
      refine ⟨77479107495954860390069497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103305476661273147186759329 77479107495954860390069497)
      ·
        refine ⟨58109330621966145292552123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77479107495954860390069497 58109330621966145292552123)
        ·
          refine ⟨87163995932949217938828185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58109330621966145292552123 87163995932949217938828185)
          ·
            refine ⟨65372996949711913454121139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87163995932949217938828185 65372996949711913454121139)
            ·
              refine ⟨98059495424567870181181709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65372996949711913454121139 98059495424567870181181709)
              ·
                refine ⟨36772310784212951317943141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98059495424567870181181709 36772310784212951317943141)
                ·
                  refine ⟨6894808272039928372114339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36772310784212951317943141 6894808272039928372114339)
                  ·
                    refine ⟨10342212408059892558171509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6894808272039928372114339 10342212408059892558171509)
                    ·
                      refine ⟨969582413255614927328579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10342212408059892558171509 969582413255614927328579)
                      ·
                        rfl

theorem cell23_1888255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_1888255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888255 prefixEnd_1888255 := by exact prefixLift 1888255
  have htrace : WordTrace (prefixWord ++ tailWord_1888255) baseStart_1888255 baseEnd_1888255 := by
    simpa [prefixWord, tailWord_1888255, baseEnd_1888255] using wordTrace_append hprefix tailTrace_1888255
  have hstable : (prefixWord ++ tailWord_1888255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888255).length < 2 ^ (prefixWord ++ tailWord_1888255).sum := by decide
  have hdescent : baseEnd_1888255 < baseStart_1888255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888282 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1888282 : Nat := 118140960795 + 1888282 * 2 ^ 59
def prefixEnd_1888282 : Nat := 4983230072969 + 3 ^ 40 * 1888282 * 2
def baseEnd_1888282 : Nat := 969596277233286321690955

theorem tailTrace_1888282 : CollatzResearch.WordTrace tailWord_1888282 prefixEnd_1888282 969596277233286321690955 := by
  unfold tailWord_1888282
  simp only [CollatzResearch.WordTrace]
  refine ⟨17217825636271070433934775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45914201696722854490492733 17217825636271070433934775)
  ·
    refine ⟨25826738454406605650902163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17217825636271070433934775 25826738454406605650902163)
    ·
      refine ⟨38740107681609908476353245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25826738454406605650902163 38740107681609908476353245)
      ·
        refine ⟨14527540380603715678632467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38740107681609908476353245 14527540380603715678632467)
        ·
          refine ⟨21791310570905573517948701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14527540380603715678632467 21791310570905573517948701)
          ·
            refine ⟨8171741464089590069230763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21791310570905573517948701 8171741464089590069230763)
            ·
              refine ⟨12257612196134385103846145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8171741464089590069230763 12257612196134385103846145)
              ·
                refine ⟨9193209147100788827884609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12257612196134385103846145 9193209147100788827884609)
                ·
                  refine ⟨6894906860325591620913457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9193209147100788827884609 6894906860325591620913457)
                  ·
                    refine ⟨5171180145244193715685093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6894906860325591620913457 5171180145244193715685093)
                    ·
                      refine ⟨969596277233286321690955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5171180145244193715685093 969596277233286321690955)
                      ·
                        rfl

theorem cell23_1888282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1888282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888282 prefixEnd_1888282 := by exact prefixLift 1888282
  have htrace : WordTrace (prefixWord ++ tailWord_1888282) baseStart_1888282 baseEnd_1888282 := by
    simpa [prefixWord, tailWord_1888282, baseEnd_1888282] using wordTrace_append hprefix tailTrace_1888282
  have hstable : (prefixWord ++ tailWord_1888282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888282).length < 2 ^ (prefixWord ++ tailWord_1888282).sum := by decide
  have hdescent : baseEnd_1888282 < baseStart_1888282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888315 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 7]
def baseStart_1888315 : Nat := 118140960795 + 1888315 * 2 ^ 59
def prefixEnd_1888315 : Nat := 4983230072969 + 3 ^ 40 * 1888315 * 2
def baseEnd_1888315 : Nat := 969613222094884692578303

theorem tailTrace_1888315 : CollatzResearch.WordTrace tailWord_1888315 prefixEnd_1888315 969613222094884692578303 := by
  unfold tailWord_1888315
  simp only [CollatzResearch.WordTrace]
  refine ⟨68872506153964728371690399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45915004102643152247793599 68872506153964728371690399)
  ·
    refine ⟨103308759230947092557535599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68872506153964728371690399 103308759230947092557535599)
    ·
      refine ⟨154963138846420638836303399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103308759230947092557535599 154963138846420638836303399)
      ·
        refine ⟨232444708269630958254455099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154963138846420638836303399 232444708269630958254455099)
        ·
          refine ⟨348667062404446437381682649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232444708269630958254455099 348667062404446437381682649)
          ·
            refine ⟨261500296803334828036261987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348667062404446437381682649 261500296803334828036261987)
            ·
              refine ⟨392250445205002242054392981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261500296803334828036261987 392250445205002242054392981)
              ·
                refine ⟨18386739618984480096299671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 392250445205002242054392981 18386739618984480096299671)
                ·
                  refine ⟨27580109428476720144449507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18386739618984480096299671 27580109428476720144449507)
                  ·
                    refine ⟨41370164142715080216674261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27580109428476720144449507 41370164142715080216674261)
                    ·
                      refine ⟨969613222094884692578303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41370164142715080216674261 969613222094884692578303)
                      ·
                        rfl

theorem cell23_1888315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_1888315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888315 prefixEnd_1888315 := by exact prefixLift 1888315
  have htrace : WordTrace (prefixWord ++ tailWord_1888315) baseStart_1888315 baseEnd_1888315 := by
    simpa [prefixWord, tailWord_1888315, baseEnd_1888315] using wordTrace_append hprefix tailTrace_1888315
  have hstable : (prefixWord ++ tailWord_1888315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888315).length < 2 ^ (prefixWord ++ tailWord_1888315).sum := by decide
  have hdescent : baseEnd_1888315 < baseStart_1888315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888335 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 1, 10]
def baseStart_1888335 : Nat := 118140960795 + 1888335 * 2 ^ 59
def prefixEnd_1888335 : Nat := 4983230072969 + 3 ^ 40 * 1888335 * 2
def baseEnd_1888335 : Nat := 323207830569324871442737

theorem tailTrace_1888335 : CollatzResearch.WordTrace tailWord_1888335 prefixEnd_1888335 323207830569324871442737 := by
  unfold tailWord_1888335
  simp only [CollatzResearch.WordTrace]
  refine ⟨68873235613892271787418459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45915490409261514524945639 68873235613892271787418459)
  ·
    refine ⟨103309853420838407681127689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68873235613892271787418459 103309853420838407681127689)
    ·
      refine ⟨77482390065628805760845767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103309853420838407681127689 77482390065628805760845767)
      ·
        refine ⟨116223585098443208641268651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77482390065628805760845767 116223585098443208641268651)
        ·
          refine ⟨174335377647664812961902977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116223585098443208641268651 174335377647664812961902977)
          ·
            refine ⟨130751533235748609721427233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174335377647664812961902977 130751533235748609721427233)
            ·
              refine ⟨98063649926811457291070425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130751533235748609721427233 98063649926811457291070425)
              ·
                refine ⟨73547737445108592968302819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98063649926811457291070425 73547737445108592968302819)
                ·
                  refine ⟨110321606167662889452454229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73547737445108592968302819 110321606167662889452454229)
                  ·
                    refine ⟨323207830569324871442737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 110321606167662889452454229 323207830569324871442737)
                    ·
                      rfl

theorem cell23_1888335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_1888335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888335 prefixEnd_1888335 := by exact prefixLift 1888335
  have htrace : WordTrace (prefixWord ++ tailWord_1888335) baseStart_1888335 baseEnd_1888335 := by
    simpa [prefixWord, tailWord_1888335, baseEnd_1888335] using wordTrace_append hprefix tailTrace_1888335
  have hstable : (prefixWord ++ tailWord_1888335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888335).length < 2 ^ (prefixWord ++ tailWord_1888335).sum := by decide
  have hdescent : baseEnd_1888335 < baseStart_1888335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888349 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1888349 : Nat := 118140960795 + 1888349 * 2 ^ 59
def prefixEnd_1888349 : Nat := 4983230072969 + 3 ^ 40 * 1888349 * 2
def baseEnd_1888349 : Nat := 969630680437137559553147

theorem tailTrace_1888349 : CollatzResearch.WordTrace tailWord_1888349 prefixEnd_1888349 969630680437137559553147 := by
  unfold tailWord_1888349
  simp only [CollatzResearch.WordTrace]
  refine ⟨68873746235841552178428101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45915830823894368118952067 68873746235841552178428101)
  ·
    refine ⟨12913827419220291033455269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68873746235841552178428101 12913827419220291033455269)
    ·
      refine ⟨2421342641103804568772863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12913827419220291033455269 2421342641103804568772863)
      ·
        refine ⟨3632013961655706853159295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421342641103804568772863 3632013961655706853159295)
        ·
          refine ⟨5448020942483560279738943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632013961655706853159295 5448020942483560279738943)
          ·
            refine ⟨8172031413725340419608415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5448020942483560279738943 8172031413725340419608415)
            ·
              refine ⟨12258047120588010629412623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8172031413725340419608415 12258047120588010629412623)
              ·
                refine ⟨18387070680882015944118935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12258047120588010629412623 18387070680882015944118935)
                ·
                  refine ⟨27580606021323023916178403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18387070680882015944118935 27580606021323023916178403)
                  ·
                    refine ⟨41370909031984535874267605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27580606021323023916178403 41370909031984535874267605)
                    ·
                      refine ⟨969630680437137559553147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41370909031984535874267605 969630680437137559553147)
                      ·
                        rfl

theorem cell23_1888349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1888349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888349 prefixEnd_1888349 := by exact prefixLift 1888349
  have htrace : WordTrace (prefixWord ++ tailWord_1888349) baseStart_1888349 baseEnd_1888349 := by
    simpa [prefixWord, tailWord_1888349, baseEnd_1888349] using wordTrace_append hprefix tailTrace_1888349
  have hstable : (prefixWord ++ tailWord_1888349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888349).length < 2 ^ (prefixWord ++ tailWord_1888349).sum := by decide
  have hdescent : baseEnd_1888349 < baseStart_1888349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888354 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_1888354 : Nat := 118140960795 + 1888354 * 2 ^ 59
def prefixEnd_1888354 : Nat := 4983230072969 + 3 ^ 40 * 1888354 * 2
def baseEnd_1888354 : Nat := 969633247840410039990625

theorem tailTrace_1888354 : CollatzResearch.WordTrace tailWord_1888354 prefixEnd_1888354 969633247840410039990625 := by
  unfold tailWord_1888354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17218482150205859508090029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45915952400548958688240077 17218482150205859508090029)
  ·
    refine ⟨6456930806327197315533761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17218482150205859508090029 6456930806327197315533761)
    ·
      refine ⟨4842698104745397986650321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6456930806327197315533761 4842698104745397986650321)
      ·
        refine ⟨3632023578559048489987741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4842698104745397986650321 3632023578559048489987741)
        ·
          refine ⟨1362008841959643183745403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3632023578559048489987741 1362008841959643183745403)
          ·
            refine ⟨2043013262939464775618105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362008841959643183745403 2043013262939464775618105)
            ·
              refine ⟨1532259947204598581713579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043013262939464775618105 1532259947204598581713579)
              ·
                refine ⟨2298389920806897872570369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532259947204598581713579 2298389920806897872570369)
                ·
                  refine ⟨1723792440605173404427777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2298389920806897872570369 1723792440605173404427777)
                  ·
                    refine ⟨1292844330453880053320833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1723792440605173404427777 1292844330453880053320833)
                    ·
                      refine ⟨969633247840410039990625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292844330453880053320833 969633247840410039990625)
                      ·
                        rfl

theorem cell23_1888354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_1888354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888354 prefixEnd_1888354 := by exact prefixLift 1888354
  have htrace : WordTrace (prefixWord ++ tailWord_1888354) baseStart_1888354 baseEnd_1888354 := by
    simpa [prefixWord, tailWord_1888354, baseEnd_1888354] using wordTrace_append hprefix tailTrace_1888354
  have hstable : (prefixWord ++ tailWord_1888354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888354).length < 2 ^ (prefixWord ++ tailWord_1888354).sum := by decide
  have hdescent : baseEnd_1888354 < baseStart_1888354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888359 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_1888359 : Nat := 118140960795 + 1888359 * 2 ^ 59
def prefixEnd_1888359 : Nat := 4983230072969 + 3 ^ 40 * 1888359 * 2
def baseEnd_1888359 : Nat := 969635815243682520428101

theorem tailTrace_1888359 : CollatzResearch.WordTrace tailWord_1888359 prefixEnd_1888359 969635815243682520428101 := by
  unfold tailWord_1888359
  simp only [CollatzResearch.WordTrace]
  refine ⟨68874110965805323886292131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45916073977203549257528087 68874110965805323886292131)
  ·
    refine ⟨103311166448707985829438197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68874110965805323886292131 103311166448707985829438197)
    ·
      refine ⟨9685421854566373671509831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103311166448707985829438197 9685421854566373671509831)
      ·
        refine ⟨14528132781849560507264747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9685421854566373671509831 14528132781849560507264747)
        ·
          refine ⟨21792199172774340760897121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14528132781849560507264747 21792199172774340760897121)
          ·
            refine ⟨16344149379580755570672841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21792199172774340760897121 16344149379580755570672841)
            ·
              refine ⟨12258112034685566678004631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16344149379580755570672841 12258112034685566678004631)
              ·
                refine ⟨18387168052028350017006947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12258112034685566678004631 18387168052028350017006947)
                ·
                  refine ⟨27580752078042525025510421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18387168052028350017006947 27580752078042525025510421)
                  ·
                    refine ⟨1292847753658243360570801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27580752078042525025510421 1292847753658243360570801)
                    ·
                      refine ⟨969635815243682520428101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292847753658243360570801 969635815243682520428101)
                      ·
                        rfl

theorem cell23_1888359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_1888359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888359 prefixEnd_1888359 := by exact prefixLift 1888359
  have htrace : WordTrace (prefixWord ++ tailWord_1888359) baseStart_1888359 baseEnd_1888359 := by
    simpa [prefixWord, tailWord_1888359, baseEnd_1888359] using wordTrace_append hprefix tailTrace_1888359
  have hstable : (prefixWord ++ tailWord_1888359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888359).length < 2 ^ (prefixWord ++ tailWord_1888359).sum := by decide
  have hdescent : baseEnd_1888359 < baseStart_1888359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888409 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 7, 1, 3]
def baseStart_1888409 : Nat := 118140960795 + 1888409 * 2 ^ 59
def prefixEnd_1888409 : Nat := 4983230072969 + 3 ^ 40 * 1888409 * 2
def baseEnd_1888409 : Nat := 969661489276407324802871

theorem tailTrace_1888409 : CollatzResearch.WordTrace tailWord_1888409 prefixEnd_1888409 969661489276407324802871 := by
  unfold tailWord_1888409
  simp only [CollatzResearch.WordTrace]
  refine ⟨68875934615624182425612281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45917289743749454950408187 68875934615624182425612281)
  ·
    refine ⟨51656950961718136819209211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68875934615624182425612281 51656950961718136819209211)
    ·
      refine ⟨77485426442577205228813817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51656950961718136819209211 77485426442577205228813817)
      ·
        refine ⟨58114069831932903921610363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77485426442577205228813817 58114069831932903921610363)
        ·
          refine ⟨87171104747899355882415545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58114069831932903921610363 87171104747899355882415545)
          ·
            refine ⟨65378328560924516911811659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87171104747899355882415545 65378328560924516911811659)
            ·
              refine ⟨98067492841386775367717489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65378328560924516911811659 98067492841386775367717489)
              ·
                refine ⟨73550619631040081525788117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98067492841386775367717489 73550619631040081525788117)
                ·
                  refine ⟨1723842647602501910760659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 73550619631040081525788117 1723842647602501910760659)
                  ·
                    refine ⟨2585763971403752866140989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1723842647602501910760659 2585763971403752866140989)
                    ·
                      refine ⟨969661489276407324802871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2585763971403752866140989 969661489276407324802871)
                      ·
                        rfl

theorem cell23_1888409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_1888409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888409 prefixEnd_1888409 := by exact prefixLift 1888409
  have htrace : WordTrace (prefixWord ++ tailWord_1888409) baseStart_1888409 baseEnd_1888409 := by
    simpa [prefixWord, tailWord_1888409, baseEnd_1888409] using wordTrace_append hprefix tailTrace_1888409
  have hstable : (prefixWord ++ tailWord_1888409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888409).length < 2 ^ (prefixWord ++ tailWord_1888409).sum := by decide
  have hdescent : baseEnd_1888409 < baseStart_1888409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888443 : List Nat := [1, 1, 1, 1, 1, 2, 8, 3, 1, 1, 3]
def baseStart_1888443 : Nat := 118140960795 + 1888443 * 2 ^ 59
def prefixEnd_1888443 : Nat := 4983230072969 + 3 ^ 40 * 1888443 * 2
def baseEnd_1888443 : Nat := 969678947618660191777715

theorem tailTrace_1888443 : CollatzResearch.WordTrace tailWord_1888443 prefixEnd_1888443 969678947618660191777715 := by
  unfold tailWord_1888443
  simp only [CollatzResearch.WordTrace]
  refine ⟨68877174697501006232349983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45918116465000670821566655 68877174697501006232349983)
  ·
    refine ⟨103315762046251509348524975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68877174697501006232349983 103315762046251509348524975)
    ·
      refine ⟨154973643069377264022787463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103315762046251509348524975 154973643069377264022787463)
      ·
        refine ⟨232460464604065896034181195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154973643069377264022787463 232460464604065896034181195)
        ·
          refine ⟨348690696906098844051271793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232460464604065896034181195 348690696906098844051271793)
          ·
            refine ⟨261518022679574133038453845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348690696906098844051271793 261518022679574133038453845)
            ·
              refine ⟨3064664328276259371544381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 261518022679574133038453845 3064664328276259371544381)
              ·
                refine ⟨1149249123103597264329143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3064664328276259371544381 1149249123103597264329143)
                ·
                  refine ⟨1723873684655395896493715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149249123103597264329143 1723873684655395896493715)
                  ·
                    refine ⟨2585810526983093844740573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1723873684655395896493715 2585810526983093844740573)
                    ·
                      refine ⟨969678947618660191777715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2585810526983093844740573 969678947618660191777715)
                      ·
                        rfl

theorem cell23_1888443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 1, 1, 3].length) (baseStart_1888443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888443 prefixEnd_1888443 := by exact prefixLift 1888443
  have htrace : WordTrace (prefixWord ++ tailWord_1888443) baseStart_1888443 baseEnd_1888443 := by
    simpa [prefixWord, tailWord_1888443, baseEnd_1888443] using wordTrace_append hprefix tailTrace_1888443
  have hstable : (prefixWord ++ tailWord_1888443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888443).length < 2 ^ (prefixWord ++ tailWord_1888443).sum := by decide
  have hdescent : baseEnd_1888443 < baseStart_1888443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888450 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1888450 : Nat := 118140960795 + 1888450 * 2 ^ 59
def prefixEnd_1888450 : Nat := 4983230072969 + 3 ^ 40 * 1888450 * 2
def baseEnd_1888450 : Nat := 107742504664804629376687

theorem tailTrace_1888450 : CollatzResearch.WordTrace tailWord_1888450 prefixEnd_1888450 107742504664804629376687 := by
  unfold tailWord_1888450
  simp only [CollatzResearch.WordTrace]
  refine ⟨17219357502118911606963701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45918286672317097618569869 17219357502118911606963701)
  ·
    refine ⟨1614314765823647963152847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17219357502118911606963701 1614314765823647963152847)
    ·
      refine ⟨2421472148735471944729271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614314765823647963152847 2421472148735471944729271)
      ·
        refine ⟨3632208223103207917093907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421472148735471944729271 3632208223103207917093907)
        ·
          refine ⟨5448312334654811875640861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632208223103207917093907 5448312334654811875640861)
          ·
            refine ⟨2043117125495554453365323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5448312334654811875640861 2043117125495554453365323)
            ·
              refine ⟨3064675688243331680047985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043117125495554453365323 3064675688243331680047985)
              ·
                refine ⟨2298506766182498760035989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064675688243331680047985 2298506766182498760035989)
                ·
                  refine ⟨107742504664804629376687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2298506766182498760035989 107742504664804629376687)
                  ·
                    rfl

theorem cell23_1888450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1888450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888450 prefixEnd_1888450 := by exact prefixLift 1888450
  have htrace : WordTrace (prefixWord ++ tailWord_1888450) baseStart_1888450 baseEnd_1888450 := by
    simpa [prefixWord, tailWord_1888450, baseEnd_1888450] using wordTrace_append hprefix tailTrace_1888450
  have hstable : (prefixWord ++ tailWord_1888450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888450).length < 2 ^ (prefixWord ++ tailWord_1888450).sum := by decide
  have hdescent : baseEnd_1888450 < baseStart_1888450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888459 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 4, 4]
def baseStart_1888459 : Nat := 118140960795 + 1888459 * 2 ^ 59
def prefixEnd_1888459 : Nat := 4983230072969 + 3 ^ 40 * 1888459 * 2
def baseEnd_1888459 : Nat := 323229054436377376392547

theorem tailTrace_1888459 : CollatzResearch.WordTrace tailWord_1888459 prefixEnd_1888459 323229054436377376392547 := by
  unfold tailWord_1888459
  simp only [CollatzResearch.WordTrace]
  refine ⟨68877758265443040964932431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45918505510295360643288287 68877758265443040964932431)
  ·
    refine ⟨103316637398164561447398647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68877758265443040964932431 103316637398164561447398647)
    ·
      refine ⟨154974956097246842171097971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103316637398164561447398647 154974956097246842171097971)
      ·
        refine ⟨232462434145870263256646957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154974956097246842171097971 232462434145870263256646957)
        ·
          refine ⟨87173412804701348721242609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232462434145870263256646957 87173412804701348721242609)
          ·
            refine ⟨65380059603526011540931957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87173412804701348721242609 65380059603526011540931957)
            ·
              refine ⟨6129380587830563581962371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65380059603526011540931957 6129380587830563581962371)
              ·
                refine ⟨9194070881745845372943557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129380587830563581962371 9194070881745845372943557)
                ·
                  refine ⟨1723888290327346007426917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9194070881745845372943557 1723888290327346007426917)
                  ·
                    refine ⟨323229054436377376392547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723888290327346007426917 323229054436377376392547)
                    ·
                      rfl

theorem cell23_1888459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 4].length) (baseStart_1888459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888459 prefixEnd_1888459 := by exact prefixLift 1888459
  have htrace : WordTrace (prefixWord ++ tailWord_1888459) baseStart_1888459 baseEnd_1888459 := by
    simpa [prefixWord, tailWord_1888459, baseEnd_1888459] using wordTrace_append hprefix tailTrace_1888459
  have hstable : (prefixWord ++ tailWord_1888459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888459).length < 2 ^ (prefixWord ++ tailWord_1888459).sum := by decide
  have hdescent : baseEnd_1888459 < baseStart_1888459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888460 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1888460 : Nat := 118140960795 + 1888460 * 2 ^ 59
def prefixEnd_1888460 : Nat := 4983230072969 + 3 ^ 40 * 1888460 * 2
def baseEnd_1888460 : Nat := 969687676789786625265137

theorem tailTrace_1888460 : CollatzResearch.WordTrace tailWord_1888460 prefixEnd_1888460 969687676789786625265137 := by
  unfold tailWord_1888460
  simp only [CollatzResearch.WordTrace]
  refine ⟨34438897369219709067859417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45918529825626278757145889 34438897369219709067859417)
  ·
    refine ⟨25829173026914781800894563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34438897369219709067859417 25829173026914781800894563)
    ·
      refine ⟨38743759540372172701341845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25829173026914781800894563 38743759540372172701341845)
      ·
        refine ⟨1816113728454945595375399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38743759540372172701341845 1816113728454945595375399)
        ·
          refine ⟨2724170592682418393063099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816113728454945595375399 2724170592682418393063099)
          ·
            refine ⟨4086255889023627589594649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724170592682418393063099 4086255889023627589594649)
            ·
              refine ⟨3064691916767720692195987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4086255889023627589594649 3064691916767720692195987)
              ·
                refine ⟨4597037875151581038293981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064691916767720692195987 4597037875151581038293981)
                ·
                  refine ⟨1723889203181842889360243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4597037875151581038293981 1723889203181842889360243)
                  ·
                    refine ⟨2585833804772764334040365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1723889203181842889360243 2585833804772764334040365)
                    ·
                      refine ⟨969687676789786625265137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2585833804772764334040365 969687676789786625265137)
                      ·
                        rfl

theorem cell23_1888460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1888460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888460 prefixEnd_1888460 := by exact prefixLift 1888460
  have htrace : WordTrace (prefixWord ++ tailWord_1888460) baseStart_1888460 baseEnd_1888460 := by
    simpa [prefixWord, tailWord_1888460, baseEnd_1888460] using wordTrace_append hprefix tailTrace_1888460
  have hstable : (prefixWord ++ tailWord_1888460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888460).length < 2 ^ (prefixWord ++ tailWord_1888460).sum := by decide
  have hdescent : baseEnd_1888460 < baseStart_1888460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888499 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 3]
def baseStart_1888499 : Nat := 118140960795 + 1888499 * 2 ^ 59
def prefixEnd_1888499 : Nat := 4983230072969 + 3 ^ 40 * 1888499 * 2
def baseEnd_1888499 : Nat := 969707702535311972677457

theorem tailTrace_1888499 : CollatzResearch.WordTrace tailWord_1888499 prefixEnd_1888499 969707702535311972677457 := by
  unfold tailWord_1888499
  simp only [CollatzResearch.WordTrace]
  refine ⟨68879217185298127796388551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45919478123532085197592367 68879217185298127796388551)
  ·
    refine ⟨103318825777947191694582827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68879217185298127796388551 103318825777947191694582827)
    ·
      refine ⟨154978238666920787541874241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103318825777947191694582827 154978238666920787541874241)
      ·
        refine ⟨116233679000190590656405681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154978238666920787541874241 116233679000190590656405681)
        ·
          refine ⟨87175259250142942992304261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116233679000190590656405681 87175259250142942992304261)
          ·
            refine ⟨16345361109401801811057049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87175259250142942992304261 16345361109401801811057049)
            ·
              refine ⟨12259020832051351358292787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16345361109401801811057049 12259020832051351358292787)
              ·
                refine ⟨18388531248077027037439181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12259020832051351358292787 18388531248077027037439181)
                ·
                  refine ⟨6895699218028885139039693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18388531248077027037439181 6895699218028885139039693)
                  ·
                    refine ⟨2585887206760831927139885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6895699218028885139039693 2585887206760831927139885)
                    ·
                      refine ⟨969707702535311972677457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2585887206760831927139885 969707702535311972677457)
                      ·
                        rfl

theorem cell23_1888499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 3].length) (baseStart_1888499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888499 prefixEnd_1888499 := by exact prefixLift 1888499
  have htrace : WordTrace (prefixWord ++ tailWord_1888499) baseStart_1888499 baseEnd_1888499 := by
    simpa [prefixWord, tailWord_1888499, baseEnd_1888499] using wordTrace_append hprefix tailTrace_1888499
  have hstable : (prefixWord ++ tailWord_1888499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888499).length < 2 ^ (prefixWord ++ tailWord_1888499).sum := by decide
  have hdescent : baseEnd_1888499 < baseStart_1888499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888543 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 3, 3, 2]
def baseStart_1888543 : Nat := 118140960795 + 1888543 * 2 ^ 59
def prefixEnd_1888543 : Nat := 4983230072969 + 3 ^ 40 * 1888543 * 2
def baseEnd_1888543 : Nat := 969730295684109800527255

theorem tailTrace_1888543 : CollatzResearch.WordTrace tailWord_1888543 prefixEnd_1888543 969730295684109800527255 := by
  unfold tailWord_1888543
  simp only [CollatzResearch.WordTrace]
  refine ⟨68880821997138723310990283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45920547998092482207326855 68880821997138723310990283)
  ·
    refine ⟨103321232995708084966485425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68880821997138723310990283 103321232995708084966485425)
    ·
      refine ⟨77490924746781063724864069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103321232995708084966485425 77490924746781063724864069)
      ·
        refine ⟨14529548390021449448412013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77490924746781063724864069 14529548390021449448412013)
        ·
          refine ⟨5448580646258043543154505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14529548390021449448412013 5448580646258043543154505)
          ·
            refine ⟨4086435484693532657365879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5448580646258043543154505 4086435484693532657365879)
            ·
              refine ⟨6129653227040298986048819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086435484693532657365879 6129653227040298986048819)
              ·
                refine ⟨9194479840560448479073229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129653227040298986048819 9194479840560448479073229)
                ·
                  refine ⟨3447929940210168179652461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9194479840560448479073229 3447929940210168179652461)
                  ·
                    refine ⟨1292973727578813067369673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3447929940210168179652461 1292973727578813067369673)
                    ·
                      refine ⟨969730295684109800527255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292973727578813067369673 969730295684109800527255)
                      ·
                        rfl

theorem cell23_1888543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_1888543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888543 prefixEnd_1888543 := by exact prefixLift 1888543
  have htrace : WordTrace (prefixWord ++ tailWord_1888543) baseStart_1888543 baseEnd_1888543 := by
    simpa [prefixWord, tailWord_1888543, baseEnd_1888543] using wordTrace_append hprefix tailTrace_1888543
  have hstable : (prefixWord ++ tailWord_1888543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888543).length < 2 ^ (prefixWord ++ tailWord_1888543).sum := by decide
  have hdescent : baseEnd_1888543 < baseStart_1888543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888556 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 3, 4, 2]
def baseStart_1888556 : Nat := 118140960795 + 1888556 * 2 ^ 59
def prefixEnd_1888556 : Nat := 4983230072969 + 3 ^ 40 * 1888556 * 2
def baseEnd_1888556 : Nat := 969736970932618249664695

theorem tailTrace_1888556 : CollatzResearch.WordTrace tailWord_1888556 prefixEnd_1888556 969736970932618249664695 := by
  unfold tailWord_1888556
  simp only [CollatzResearch.WordTrace]
  refine ⟨34440648073045813265606761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45920864097394417687475681 34440648073045813265606761)
  ·
    refine ⟨25830486054784359949205071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34440648073045813265606761 25830486054784359949205071)
    ·
      refine ⟨38745729082176539923807607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25830486054784359949205071 38745729082176539923807607)
      ·
        refine ⟨58118593623264809885711411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38745729082176539923807607 58118593623264809885711411)
        ·
          refine ⟨87177890434897214828567117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58118593623264809885711411 87177890434897214828567117)
          ·
            refine ⟨32691708913086455560712669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87177890434897214828567117 32691708913086455560712669)
            ·
              refine ⟨12259390842407420835267251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32691708913086455560712669 12259390842407420835267251)
              ·
                refine ⟨18389086263611131252900877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12259390842407420835267251 18389086263611131252900877)
                ·
                  refine ⟨6895907348854174219837829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18389086263611131252900877 6895907348854174219837829)
                  ·
                    refine ⟨1292982627910157666219593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6895907348854174219837829 1292982627910157666219593)
                    ·
                      refine ⟨969736970932618249664695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1292982627910157666219593 969736970932618249664695)
                      ·
                        rfl

theorem cell23_1888556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 4, 2].length) (baseStart_1888556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888556 prefixEnd_1888556 := by exact prefixLift 1888556
  have htrace : WordTrace (prefixWord ++ tailWord_1888556) baseStart_1888556 baseEnd_1888556 := by
    simpa [prefixWord, tailWord_1888556, baseEnd_1888556] using wordTrace_append hprefix tailTrace_1888556
  have hstable : (prefixWord ++ tailWord_1888556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888556).length < 2 ^ (prefixWord ++ tailWord_1888556).sum := by decide
  have hdescent : baseEnd_1888556 < baseStart_1888556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888559 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 5]
def baseStart_1888559 : Nat := 118140960795 + 1888559 * 2 ^ 59
def prefixEnd_1888559 : Nat := 4983230072969 + 3 ^ 40 * 1888559 * 2
def baseEnd_1888559 : Nat := 969738511374581737927181

theorem tailTrace_1888559 : CollatzResearch.WordTrace tailWord_1888559 prefixEnd_1888559 969738511374581737927181 := by
  unfold tailWord_1888559
  simp only [CollatzResearch.WordTrace]
  refine ⟨68881405565080758043572731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45920937043387172029048487 68881405565080758043572731)
  ·
    refine ⟨103322108347621137065359097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68881405565080758043572731 103322108347621137065359097)
    ·
      refine ⟨77491581260715852799019323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103322108347621137065359097 77491581260715852799019323)
      ·
        refine ⟨116237371891073779198528985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77491581260715852799019323 116237371891073779198528985)
        ·
          refine ⟨87178028918305334398896739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116237371891073779198528985 87178028918305334398896739)
          ·
            refine ⟨130767043377458001598345109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87178028918305334398896739 130767043377458001598345109)
            ·
              refine ⟨6129705158318343824922427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130767043377458001598345109 6129705158318343824922427)
              ·
                refine ⟨9194557737477515737383641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129705158318343824922427 9194557737477515737383641)
                ·
                  refine ⟨6895918303108136803037731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9194557737477515737383641 6895918303108136803037731)
                  ·
                    refine ⟨10343877454662205204556597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6895918303108136803037731 10343877454662205204556597)
                    ·
                      refine ⟨969738511374581737927181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10343877454662205204556597 969738511374581737927181)
                      ·
                        rfl

theorem cell23_1888559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_1888559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888559 prefixEnd_1888559 := by exact prefixLift 1888559
  have htrace : WordTrace (prefixWord ++ tailWord_1888559) baseStart_1888559 baseEnd_1888559 := by
    simpa [prefixWord, tailWord_1888559, baseEnd_1888559] using wordTrace_append hprefix tailTrace_1888559
  have hstable : (prefixWord ++ tailWord_1888559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888559).length < 2 ^ (prefixWord ++ tailWord_1888559).sum := by decide
  have hdescent : baseEnd_1888559 < baseStart_1888559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888596 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 7]
def baseStart_1888596 : Nat := 118140960795 + 1888596 * 2 ^ 59
def prefixEnd_1888596 : Nat := 4983230072969 + 3 ^ 40 * 1888596 * 2
def baseEnd_1888596 : Nat := 107750834462088677018279

theorem tailTrace_1888596 : CollatzResearch.WordTrace tailWord_1888596 prefixEnd_1888596 107750834462088677018279 := by
  unfold tailWord_1888596
  simp only [CollatzResearch.WordTrace]
  refine ⟨34441377532973356681334821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45921836710631142241779761 34441377532973356681334821)
  ·
    refine ⟨6457758287432504377750279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34441377532973356681334821 6457758287432504377750279)
    ·
      refine ⟨9686637431148756566625419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6457758287432504377750279 9686637431148756566625419)
      ·
        refine ⟨14529956146723134849938129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9686637431148756566625419 14529956146723134849938129)
        ·
          refine ⟨10897467110042351137453597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14529956146723134849938129 10897467110042351137453597)
          ·
            refine ⟨4086550166265881676545099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10897467110042351137453597 4086550166265881676545099)
            ·
              refine ⟨6129825249398822514817649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086550166265881676545099 6129825249398822514817649)
              ·
                refine ⟨4597368937049116886113237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6129825249398822514817649 4597368937049116886113237)
                ·
                  refine ⟨107750834462088677018279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4597368937049116886113237 107750834462088677018279)
                  ·
                    rfl

theorem cell23_1888596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_1888596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888596 prefixEnd_1888596 := by exact prefixLift 1888596
  have htrace : WordTrace (prefixWord ++ tailWord_1888596) baseStart_1888596 baseEnd_1888596 := by
    simpa [prefixWord, tailWord_1888596, baseEnd_1888596] using wordTrace_append hprefix tailTrace_1888596
  have hstable : (prefixWord ++ tailWord_1888596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888596).length < 2 ^ (prefixWord ++ tailWord_1888596).sum := by decide
  have hdescent : baseEnd_1888596 < baseStart_1888596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888613 : List Nat := [1, 3, 1, 3, 1, 4, 2, 3, 5]
def baseStart_1888613 : Nat := 118140960795 + 1888613 * 2 ^ 59
def prefixEnd_1888613 : Nat := 4983230072969 + 3 ^ 40 * 1888613 * 2
def baseEnd_1888613 : Nat := 107751804369991614072437

theorem tailTrace_1888613 : CollatzResearch.WordTrace tailWord_1888613 prefixEnd_1888613 107751804369991614072437 := by
  unfold tailWord_1888613
  simp only [CollatzResearch.WordTrace]
  refine ⟨68883375106885125266038493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45922250071256750177358995 68883375106885125266038493)
  ·
    refine ⟨25831265665081921974764435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68883375106885125266038493 25831265665081921974764435)
    ·
      refine ⟨38746898497622882962146653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25831265665081921974764435 38746898497622882962146653)
      ·
        refine ⟨14530086936608581110804995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38746898497622882962146653 14530086936608581110804995)
        ·
          refine ⟨21795130404912871666207493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14530086936608581110804995 21795130404912871666207493)
          ·
            refine ⟨4086586950921163437413905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21795130404912871666207493 4086586950921163437413905)
            ·
              refine ⟨3064940213190872578060429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4086586950921163437413905 3064940213190872578060429)
              ·
                refine ⟨1149352579946577216772661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3064940213190872578060429 1149352579946577216772661)
                ·
                  refine ⟨107751804369991614072437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1149352579946577216772661 107751804369991614072437)
                  ·
                    rfl

theorem cell23_1888613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_1888613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888613 prefixEnd_1888613 := by exact prefixLift 1888613
  have htrace : WordTrace (prefixWord ++ tailWord_1888613) baseStart_1888613 baseEnd_1888613 := by
    simpa [prefixWord, tailWord_1888613, baseEnd_1888613] using wordTrace_append hprefix tailTrace_1888613
  have hstable : (prefixWord ++ tailWord_1888613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888613).length < 2 ^ (prefixWord ++ tailWord_1888613).sum := by decide
  have hdescent : baseEnd_1888613 < baseStart_1888613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888630 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_1888630 : Nat := 118140960795 + 1888630 * 2 ^ 59
def prefixEnd_1888630 : Nat := 4983230072969 + 3 ^ 40 * 1888630 * 2
def baseEnd_1888630 : Nat := 107752774277894551126595

theorem tailTrace_1888630 : CollatzResearch.WordTrace tailWord_1888630 prefixEnd_1888630 107752774277894551126595 := by
  unfold tailWord_1888630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4305249696738971073087959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45922663431882358112938229 4305249696738971073087959)
  ·
    refine ⟨6457874545108456609631939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4305249696738971073087959 6457874545108456609631939)
    ·
      refine ⟨9686811817662684914447909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6457874545108456609631939 9686811817662684914447909)
      ·
        refine ⟨1816277215811753421458983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9686811817662684914447909 1816277215811753421458983)
        ·
          refine ⟨2724415823717630132188475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816277215811753421458983 2724415823717630132188475)
          ·
            refine ⟨4086623735576445198282713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724415823717630132188475 4086623735576445198282713)
            ·
              refine ⟨3064967801682333898712035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4086623735576445198282713 3064967801682333898712035)
              ·
                refine ⟨4597451702523500848068053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064967801682333898712035 4597451702523500848068053)
                ·
                  refine ⟨107752774277894551126595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4597451702523500848068053 107752774277894551126595)
                  ·
                    rfl

theorem cell23_1888630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_1888630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888630 prefixEnd_1888630 := by exact prefixLift 1888630
  have htrace : WordTrace (prefixWord ++ tailWord_1888630) baseStart_1888630 baseEnd_1888630 := by
    simpa [prefixWord, tailWord_1888630, baseEnd_1888630] using wordTrace_append hprefix tailTrace_1888630
  have hstable : (prefixWord ++ tailWord_1888630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888630).length < 2 ^ (prefixWord ++ tailWord_1888630).sum := by decide
  have hdescent : baseEnd_1888630 < baseStart_1888630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888680 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1888680 : Nat := 118140960795 + 1888680 * 2 ^ 59
def prefixEnd_1888680 : Nat := 4983230072969 + 3 ^ 40 * 1888680 * 2
def baseEnd_1888680 : Nat := 969800642533775764514125

theorem tailTrace_1888680 : CollatzResearch.WordTrace tailWord_1888680 prefixEnd_1888680 969800642533775764514125 := by
  unfold tailWord_1888680
  simp only [CollatzResearch.WordTrace]
  refine ⟨34442909398821197854363747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45923879198428263805818329 34442909398821197854363747)
  ·
    refine ⟨51664364098231796781545621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34442909398821197854363747 51664364098231796781545621)
    ·
      refine ⟨2421767067104615474134951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51664364098231796781545621 2421767067104615474134951)
      ·
        refine ⟨3632650600656923211202427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421767067104615474134951 3632650600656923211202427)
        ·
          refine ⟨5448975900985384816803641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632650600656923211202427 5448975900985384816803641)
          ·
            refine ⟨4086731925739038612602731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5448975900985384816803641 4086731925739038612602731)
            ·
              refine ⟨6130097888608557918904097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086731925739038612602731 6130097888608557918904097)
              ·
                refine ⟨4597573416456418439178073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6130097888608557918904097 4597573416456418439178073)
                ·
                  refine ⟨3448180062342313829383555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4597573416456418439178073 3448180062342313829383555)
                  ·
                    refine ⟨5172270093513470744075333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3448180062342313829383555 5172270093513470744075333)
                    ·
                      refine ⟨969800642533775764514125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5172270093513470744075333 969800642533775764514125)
                      ·
                        rfl

theorem cell23_1888680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1888680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888680 prefixEnd_1888680 := by exact prefixLift 1888680
  have htrace : WordTrace (prefixWord ++ tailWord_1888680) baseStart_1888680 baseEnd_1888680 := by
    simpa [prefixWord, tailWord_1888680, baseEnd_1888680] using wordTrace_append hprefix tailTrace_1888680
  have hstable : (prefixWord ++ tailWord_1888680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888680).length < 2 ^ (prefixWord ++ tailWord_1888680).sum := by decide
  have hdescent : baseEnd_1888680 < baseStart_1888680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888713 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 3, 1, 3]
def baseStart_1888713 : Nat := 118140960795 + 1888713 * 2 ^ 59
def prefixEnd_1888713 : Nat := 4983230072969 + 3 ^ 40 * 1888713 * 2
def baseEnd_1888713 : Nat := 969817587395374135401473

theorem tailTrace_1888713 : CollatzResearch.WordTrace tailWord_1888713 prefixEnd_1888713 969817587395374135401473 := by
  unfold tailWord_1888713
  simp only [CollatzResearch.WordTrace]
  refine ⟨68887022406522842344678793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45924681604348561563119195 68887022406522842344678793)
  ·
    refine ⟨51665266804892131758509095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68887022406522842344678793 51665266804892131758509095)
    ·
      refine ⟨77497900207338197637763643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51665266804892131758509095 77497900207338197637763643)
      ·
        refine ⟨116246850311007296456645465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77497900207338197637763643 116246850311007296456645465)
        ·
          refine ⟨87185137733255472342484099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116246850311007296456645465 87185137733255472342484099)
          ·
            refine ⟨130777706599883208513726149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87185137733255472342484099 130777706599883208513726149)
            ·
              refine ⟨24520819987478101596323653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130777706599883208513726149 24520819987478101596323653)
              ·
                refine ⟨4597653747652144049310685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24520819987478101596323653 4597653747652144049310685)
                ·
                  refine ⟨1724120155369554018491507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4597653747652144049310685 1724120155369554018491507)
                  ·
                    refine ⟨2586180233054331027737261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1724120155369554018491507 2586180233054331027737261)
                    ·
                      refine ⟨969817587395374135401473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2586180233054331027737261 969817587395374135401473)
                      ·
                        rfl

theorem cell23_1888713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 1, 3].length) (baseStart_1888713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888713 prefixEnd_1888713 := by exact prefixLift 1888713
  have htrace : WordTrace (prefixWord ++ tailWord_1888713) baseStart_1888713 baseEnd_1888713 := by
    simpa [prefixWord, tailWord_1888713, baseEnd_1888713] using wordTrace_append hprefix tailTrace_1888713
  have hstable : (prefixWord ++ tailWord_1888713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888713).length < 2 ^ (prefixWord ++ tailWord_1888713).sum := by decide
  have hdescent : baseEnd_1888713 < baseStart_1888713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888741 : List Nat := [1, 3, 1, 5, 3, 1, 2, 2, 1, 4]
def baseStart_1888741 : Nat := 118140960795 + 1888741 * 2 ^ 59
def prefixEnd_1888741 : Nat := 4983230072969 + 3 ^ 40 * 1888741 * 2
def baseEnd_1888741 : Nat := 323277321617900008617115

theorem tailTrace_1888741 : CollatzResearch.WordTrace tailWord_1888741 prefixEnd_1888741 323277321617900008617115 := by
  unfold tailWord_1888741
  simp only [CollatzResearch.WordTrace]
  refine ⟨68888043650421403126698077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45925362433614268751132051 68888043650421403126698077)
  ·
    refine ⟨25833016368908026172511779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68888043650421403126698077 25833016368908026172511779)
    ·
      refine ⟨38749524553362039258767669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25833016368908026172511779 38749524553362039258767669)
      ·
        refine ⟨3632767926877691180509469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38749524553362039258767669 3632767926877691180509469)
        ·
          refine ⟨1362287972579134192691051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3632767926877691180509469 1362287972579134192691051)
          ·
            refine ⟨2043431958868701289036577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362287972579134192691051 2043431958868701289036577)
            ·
              refine ⟨1532573969151525966777433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043431958868701289036577 1532573969151525966777433)
              ·
                refine ⟨1149430476863644475083075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532573969151525966777433 1149430476863644475083075)
                ·
                  refine ⟨1724145715295466712624613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149430476863644475083075 1724145715295466712624613)
                  ·
                    refine ⟨323277321617900008617115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1724145715295466712624613 323277321617900008617115)
                    ·
                      rfl

theorem cell23_1888741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_1888741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888741 prefixEnd_1888741 := by exact prefixLift 1888741
  have htrace : WordTrace (prefixWord ++ tailWord_1888741) baseStart_1888741 baseEnd_1888741 := by
    simpa [prefixWord, tailWord_1888741, baseEnd_1888741] using wordTrace_append hprefix tailTrace_1888741
  have hstable : (prefixWord ++ tailWord_1888741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888741).length < 2 ^ (prefixWord ++ tailWord_1888741).sum := by decide
  have hdescent : baseEnd_1888741 < baseStart_1888741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888773 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 3, 2, 3]
def baseStart_1888773 : Nat := 118140960795 + 1888773 * 2 ^ 59
def prefixEnd_1888773 : Nat := 4983230072969 + 3 ^ 40 * 1888773 * 2
def baseEnd_1888773 : Nat := 969848396234643900651197

theorem tailTrace_1888773 : CollatzResearch.WordTrace tailWord_1888773 prefixEnd_1888773 969848396234643900651197 := by
  unfold tailWord_1888773
  simp only [CollatzResearch.WordTrace]
  refine ⟨68889210786305472591862973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45926140524203648394575315 68889210786305472591862973)
  ·
    refine ⟨25833454044864552221948615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68889210786305472591862973 25833454044864552221948615)
    ·
      refine ⟨38750181067296828332922923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25833454044864552221948615 38750181067296828332922923)
      ·
        refine ⟨58125271600945242499384385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38750181067296828332922923 58125271600945242499384385)
        ·
          refine ⟨43593953700708931874538289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58125271600945242499384385 43593953700708931874538289)
          ·
            refine ⟨32695465275531698905903717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43593953700708931874538289 32695465275531698905903717)
            ·
              refine ⟨6130399739162193544856947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32695465275531698905903717 6130399739162193544856947)
              ·
                refine ⟨9195599608743290317285421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6130399739162193544856947 9195599608743290317285421)
                ·
                  refine ⟨3448349853278733868982033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9195599608743290317285421 3448349853278733868982033)
                  ·
                    refine ⟨2586262389959050401736525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3448349853278733868982033 2586262389959050401736525)
                    ·
                      refine ⟨969848396234643900651197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2586262389959050401736525 969848396234643900651197)
                      ·
                        rfl

theorem cell23_1888773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_1888773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888773 prefixEnd_1888773 := by exact prefixLift 1888773
  have htrace : WordTrace (prefixWord ++ tailWord_1888773) baseStart_1888773 baseEnd_1888773 := by
    simpa [prefixWord, tailWord_1888773, baseEnd_1888773] using wordTrace_append hprefix tailTrace_1888773
  have hstable : (prefixWord ++ tailWord_1888773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888773).length < 2 ^ (prefixWord ++ tailWord_1888773).sum := by decide
  have hdescent : baseEnd_1888773 < baseStart_1888773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888781 : List Nat := [1, 7, 1, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_1888781 : Nat := 118140960795 + 1888781 * 2 ^ 59
def prefixEnd_1888781 : Nat := 4983230072969 + 3 ^ 40 * 1888781 * 2
def baseEnd_1888781 : Nat := 969852504079879869351161

theorem tailTrace_1888781 : CollatzResearch.WordTrace tailWord_1888781 prefixEnd_1888781 969852504079879869351161 := by
  unfold tailWord_1888781
  simp only [CollatzResearch.WordTrace]
  refine ⟨68889502570276489958154197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45926335046850993305436131 68889502570276489958154197)
  ·
    refine ⟨1614597716490855233394239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 68889502570276489958154197 1614597716490855233394239)
    ·
      refine ⟨2421896574736282850091359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614597716490855233394239 2421896574736282850091359)
      ·
        refine ⟨3632844862104424275137039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421896574736282850091359 3632844862104424275137039)
        ·
          refine ⟨5449267293156636412705559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632844862104424275137039 5449267293156636412705559)
          ·
            refine ⟨8173900939734954619058339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449267293156636412705559 8173900939734954619058339)
            ·
              refine ⟨12260851409602431928587509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8173900939734954619058339 12260851409602431928587509)
              ·
                refine ⟨1149454819650227993305079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12260851409602431928587509 1149454819650227993305079)
                ·
                  refine ⟨1724182229475341989957619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149454819650227993305079 1724182229475341989957619)
                  ·
                    refine ⟨2586273344213012984936429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1724182229475341989957619 2586273344213012984936429)
                    ·
                      refine ⟨969852504079879869351161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2586273344213012984936429 969852504079879869351161)
                      ·
                        rfl

theorem cell23_1888781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_1888781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888781 prefixEnd_1888781 := by exact prefixLift 1888781
  have htrace : WordTrace (prefixWord ++ tailWord_1888781) baseStart_1888781 baseEnd_1888781 := by
    simpa [prefixWord, tailWord_1888781, baseEnd_1888781] using wordTrace_append hprefix tailTrace_1888781
  have hstable : (prefixWord ++ tailWord_1888781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888781).length < 2 ^ (prefixWord ++ tailWord_1888781).sum := by decide
  have hdescent : baseEnd_1888781 < baseStart_1888781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888797 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1888797 : Nat := 118140960795 + 1888797 * 2 ^ 59
def prefixEnd_1888797 : Nat := 4983230072969 + 3 ^ 40 * 1888797 * 2
def baseEnd_1888797 : Nat := 323286906590117268917029

theorem tailTrace_1888797 : CollatzResearch.WordTrace tailWord_1888797 prefixEnd_1888797 323286906590117268917029 := by
  unfold tailWord_1888797
  simp only [CollatzResearch.WordTrace]
  refine ⟨68890086138218524690736645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45926724092145683127157763 68890086138218524690736645)
  ·
    refine ⟨12916891150915973379513121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68890086138218524690736645 12916891150915973379513121)
    ·
      refine ⟨9687668363186980034634841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12916891150915973379513121 9687668363186980034634841)
      ·
        refine ⟨7265751272390235025976131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9687668363186980034634841 7265751272390235025976131)
        ·
          refine ⟨10898626908585352538964197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7265751272390235025976131 10898626908585352538964197)
          ·
            refine ⟨2043492545359753601055787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10898626908585352538964197 2043492545359753601055787)
            ·
              refine ⟨3065238818039630401583681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043492545359753601055787 3065238818039630401583681)
              ·
                refine ⟨2298929113529722801187761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3065238818039630401583681 2298929113529722801187761)
                ·
                  refine ⟨1724196835147292100890821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2298929113529722801187761 1724196835147292100890821)
                  ·
                    refine ⟨323286906590117268917029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1724196835147292100890821 323286906590117268917029)
                    ·
                      rfl

theorem cell23_1888797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1888797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888797 prefixEnd_1888797 := by exact prefixLift 1888797
  have htrace : WordTrace (prefixWord ++ tailWord_1888797) baseStart_1888797 baseEnd_1888797 := by
    simpa [prefixWord, tailWord_1888797, baseEnd_1888797] using wordTrace_append hprefix tailTrace_1888797
  have hstable : (prefixWord ++ tailWord_1888797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888797).length < 2 ^ (prefixWord ++ tailWord_1888797).sum := by decide
  have hdescent : baseEnd_1888797 < baseStart_1888797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888807 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1888807 : Nat := 118140960795 + 1888807 * 2 ^ 59
def prefixEnd_1888807 : Nat := 4983230072969 + 3 ^ 40 * 1888807 * 2
def baseEnd_1888807 : Nat := 969865854576896767626041

theorem tailTrace_1888807 : CollatzResearch.WordTrace tailWord_1888807 prefixEnd_1888807 969865854576896767626041 := by
  unfold tailWord_1888807
  simp only [CollatzResearch.WordTrace]
  refine ⟨68890450868182296398600675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45926967245454864265733783 68890450868182296398600675)
  ·
    refine ⟨103335676302273444597901013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68890450868182296398600675 103335676302273444597901013)
    ·
      refine ⟨2421929913334533857763305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 103335676302273444597901013 2421929913334533857763305)
      ·
        refine ⟨1816447435000900393322479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2421929913334533857763305 1816447435000900393322479)
        ·
          refine ⟨2724671152501350589983719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816447435000900393322479 2724671152501350589983719)
          ·
            refine ⟨4087006728752025884975579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724671152501350589983719 4087006728752025884975579)
            ·
              refine ⟨6130510093128038827463369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4087006728752025884975579 6130510093128038827463369)
              ·
                refine ⟨4597882569846029120597527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6130510093128038827463369 4597882569846029120597527)
                ·
                  refine ⟨6896823854769043680896291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597882569846029120597527 6896823854769043680896291)
                  ·
                    refine ⟨10345235782153565521344437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6896823854769043680896291 10345235782153565521344437)
                    ·
                      refine ⟨969865854576896767626041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10345235782153565521344437 969865854576896767626041)
                      ·
                        rfl

theorem cell23_1888807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1888807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888807 prefixEnd_1888807 := by exact prefixLift 1888807
  have htrace : WordTrace (prefixWord ++ tailWord_1888807) baseStart_1888807 baseEnd_1888807 := by
    simpa [prefixWord, tailWord_1888807, baseEnd_1888807] using wordTrace_append hprefix tailTrace_1888807
  have hstable : (prefixWord ++ tailWord_1888807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888807).length < 2 ^ (prefixWord ++ tailWord_1888807).sum := by decide
  have hdescent : baseEnd_1888807 < baseStart_1888807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888814 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_1888814 : Nat := 118140960795 + 1888814 * 2 ^ 59
def prefixEnd_1888814 : Nat := 4983230072969 + 3 ^ 40 * 1888814 * 2
def baseEnd_1888814 : Nat := 323289816313826080079503

theorem tailTrace_1888814 : CollatzResearch.WordTrace tailWord_1888814 prefixEnd_1888814 323289816313826080079503 := by
  unfold tailWord_1888814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8611338272394617074263187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45927137452771291062736997 8611338272394617074263187)
  ·
    refine ⟨12917007408591925611394781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8611338272394617074263187 12917007408591925611394781)
    ·
      refine ⟨4843877778221972104273043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12917007408591925611394781 4843877778221972104273043)
      ·
        refine ⟨7265816667332958156409565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4843877778221972104273043 7265816667332958156409565)
        ·
          refine ⟨2724681250249859308653587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7265816667332958156409565 2724681250249859308653587)
          ·
            refine ⟨4087021875374788962980381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724681250249859308653587 4087021875374788962980381)
            ·
              refine ⟨1532633203265545861117643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4087021875374788962980381 1532633203265545861117643)
              ·
                refine ⟨2298949804898318791676465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532633203265545861117643 2298949804898318791676465)
                ·
                  refine ⟨1724212353673739093757349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2298949804898318791676465 1724212353673739093757349)
                  ·
                    refine ⟨323289816313826080079503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1724212353673739093757349 323289816313826080079503)
                    ·
                      rfl

theorem cell23_1888814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_1888814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888814 prefixEnd_1888814 := by exact prefixLift 1888814
  have htrace : WordTrace (prefixWord ++ tailWord_1888814) baseStart_1888814 baseEnd_1888814 := by
    simpa [prefixWord, tailWord_1888814, baseEnd_1888814] using wordTrace_append hprefix tailTrace_1888814
  have hstable : (prefixWord ++ tailWord_1888814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888814).length < 2 ^ (prefixWord ++ tailWord_1888814).sum := by decide
  have hdescent : baseEnd_1888814 < baseStart_1888814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888833 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1888833 : Nat := 118140960795 + 1888833 * 2 ^ 59
def prefixEnd_1888833 : Nat := 4983230072969 + 3 ^ 40 * 1888833 * 2
def baseEnd_1888833 : Nat := 969879205073913665900921

theorem tailTrace_1888833 : CollatzResearch.WordTrace tailWord_1888833 prefixEnd_1888833 969879205073913665900921 := by
  unfold tailWord_1888833
  simp only [CollatzResearch.WordTrace]
  refine ⟨68891399166088102839047153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45927599444058735226031435 68891399166088102839047153)
  ·
    refine ⟨51668549374566077129285365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68891399166088102839047153 51668549374566077129285365)
    ·
      refine ⟨4843926503865569730870503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51668549374566077129285365 4843926503865569730870503)
      ·
        refine ⟨7265889755798354596305755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4843926503865569730870503 7265889755798354596305755)
        ·
          refine ⟨10898834633697531894458633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7265889755798354596305755 10898834633697531894458633)
          ·
            refine ⟨8174125975273148920843975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10898834633697531894458633 8174125975273148920843975)
            ·
              refine ⟨12261188962909723381265963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8174125975273148920843975 12261188962909723381265963)
              ·
                refine ⟨18391783444364585071898945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12261188962909723381265963 18391783444364585071898945)
                ·
                  refine ⟨13793837583273438803924209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18391783444364585071898945 13793837583273438803924209)
                  ·
                    refine ⟨10345378187455079102943157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13793837583273438803924209 10345378187455079102943157)
                    ·
                      refine ⟨969879205073913665900921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10345378187455079102943157 969879205073913665900921)
                      ·
                        rfl

theorem cell23_1888833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1888833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888833 prefixEnd_1888833 := by exact prefixLift 1888833
  have htrace : WordTrace (prefixWord ++ tailWord_1888833) baseStart_1888833 baseEnd_1888833 := by
    simpa [prefixWord, tailWord_1888833, baseEnd_1888833] using wordTrace_append hprefix tailTrace_1888833
  have hstable : (prefixWord ++ tailWord_1888833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888833).length < 2 ^ (prefixWord ++ tailWord_1888833).sum := by decide
  have hdescent : baseEnd_1888833 < baseStart_1888833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888838 : List Nat := [6, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_1888838 : Nat := 118140960795 + 1888838 * 2 ^ 59
def prefixEnd_1888838 : Nat := 4983230072969 + 3 ^ 40 * 1888838 * 2
def baseEnd_1888838 : Nat := 969881772477186146338399

theorem tailTrace_1888838 : CollatzResearch.WordTrace tailWord_1888838 prefixEnd_1888838 969881772477186146338399 := by
  unfold tailWord_1888838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152861922845937146655599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45927721020713325795319445 2152861922845937146655599)
  ·
    refine ⟨3229292884268905719983399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2152861922845937146655599 3229292884268905719983399)
    ·
      refine ⟨4843939326403358579975099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3229292884268905719983399 4843939326403358579975099)
      ·
        refine ⟨7265908989605037869962649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4843939326403358579975099 7265908989605037869962649)
        ·
          refine ⟨5449431742203778402471987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7265908989605037869962649 5449431742203778402471987)
          ·
            refine ⟨8174147613305667603707981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449431742203778402471987 8174147613305667603707981)
            ·
              refine ⟨3065305354989625351390493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8174147613305667603707981 3065305354989625351390493)
              ·
                refine ⟨1149489508121109506771435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3065305354989625351390493 1149489508121109506771435)
                ·
                  refine ⟨1724234262181664260157153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149489508121109506771435 1724234262181664260157153)
                  ·
                    refine ⟨1293175696636248195117865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1724234262181664260157153 1293175696636248195117865)
                    ·
                      refine ⟨969881772477186146338399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293175696636248195117865 969881772477186146338399)
                      ·
                        rfl

theorem cell23_1888838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_1888838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888838 prefixEnd_1888838 := by exact prefixLift 1888838
  have htrace : WordTrace (prefixWord ++ tailWord_1888838) baseStart_1888838 baseEnd_1888838 := by
    simpa [prefixWord, tailWord_1888838, baseEnd_1888838] using wordTrace_append hprefix tailTrace_1888838
  have hstable : (prefixWord ++ tailWord_1888838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888838).length < 2 ^ (prefixWord ++ tailWord_1888838).sum := by decide
  have hdescent : baseEnd_1888838 < baseStart_1888838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888910 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1888910 : Nat := 118140960795 + 1888910 * 2 ^ 59
def prefixEnd_1888910 : Nat := 4983230072969 + 3 ^ 40 * 1888910 * 2
def baseEnd_1888910 : Nat := 969918743084309864638067

theorem tailTrace_1888910 : CollatzResearch.WordTrace tailWord_1888910 prefixEnd_1888910 969918743084309864638067 := by
  unfold tailWord_1888910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8611775948351143123700023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45929471724539429993066789 8611775948351143123700023)
  ·
    refine ⟨12917663922526714685550035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8611775948351143123700023 12917663922526714685550035)
    ·
      refine ⟨19376495883790072028325053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12917663922526714685550035 19376495883790072028325053)
      ·
        refine ⟨7266185956421277010621895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19376495883790072028325053 7266185956421277010621895)
        ·
          refine ⟨10899278934631915515932843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7266185956421277010621895 10899278934631915515932843)
          ·
            refine ⟨16348918401947873273899265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10899278934631915515932843 16348918401947873273899265)
            ·
              refine ⟨12261688801460904955424449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16348918401947873273899265 12261688801460904955424449)
              ·
                refine ⟨9196266601095678716568337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12261688801460904955424449 9196266601095678716568337)
                ·
                  refine ⟨6897199950821759037426253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9196266601095678716568337 6897199950821759037426253)
                  ·
                    refine ⟨2586449981558159639034845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6897199950821759037426253 2586449981558159639034845)
                    ·
                      refine ⟨969918743084309864638067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2586449981558159639034845 969918743084309864638067)
                      ·
                        rfl

theorem cell23_1888910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1888910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888910 prefixEnd_1888910 := by exact prefixLift 1888910
  have htrace : WordTrace (prefixWord ++ tailWord_1888910) baseStart_1888910 baseEnd_1888910 := by
    simpa [prefixWord, tailWord_1888910, baseEnd_1888910] using wordTrace_append hprefix tailTrace_1888910
  have hstable : (prefixWord ++ tailWord_1888910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888910).length < 2 ^ (prefixWord ++ tailWord_1888910).sum := by decide
  have hdescent : baseEnd_1888910 < baseStart_1888910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888920 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 1, 7, 2]
def baseStart_1888920 : Nat := 118140960795 + 1888920 * 2 ^ 59
def prefixEnd_1888920 : Nat := 4983230072969 + 3 ^ 40 * 1888920 * 2
def baseEnd_1888920 : Nat := 969923877890854825513021

theorem tailTrace_1888920 : CollatzResearch.WordTrace tailWord_1888920 prefixEnd_1888920 969923877890854825513021 := by
  unfold tailWord_1888920
  simp only [CollatzResearch.WordTrace]
  refine ⟨34447286158386458348732107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45929714877848611131642809 34447286158386458348732107)
  ·
    refine ⟨51670929237579687523098161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34447286158386458348732107 51670929237579687523098161)
    ·
      refine ⟨38753196928184765642323621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51670929237579687523098161 38753196928184765642323621)
      ·
        refine ⟨7266224424034643557935679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38753196928184765642323621 7266224424034643557935679)
        ·
          refine ⟨10899336636051965336903519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7266224424034643557935679 10899336636051965336903519)
          ·
            refine ⟨16349004954077948005355279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10899336636051965336903519 16349004954077948005355279)
            ·
              refine ⟨24523507431116922008032919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16349004954077948005355279 24523507431116922008032919)
              ·
                refine ⟨36785261146675383012049379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24523507431116922008032919 36785261146675383012049379)
                ·
                  refine ⟨55177891720013074518074069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36785261146675383012049379 55177891720013074518074069)
                  ·
                    refine ⟨1293231837187806434017361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55177891720013074518074069 1293231837187806434017361)
                    ·
                      refine ⟨969923877890854825513021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293231837187806434017361 969923877890854825513021)
                      ·
                        rfl

theorem cell23_1888920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_1888920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888920 prefixEnd_1888920 := by exact prefixLift 1888920
  have htrace : WordTrace (prefixWord ++ tailWord_1888920) baseStart_1888920 baseEnd_1888920 := by
    simpa [prefixWord, tailWord_1888920, baseEnd_1888920] using wordTrace_append hprefix tailTrace_1888920
  have hstable : (prefixWord ++ tailWord_1888920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888920).length < 2 ^ (prefixWord ++ tailWord_1888920).sum := by decide
  have hdescent : baseEnd_1888920 < baseStart_1888920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888933 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_1888933 : Nat := 118140960795 + 1888933 * 2 ^ 59
def prefixEnd_1888933 : Nat := 4983230072969 + 3 ^ 40 * 1888933 * 2
def baseEnd_1888933 : Nat := 969930553139363274650461

theorem tailTrace_1888933 : CollatzResearch.WordTrace tailWord_1888933 prefixEnd_1888933 969930553139363274650461 := by
  unfold tailWord_1888933
  simp only [CollatzResearch.WordTrace]
  refine ⟨68895046465725819917687453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45930030977150546611791635 68895046465725819917687453)
  ·
    refine ⟨25835642424647182469132795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68895046465725819917687453 25835642424647182469132795)
    ·
      refine ⟨38753463636970773703699193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25835642424647182469132795 38753463636970773703699193)
      ·
        refine ⟨29065097727728080277774395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38753463636970773703699193 29065097727728080277774395)
        ·
          refine ⟨43597646591592120416661593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29065097727728080277774395 43597646591592120416661593)
          ·
            refine ⟨32698234943694090312496195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43597646591592120416661593 32698234943694090312496195)
            ·
              refine ⟨49047352415541135468744293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32698234943694090312496195 49047352415541135468744293)
              ·
                refine ⟨9196378577913962900389555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49047352415541135468744293 9196378577913962900389555)
                ·
                  refine ⟨13794567866870944350584333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9196378577913962900389555 13794567866870944350584333)
                  ·
                    refine ⟨5172962950076604131469125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13794567866870944350584333 5172962950076604131469125)
                    ·
                      refine ⟨969930553139363274650461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5172962950076604131469125 969930553139363274650461)
                      ·
                        rfl

theorem cell23_1888933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_1888933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888933 prefixEnd_1888933 := by exact prefixLift 1888933
  have htrace : WordTrace (prefixWord ++ tailWord_1888933) baseStart_1888933 baseEnd_1888933 := by
    simpa [prefixWord, tailWord_1888933, baseEnd_1888933] using wordTrace_append hprefix tailTrace_1888933
  have hstable : (prefixWord ++ tailWord_1888933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888933).length < 2 ^ (prefixWord ++ tailWord_1888933).sum := by decide
  have hdescent : baseEnd_1888933 < baseStart_1888933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888977 : List Nat := [1, 2, 2, 1, 2, 3, 1, 6, 1, 4]
def baseStart_1888977 : Nat := 118140960795 + 1888977 * 2 ^ 59
def prefixEnd_1888977 : Nat := 4983230072969 + 3 ^ 40 * 1888977 * 2
def baseEnd_1888977 : Nat := 323317715429387034166753

theorem tailTrace_1888977 : CollatzResearch.WordTrace tailWord_1888977 prefixEnd_1888977 323317715429387034166753 := by
  unfold tailWord_1888977
  simp only [CollatzResearch.WordTrace]
  refine ⟨68896651277566415432289185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45931100851710943621526123 68896651277566415432289185)
  ·
    refine ⟨51672488458174811574216889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68896651277566415432289185 51672488458174811574216889)
    ·
      refine ⟨38754366343631108680662667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51672488458174811574216889 38754366343631108680662667)
      ·
        refine ⟨58131549515446663020994001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38754366343631108680662667 58131549515446663020994001)
        ·
          refine ⟨43598662136584997265745501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58131549515446663020994001 43598662136584997265745501)
          ·
            refine ⟨16349498301219373974654563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43598662136584997265745501 16349498301219373974654563)
            ·
              refine ⟨24524247451829060961981845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16349498301219373974654563 24524247451829060961981845)
              ·
                refine ⟨1149574099304487232592899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24524247451829060961981845 1149574099304487232592899)
                ·
                  refine ⟨1724361148956730848889349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149574099304487232592899 1724361148956730848889349)
                  ·
                    refine ⟨323317715429387034166753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1724361148956730848889349 323317715429387034166753)
                    ·
                      rfl

theorem cell23_1888977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_1888977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1888977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1888977 prefixEnd_1888977 := by exact prefixLift 1888977
  have htrace : WordTrace (prefixWord ++ tailWord_1888977) baseStart_1888977 baseEnd_1888977 := by
    simpa [prefixWord, tailWord_1888977, baseEnd_1888977] using wordTrace_append hprefix tailTrace_1888977
  have hstable : (prefixWord ++ tailWord_1888977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888977).length < 2 ^ (prefixWord ++ tailWord_1888977).sum := by decide
  have hdescent : baseEnd_1888977 < baseStart_1888977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889050 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_1889050 : Nat := 118140960795 + 1889050 * 2 ^ 59
def prefixEnd_1889050 : Nat := 4983230072969 + 3 ^ 40 * 1889050 * 2
def baseEnd_1889050 : Nat := 323330210125313105629141

theorem tailTrace_1889050 : CollatzResearch.WordTrace tailWord_1889050 prefixEnd_1889050 323330210125313105629141 := by
  unfold tailWord_1889050
  simp only [CollatzResearch.WordTrace]
  refine ⟨17224828451575487224924151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45932875870867965933131069 17224828451575487224924151)
  ·
    refine ⟨25837242677363230837386227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17224828451575487224924151 25837242677363230837386227)
    ·
      refine ⟨38755864016044846256079341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25837242677363230837386227 38755864016044846256079341)
      ·
        refine ⟨14533449006016817346029753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38755864016044846256079341 14533449006016817346029753)
        ·
          refine ⟨10900086754512613009522315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14533449006016817346029753 10900086754512613009522315)
          ·
            refine ⟨16350130131768919514283473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10900086754512613009522315 16350130131768919514283473)
            ·
              refine ⟨12262597598826689635712605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16350130131768919514283473 12262597598826689635712605)
              ·
                refine ⟨4598474099560008613392227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12262597598826689635712605 4598474099560008613392227)
                ·
                  refine ⟨6897711149340012920088341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598474099560008613392227 6897711149340012920088341)
                  ·
                    refine ⟨323330210125313105629141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6897711149340012920088341 323330210125313105629141)
                    ·
                      rfl

theorem cell23_1889050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_1889050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889050 prefixEnd_1889050 := by exact prefixLift 1889050
  have htrace : WordTrace (prefixWord ++ tailWord_1889050) baseStart_1889050 baseEnd_1889050 := by
    simpa [prefixWord, tailWord_1889050, baseEnd_1889050] using wordTrace_append hprefix tailTrace_1889050
  have hstable : (prefixWord ++ tailWord_1889050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889050).length < 2 ^ (prefixWord ++ tailWord_1889050).sum := by decide
  have hdescent : baseEnd_1889050 < baseStart_1889050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889074 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4]
def baseStart_1889074 : Nat := 118140960795 + 1889074 * 2 ^ 59
def prefixEnd_1889074 : Nat := 4983230072969 + 3 ^ 40 * 1889074 * 2
def baseEnd_1889074 : Nat := 970002953911647222987313

theorem tailTrace_1889074 : CollatzResearch.WordTrace tailWord_1889074 prefixEnd_1889074 970002953911647222987313 := by
  unfold tailWord_1889074
  simp only [CollatzResearch.WordTrace]
  refine ⟨17225047289553750249642569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45933459438810000665713517 17225047289553750249642569)
  ·
    refine ⟨12918785467165312687231927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17225047289553750249642569 12918785467165312687231927)
    ·
      refine ⟨19378178200747969030847891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12918785467165312687231927 19378178200747969030847891)
      ·
        refine ⟨29067267301121953546271837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19378178200747969030847891 29067267301121953546271837)
        ·
          refine ⟨10900225237920732579851939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29067267301121953546271837 10900225237920732579851939)
          ·
            refine ⟨16350337856881098869777909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10900225237920732579851939 16350337856881098869777909)
            ·
              refine ⟨1532844174082603019041679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16350337856881098869777909 1532844174082603019041679)
              ·
                refine ⟨2299266261123904528562519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532844174082603019041679 2299266261123904528562519)
                ·
                  refine ⟨3448899391685856792843779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299266261123904528562519 3448899391685856792843779)
                  ·
                    refine ⟨5173349087528785189265669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3448899391685856792843779 5173349087528785189265669)
                    ·
                      refine ⟨970002953911647222987313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5173349087528785189265669 970002953911647222987313)
                      ·
                        rfl

theorem cell23_1889074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_1889074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889074 prefixEnd_1889074 := by exact prefixLift 1889074
  have htrace : WordTrace (prefixWord ++ tailWord_1889074) baseStart_1889074 baseEnd_1889074 := by
    simpa [prefixWord, tailWord_1889074, baseEnd_1889074] using wordTrace_append hprefix tailTrace_1889074
  have hstable : (prefixWord ++ tailWord_1889074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889074).length < 2 ^ (prefixWord ++ tailWord_1889074).sum := by decide
  have hdescent : baseEnd_1889074 < baseStart_1889074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889077 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_1889077 : Nat := 118140960795 + 1889077 * 2 ^ 59
def prefixEnd_1889077 : Nat := 4983230072969 + 3 ^ 40 * 1889077 * 2
def baseEnd_1889077 : Nat := 970004494353610711249799

theorem tailTrace_1889077 : CollatzResearch.WordTrace tailWord_1889077 prefixEnd_1889077 970004494353610711249799 := by
  unfold tailWord_1889077
  simp only [CollatzResearch.WordTrace]
  refine ⟨68900298577204132510929485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45933532384802755007286323 68900298577204132510929485)
  ·
    refine ⟨25837611966451549691598557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68900298577204132510929485 25837611966451549691598557)
    ·
      refine ⟨9689104487419331134349459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25837611966451549691598557 9689104487419331134349459)
      ·
        refine ⟨14533656731128996701524189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9689104487419331134349459 14533656731128996701524189)
        ·
          refine ⟨5450121274173373763071571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14533656731128996701524189 5450121274173373763071571)
          ·
            refine ⟨8175181911260060644607357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5450121274173373763071571 8175181911260060644607357)
            ·
              refine ⟨3065693216722522741727759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8175181911260060644607357 3065693216722522741727759)
              ·
                refine ⟨4598539825083784112591639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065693216722522741727759 4598539825083784112591639)
                ·
                  refine ⟨6897809737625676168887459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598539825083784112591639 6897809737625676168887459)
                  ·
                    refine ⟨10346714606438514253331189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6897809737625676168887459 10346714606438514253331189)
                    ·
                      refine ⟨970004494353610711249799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10346714606438514253331189 970004494353610711249799)
                      ·
                        rfl

theorem cell23_1889077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_1889077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889077 prefixEnd_1889077 := by exact prefixLift 1889077
  have htrace : WordTrace (prefixWord ++ tailWord_1889077) baseStart_1889077 baseEnd_1889077 := by
    simpa [prefixWord, tailWord_1889077, baseEnd_1889077] using wordTrace_append hprefix tailTrace_1889077
  have hstable : (prefixWord ++ tailWord_1889077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889077).length < 2 ^ (prefixWord ++ tailWord_1889077).sum := by decide
  have hdescent : baseEnd_1889077 < baseStart_1889077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889083 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 8]
def baseStart_1889083 : Nat := 118140960795 + 1889083 * 2 ^ 59
def prefixEnd_1889083 : Nat := 4983230072969 + 3 ^ 40 * 1889083 * 2
def baseEnd_1889083 : Nat := 970007575237537687774771

theorem tailTrace_1889083 : CollatzResearch.WordTrace tailWord_1889083 prefixEnd_1889083 970007575237537687774771 := by
  unfold tailWord_1889083
  simp only [CollatzResearch.WordTrace]
  refine ⟨68900517415182395535647903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45933678276788263690431935 68900517415182395535647903)
  ·
    refine ⟨103350776122773593303471855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68900517415182395535647903 103350776122773593303471855)
    ·
      refine ⟨155026164184160389955207783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103350776122773593303471855 155026164184160389955207783)
      ·
        refine ⟨232539246276240584932811675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155026164184160389955207783 232539246276240584932811675)
        ·
          refine ⟨348808869414360877399217513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232539246276240584932811675 348808869414360877399217513)
          ·
            refine ⟨261606652060770658049413135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348808869414360877399217513 261606652060770658049413135)
            ·
              refine ⟨392409978091155987074119703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261606652060770658049413135 392409978091155987074119703)
              ·
                refine ⟨588614967136733980611179555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392409978091155987074119703 588614967136733980611179555)
                ·
                  refine ⟨882922450705100970916769333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588614967136733980611179555 882922450705100970916769333)
                  ·
                    refine ⟨82773979753603216023447125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 882922450705100970916769333 82773979753603216023447125)
                    ·
                      refine ⟨970007575237537687774771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 82773979753603216023447125 970007575237537687774771)
                      ·
                        rfl

theorem cell23_1889083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_1889083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889083 prefixEnd_1889083 := by exact prefixLift 1889083
  have htrace : WordTrace (prefixWord ++ tailWord_1889083) baseStart_1889083 baseEnd_1889083 := by
    simpa [prefixWord, tailWord_1889083, baseEnd_1889083] using wordTrace_append hprefix tailTrace_1889083
  have hstable : (prefixWord ++ tailWord_1889083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889083).length < 2 ^ (prefixWord ++ tailWord_1889083).sum := by decide
  have hdescent : baseEnd_1889083 < baseStart_1889083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889085 : List Nat := [1, 4, 1, 4, 2, 2, 2, 2, 1, 1, 3]
def baseStart_1889085 : Nat := 118140960795 + 1889085 * 2 ^ 59
def prefixEnd_1889085 : Nat := 4983230072969 + 3 ^ 40 * 1889085 * 2
def baseEnd_1889085 : Nat := 970008602198846679949763

theorem tailTrace_1889085 : CollatzResearch.WordTrace tailWord_1889085 prefixEnd_1889085 970008602198846679949763 := by
  unfold tailWord_1889085
  simp only [CollatzResearch.WordTrace]
  refine ⟨68900590361175149877220709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45933726907450099918147139 68900590361175149877220709)
  ·
    refine ⟨12918860692720340601978883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68900590361175149877220709 12918860692720340601978883)
    ·
      refine ⟨19378291039080510902968325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12918860692720340601978883 19378291039080510902968325)
      ·
        refine ⟨3633429569827595794306561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19378291039080510902968325 3633429569827595794306561)
        ·
          refine ⟨2725072177370696845729921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3633429569827595794306561 2725072177370696845729921)
          ·
            refine ⟨2043804133028022634297441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2725072177370696845729921 2043804133028022634297441)
            ·
              refine ⟨1532853099771016975723081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043804133028022634297441 1532853099771016975723081)
              ·
                refine ⟨1149639824828262731792311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532853099771016975723081 1149639824828262731792311)
                ·
                  refine ⟨1724459737242394097688467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149639824828262731792311 1724459737242394097688467)
                  ·
                    refine ⟨2586689605863591146532701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1724459737242394097688467 2586689605863591146532701)
                    ·
                      refine ⟨970008602198846679949763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2586689605863591146532701 970008602198846679949763)
                      ·
                        rfl

theorem cell23_1889085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_1889085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889085 prefixEnd_1889085 := by exact prefixLift 1889085
  have htrace : WordTrace (prefixWord ++ tailWord_1889085) baseStart_1889085 baseEnd_1889085 := by
    simpa [prefixWord, tailWord_1889085, baseEnd_1889085] using wordTrace_append hprefix tailTrace_1889085
  have hstable : (prefixWord ++ tailWord_1889085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889085).length < 2 ^ (prefixWord ++ tailWord_1889085).sum := by decide
  have hdescent : baseEnd_1889085 < baseStart_1889085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889091 : List Nat := [1, 1, 1, 3, 1, 4, 3, 4, 1, 2, 2]
def baseStart_1889091 : Nat := 118140960795 + 1889091 * 2 ^ 59
def prefixEnd_1889091 : Nat := 4983230072969 + 3 ^ 40 * 1889091 * 2
def baseEnd_1889091 : Nat := 970011683082773656474735

theorem tailTrace_1889091 : CollatzResearch.WordTrace tailWord_1889091 prefixEnd_1889091 970011683082773656474735 := by
  unfold tailWord_1889091
  simp only [CollatzResearch.WordTrace]
  refine ⟨68900809199153412901939127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45933872799435608601292751 68900809199153412901939127)
  ·
    refine ⟨103351213798730119352908691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68900809199153412901939127 103351213798730119352908691)
    ·
      refine ⟨155026820698095179029363037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103351213798730119352908691 155026820698095179029363037)
      ·
        refine ⟨58135057761785692136011139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155026820698095179029363037 58135057761785692136011139)
        ·
          refine ⟨87202586642678538204016709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58135057761785692136011139 87202586642678538204016709)
          ·
            refine ⟨16350484995502225913253133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87202586642678538204016709 16350484995502225913253133)
            ·
              refine ⟨6131431873313334717469925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16350484995502225913253133 6131431873313334717469925)
              ·
                refine ⟨1149643476246250259525611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6131431873313334717469925 1149643476246250259525611)
                ·
                  refine ⟨1724465214369375389288417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149643476246250259525611 1724465214369375389288417)
                  ·
                    refine ⟨1293348910777031541966313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1724465214369375389288417 1293348910777031541966313)
                    ·
                      refine ⟨970011683082773656474735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293348910777031541966313 970011683082773656474735)
                      ·
                        rfl

theorem cell23_1889091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 1, 2, 2].length) (baseStart_1889091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889091 prefixEnd_1889091 := by exact prefixLift 1889091
  have htrace : WordTrace (prefixWord ++ tailWord_1889091) baseStart_1889091 baseEnd_1889091 := by
    simpa [prefixWord, tailWord_1889091, baseEnd_1889091] using wordTrace_append hprefix tailTrace_1889091
  have hstable : (prefixWord ++ tailWord_1889091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889091).length < 2 ^ (prefixWord ++ tailWord_1889091).sum := by decide
  have hdescent : baseEnd_1889091 < baseStart_1889091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889120 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1889120 : Nat := 118140960795 + 1889120 * 2 ^ 59
def prefixEnd_1889120 : Nat := 4983230072969 + 3 ^ 40 * 1889120 * 2
def baseEnd_1889120 : Nat := 970026574021754043012101

theorem tailTrace_1889120 : CollatzResearch.WordTrace tailWord_1889120 prefixEnd_1889120 970026574021754043012101 := by
  unfold tailWord_1889120
  simp only [CollatzResearch.WordTrace]
  refine ⟨34450933458024175427372407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45934577944032233903163209 34450933458024175427372407)
  ·
    refine ⟨51676400187036263141058611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34450933458024175427372407 51676400187036263141058611)
    ·
      refine ⟨77514600280554394711587917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51676400187036263141058611 77514600280554394711587917)
      ·
        refine ⟨29067975105207898016845469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77514600280554394711587917 29067975105207898016845469)
        ·
          refine ⟨10900490664452961756317051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29067975105207898016845469 10900490664452961756317051)
          ·
            refine ⟨16350735996679442634475577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10900490664452961756317051 16350735996679442634475577)
            ·
              refine ⟨12263051997509581975856683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16350735996679442634475577 12263051997509581975856683)
              ·
                refine ⟨18394577996264372963785025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12263051997509581975856683 18394577996264372963785025)
                ·
                  refine ⟨13795933497198279722838769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18394577996264372963785025 13795933497198279722838769)
                  ·
                    refine ⟨10346950122898709792129077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13795933497198279722838769 10346950122898709792129077)
                    ·
                      refine ⟨970026574021754043012101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10346950122898709792129077 970026574021754043012101)
                      ·
                        rfl

theorem cell23_1889120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1889120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889120 prefixEnd_1889120 := by exact prefixLift 1889120
  have htrace : WordTrace (prefixWord ++ tailWord_1889120) baseStart_1889120 baseEnd_1889120 := by
    simpa [prefixWord, tailWord_1889120, baseEnd_1889120] using wordTrace_append hprefix tailTrace_1889120
  have hstable : (prefixWord ++ tailWord_1889120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889120).length < 2 ^ (prefixWord ++ tailWord_1889120).sum := by decide
  have hdescent : baseEnd_1889120 < baseStart_1889120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889141 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1889141 : Nat := 118140960795 + 1889141 * 2 ^ 59
def prefixEnd_1889141 : Nat := 4983230072969 + 3 ^ 40 * 1889141 * 2
def baseEnd_1889141 : Nat := 970037357115498460849505

theorem tailTrace_1889141 : CollatzResearch.WordTrace tailWord_1889141 prefixEnd_1889141 970037357115498460849505 := by
  unfold tailWord_1889141
  simp only [CollatzResearch.WordTrace]
  refine ⟨68902632848972271441259277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45935088565981514294172851 68902632848972271441259277)
  ·
    refine ⟨25838487318364601790472229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68902632848972271441259277 25838487318364601790472229)
    ·
      refine ⟨4844716372193362835713543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25838487318364601790472229 4844716372193362835713543)
      ·
        refine ⟨7267074558290044253570315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4844716372193362835713543 7267074558290044253570315)
        ·
          refine ⟨10900611837435066380355473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7267074558290044253570315 10900611837435066380355473)
          ·
            refine ⟨8175458878076299785266605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10900611837435066380355473 8175458878076299785266605)
            ·
              refine ⟨3065797079278612419474977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8175458878076299785266605 3065797079278612419474977)
              ·
                refine ⟨2299347809458959314606233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3065797079278612419474977 2299347809458959314606233)
                ·
                  refine ⟨1724510857094219485954675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2299347809458959314606233 1724510857094219485954675)
                  ·
                    refine ⟨2586766285641329228932013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1724510857094219485954675 2586766285641329228932013)
                    ·
                      refine ⟨970037357115498460849505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2586766285641329228932013 970037357115498460849505)
                      ·
                        rfl

theorem cell23_1889141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1889141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889141 prefixEnd_1889141 := by exact prefixLift 1889141
  have htrace : WordTrace (prefixWord ++ tailWord_1889141) baseStart_1889141 baseEnd_1889141 := by
    simpa [prefixWord, tailWord_1889141, baseEnd_1889141] using wordTrace_append hprefix tailTrace_1889141
  have hstable : (prefixWord ++ tailWord_1889141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889141).length < 2 ^ (prefixWord ++ tailWord_1889141).sum := by decide
  have hdescent : baseEnd_1889141 < baseStart_1889141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889147 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 3, 4, 2]
def baseStart_1889147 : Nat := 118140960795 + 1889147 * 2 ^ 59
def prefixEnd_1889147 : Nat := 4983230072969 + 3 ^ 40 * 1889147 * 2
def baseEnd_1889147 : Nat := 970040437999425437374477

theorem tailTrace_1889147 : CollatzResearch.WordTrace tailWord_1889147 prefixEnd_1889147 970040437999425437374477 := by
  unfold tailWord_1889147
  simp only [CollatzResearch.WordTrace]
  refine ⟨68902851686950534465977695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45935234457967022977318463 68902851686950534465977695)
  ·
    refine ⟨103354277530425801698966543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68902851686950534465977695 103354277530425801698966543)
    ·
      refine ⟨155031416295638702548449815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103354277530425801698966543 155031416295638702548449815)
      ·
        refine ⟨232547124443458053822674723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155031416295638702548449815 232547124443458053822674723)
        ·
          refine ⟨348820686665187080734012085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232547124443458053822674723 348820686665187080734012085)
          ·
            refine ⟨32701939374861288818813633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 348820686665187080734012085 32701939374861288818813633)
            ·
              refine ⟨24526454531145966614110225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32701939374861288818813633 24526454531145966614110225)
              ·
                refine ⟨18394840898359474960582669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24526454531145966614110225 18394840898359474960582669)
                ·
                  refine ⟨6898065336884803110218501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18394840898359474960582669 6898065336884803110218501)
                  ·
                    refine ⟨1293387250665900583165969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6898065336884803110218501 1293387250665900583165969)
                    ·
                      refine ⟨970040437999425437374477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293387250665900583165969 970040437999425437374477)
                      ·
                        rfl

theorem cell23_1889147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 4, 2].length) (baseStart_1889147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889147 prefixEnd_1889147 := by exact prefixLift 1889147
  have htrace : WordTrace (prefixWord ++ tailWord_1889147) baseStart_1889147 baseEnd_1889147 := by
    simpa [prefixWord, tailWord_1889147, baseEnd_1889147] using wordTrace_append hprefix tailTrace_1889147
  have hstable : (prefixWord ++ tailWord_1889147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889147).length < 2 ^ (prefixWord ++ tailWord_1889147).sum := by decide
  have hdescent : baseEnd_1889147 < baseStart_1889147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889164 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 1, 4, 2]
def baseStart_1889164 : Nat := 118140960795 + 1889164 * 2 ^ 59
def prefixEnd_1889164 : Nat := 4983230072969 + 3 ^ 40 * 1889164 * 2
def baseEnd_1889164 : Nat := 970049167170551870861899

theorem tailTrace_1889164 : CollatzResearch.WordTrace tailWord_1889164 prefixEnd_1889164 970049167170551870861899 := by
  unfold tailWord_1889164
  simp only [CollatzResearch.WordTrace]
  refine ⟨34451735863944473184673273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45935647818592630912897697 34451735863944473184673273)
  ·
    refine ⟨25838801897958354888504955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34451735863944473184673273 25838801897958354888504955)
    ·
      refine ⟨38758202846937532332757433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25838801897958354888504955 38758202846937532332757433)
      ·
        refine ⟨29068652135203149249568075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38758202846937532332757433 29068652135203149249568075)
        ·
          refine ⟨43602978202804723874352113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29068652135203149249568075 43602978202804723874352113)
          ·
            refine ⟨32702233652103542905764085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43602978202804723874352113 32702233652103542905764085)
            ·
              refine ⟨3065834404884707147415383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32702233652103542905764085 3065834404884707147415383)
              ·
                refine ⟨4598751607327060721123075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065834404884707147415383 4598751607327060721123075)
                ·
                  refine ⟨6898127410990591081684613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598751607327060721123075 6898127410990591081684613)
                  ·
                    refine ⟨1293398889560735827815865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6898127410990591081684613 1293398889560735827815865)
                    ·
                      refine ⟨970049167170551870861899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293398889560735827815865 970049167170551870861899)
                      ·
                        rfl

theorem cell23_1889164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_1889164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889164 prefixEnd_1889164 := by exact prefixLift 1889164
  have htrace : WordTrace (prefixWord ++ tailWord_1889164) baseStart_1889164 baseEnd_1889164 := by
    simpa [prefixWord, tailWord_1889164, baseEnd_1889164] using wordTrace_append hprefix tailTrace_1889164
  have hstable : (prefixWord ++ tailWord_1889164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889164).length < 2 ^ (prefixWord ++ tailWord_1889164).sum := by decide
  have hdescent : baseEnd_1889164 < baseStart_1889164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889234 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1889234 : Nat := 118140960795 + 1889234 * 2 ^ 59
def prefixEnd_1889234 : Nat := 4983230072969 + 3 ^ 40 * 1889234 * 2
def baseEnd_1889234 : Nat := 323361703605455532328859

theorem tailTrace_1889234 : CollatzResearch.WordTrace tailWord_1889234 prefixEnd_1889234 323361703605455532328859 := by
  unfold tailWord_1889234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17226506209408837081098689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45937349891756898882929837 17226506209408837081098689)
  ·
    refine ⟨12919879657056627810824017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17226506209408837081098689 12919879657056627810824017)
    ·
      refine ⟨9689909742792470858118013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12919879657056627810824017 9689909742792470858118013)
      ·
        refine ⟨3633716153547176571794255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9689909742792470858118013 3633716153547176571794255)
        ·
          refine ⟨5450574230320764857691383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3633716153547176571794255 5450574230320764857691383)
          ·
            refine ⟨8175861345481147286537075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5450574230320764857691383 8175861345481147286537075)
            ·
              refine ⟨12263792018221720929805613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8175861345481147286537075 12263792018221720929805613)
              ·
                refine ⟨4598922006833145348677105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12263792018221720929805613 4598922006833145348677105)
                ·
                  refine ⟨3449191505124859011507829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4598922006833145348677105 3449191505124859011507829)
                  ·
                    refine ⟨323361703605455532328859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3449191505124859011507829 323361703605455532328859)
                    ·
                      rfl

theorem cell23_1889234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1889234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889234 prefixEnd_1889234 := by exact prefixLift 1889234
  have htrace : WordTrace (prefixWord ++ tailWord_1889234) baseStart_1889234 baseEnd_1889234 := by
    simpa [prefixWord, tailWord_1889234, baseEnd_1889234] using wordTrace_append hprefix tailTrace_1889234
  have hstable : (prefixWord ++ tailWord_1889234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889234).length < 2 ^ (prefixWord ++ tailWord_1889234).sum := by decide
  have hdescent : baseEnd_1889234 < baseStart_1889234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889291 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 2, 2, 3]
def baseStart_1889291 : Nat := 118140960795 + 1889291 * 2 ^ 59
def prefixEnd_1889291 : Nat := 4983230072969 + 3 ^ 40 * 1889291 * 2
def baseEnd_1889291 : Nat := 970114379213672873973815

theorem tailTrace_1889291 : CollatzResearch.WordTrace tailWord_1889291 prefixEnd_1889291 970114379213672873973815 := by
  unfold tailWord_1889291
  simp only [CollatzResearch.WordTrace]
  refine ⟨68908103798428847059219727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45938735865619231372813151 68908103798428847059219727)
  ·
    refine ⟨103362155697643270588829591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68908103798428847059219727 103362155697643270588829591)
    ·
      refine ⟨155043233546464905883244387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103362155697643270588829591 155043233546464905883244387)
      ·
        refine ⟨232564850319697358824866581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155043233546464905883244387 232564850319697358824866581)
        ·
          refine ⟨10901477358735813694915621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 232564850319697358824866581 10901477358735813694915621)
          ·
            refine ⟨2044027004762965067796679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10901477358735813694915621 2044027004762965067796679)
            ·
              refine ⟨3066040507144447601695019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044027004762965067796679 3066040507144447601695019)
              ·
                refine ⟨4599060760716671402542529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066040507144447601695019 4599060760716671402542529)
                ·
                  refine ⟨3449295570537503551906897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4599060760716671402542529 3449295570537503551906897)
                  ·
                    refine ⟨2586971677903127663930173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3449295570537503551906897 2586971677903127663930173)
                    ·
                      refine ⟨970114379213672873973815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2586971677903127663930173 970114379213672873973815)
                      ·
                        rfl

theorem cell23_1889291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 2, 3].length) (baseStart_1889291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889291 prefixEnd_1889291 := by exact prefixLift 1889291
  have htrace : WordTrace (prefixWord ++ tailWord_1889291) baseStart_1889291 baseEnd_1889291 := by
    simpa [prefixWord, tailWord_1889291, baseEnd_1889291] using wordTrace_append hprefix tailTrace_1889291
  have hstable : (prefixWord ++ tailWord_1889291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889291).length < 2 ^ (prefixWord ++ tailWord_1889291).sum := by decide
  have hdescent : baseEnd_1889291 < baseStart_1889291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889341 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_1889341 : Nat := 118140960795 + 1889341 * 2 ^ 59
def prefixEnd_1889341 : Nat := 4983230072969 + 3 ^ 40 * 1889341 * 2
def baseEnd_1889341 : Nat := 323380017748799226116195

theorem tailTrace_1889341 : CollatzResearch.WordTrace tailWord_1889341 prefixEnd_1889341 323380017748799226116195 := by
  unfold tailWord_1889341
  simp only [CollatzResearch.WordTrace]
  refine ⟨68909927448247705598539877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45939951632165137065693251 68909927448247705598539877)
  ·
    refine ⟨12920611396546444799726227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68909927448247705598539877 12920611396546444799726227)
    ·
      refine ⟨19380917094819667199589341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12920611396546444799726227 19380917094819667199589341)
      ·
        refine ⟨7267843910557375199846003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19380917094819667199589341 7267843910557375199846003)
        ·
          refine ⟨10901765865836062799769005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7267843910557375199846003 10901765865836062799769005)
          ·
            refine ⟨4088162199688523549913377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10901765865836062799769005 4088162199688523549913377)
            ·
              refine ⟨3066121649766392662435033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4088162199688523549913377 3066121649766392662435033)
              ·
                refine ⟨2299591237324794496826275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066121649766392662435033 2299591237324794496826275)
                ·
                  refine ⟨3449386855987191745239413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299591237324794496826275 3449386855987191745239413)
                  ·
                    refine ⟨323380017748799226116195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3449386855987191745239413 323380017748799226116195)
                    ·
                      rfl

theorem cell23_1889341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_1889341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889341 prefixEnd_1889341 := by exact prefixLift 1889341
  have htrace : WordTrace (prefixWord ++ tailWord_1889341) baseStart_1889341 baseEnd_1889341 := by
    simpa [prefixWord, tailWord_1889341, baseEnd_1889341] using wordTrace_append hprefix tailTrace_1889341
  have hstable : (prefixWord ++ tailWord_1889341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889341).length < 2 ^ (prefixWord ++ tailWord_1889341).sum := by decide
  have hdescent : baseEnd_1889341 < baseStart_1889341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889344 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 2, 6, 2]
def baseStart_1889344 : Nat := 118140960795 + 1889344 * 2 ^ 59
def prefixEnd_1889344 : Nat := 4983230072969 + 3 ^ 40 * 1889344 * 2
def baseEnd_1889344 : Nat := 970141593688361166611071

theorem tailTrace_1889344 : CollatzResearch.WordTrace tailWord_1889344 prefixEnd_1889344 970141593688361166611071 := by
  unfold tailWord_1889344
  simp only [CollatzResearch.WordTrace]
  refine ⟨34455018433618418555449543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45940024578157891407266057 34455018433618418555449543)
  ·
    refine ⟨51682527650427627833174315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34455018433618418555449543 51682527650427627833174315)
    ·
      refine ⟨77523791475641441749761473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51682527650427627833174315 77523791475641441749761473)
      ·
        refine ⟨58142843606731081312321105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77523791475641441749761473 58142843606731081312321105)
        ·
          refine ⟨43607132705048310984240829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58142843606731081312321105 43607132705048310984240829)
          ·
            refine ⟨16352674764393116619090311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43607132705048310984240829 16352674764393116619090311)
            ·
              refine ⟨24529012146589674928635467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16352674764393116619090311 24529012146589674928635467)
              ·
                refine ⟨36793518219884512392953201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24529012146589674928635467 36793518219884512392953201)
                ·
                  refine ⟨27595138664913384294714901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36793518219884512392953201 27595138664913384294714901)
                  ·
                    refine ⟨1293522124917814888814761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27595138664913384294714901 1293522124917814888814761)
                    ·
                      refine ⟨970141593688361166611071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293522124917814888814761 970141593688361166611071)
                      ·
                        rfl

theorem cell23_1889344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 6, 2].length) (baseStart_1889344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889344 prefixEnd_1889344 := by exact prefixLift 1889344
  have htrace : WordTrace (prefixWord ++ tailWord_1889344) baseStart_1889344 baseEnd_1889344 := by
    simpa [prefixWord, tailWord_1889344, baseEnd_1889344] using wordTrace_append hprefix tailTrace_1889344
  have hstable : (prefixWord ++ tailWord_1889344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889344).length < 2 ^ (prefixWord ++ tailWord_1889344).sum := by decide
  have hdescent : baseEnd_1889344 < baseStart_1889344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889347 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 5]
def baseStart_1889347 : Nat := 118140960795 + 1889347 * 2 ^ 59
def prefixEnd_1889347 : Nat := 4983230072969 + 3 ^ 40 * 1889347 * 2
def baseEnd_1889347 : Nat := 970143134130324654873557

theorem tailTrace_1889347 : CollatzResearch.WordTrace tailWord_1889347 prefixEnd_1889347 970143134130324654873557 := by
  unfold tailWord_1889347
  simp only [CollatzResearch.WordTrace]
  refine ⟨68910146286225968623258295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45940097524150645748838863 68910146286225968623258295)
  ·
    refine ⟨103365219429338952934887443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68910146286225968623258295 103365219429338952934887443)
    ·
      refine ⟨155047829144008429402331165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103365219429338952934887443 155047829144008429402331165)
      ·
        refine ⟨58142935929003161025874187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155047829144008429402331165 58142935929003161025874187)
        ·
          refine ⟨87214403893504741538811281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58142935929003161025874187 87214403893504741538811281)
          ·
            refine ⟨65410802920128556154108461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87214403893504741538811281 65410802920128556154108461)
            ·
              refine ⟨24529051095048208557790673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65410802920128556154108461 24529051095048208557790673)
              ·
                refine ⟨18396788321286156418343005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24529051095048208557790673 18396788321286156418343005)
                ·
                  refine ⟨6898795620482308656878627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18396788321286156418343005 6898795620482308656878627)
                  ·
                    refine ⟨10348193430723462985317941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6898795620482308656878627 10348193430723462985317941)
                    ·
                      refine ⟨970143134130324654873557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10348193430723462985317941 970143134130324654873557)
                      ·
                        rfl

theorem cell23_1889347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_1889347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889347 prefixEnd_1889347 := by exact prefixLift 1889347
  have htrace : WordTrace (prefixWord ++ tailWord_1889347) baseStart_1889347 baseEnd_1889347 := by
    simpa [prefixWord, tailWord_1889347, baseEnd_1889347] using wordTrace_append hprefix tailTrace_1889347
  have hstable : (prefixWord ++ tailWord_1889347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889347).length < 2 ^ (prefixWord ++ tailWord_1889347).sum := by decide
  have hdescent : baseEnd_1889347 < baseStart_1889347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889354 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 4, 4]
def baseStart_1889354 : Nat := 118140960795 + 1889354 * 2 ^ 59
def prefixEnd_1889354 : Nat := 4983230072969 + 3 ^ 40 * 1889354 * 2
def baseEnd_1889354 : Nat := 323382242831635375828675

theorem tailTrace_1889354 : CollatzResearch.WordTrace tailWord_1889354 prefixEnd_1889354 323382242831635375828675 := by
  unfold tailWord_1889354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17227600399300152204690779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45940267731467072545842077 17227600399300152204690779)
  ·
    refine ⟨25841400598950228307036169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17227600399300152204690779 25841400598950228307036169)
    ·
      refine ⟨19381050449212671230277127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25841400598950228307036169 19381050449212671230277127)
      ·
        refine ⟨29071575673819006845415691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19381050449212671230277127 29071575673819006845415691)
        ·
          refine ⟨43607363510728510268123537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29071575673819006845415691 43607363510728510268123537)
          ·
            refine ⟨32705522633046382701092653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43607363510728510268123537 32705522633046382701092653)
            ·
              refine ⟨12264570987392393512909745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32705522633046382701092653 12264570987392393512909745)
              ·
                refine ⟨9198428240544295134682309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12264570987392393512909745 9198428240544295134682309)
                ·
                  refine ⟨1724705295102055337752933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9198428240544295134682309 1724705295102055337752933)
                  ·
                    refine ⟨323382242831635375828675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1724705295102055337752933 323382242831635375828675)
                    ·
                      rfl

theorem cell23_1889354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_1889354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889354 prefixEnd_1889354 := by exact prefixLift 1889354
  have htrace : WordTrace (prefixWord ++ tailWord_1889354) baseStart_1889354 baseEnd_1889354 := by
    simpa [prefixWord, tailWord_1889354, baseEnd_1889354] using wordTrace_append hprefix tailTrace_1889354
  have hstable : (prefixWord ++ tailWord_1889354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889354).length < 2 ^ (prefixWord ++ tailWord_1889354).sum := by decide
  have hdescent : baseEnd_1889354 < baseStart_1889354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889361 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 5, 2, 2]
def baseStart_1889361 : Nat := 118140960795 + 1889361 * 2 ^ 59
def prefixEnd_1889361 : Nat := 4983230072969 + 3 ^ 40 * 1889361 * 2
def baseEnd_1889361 : Nat := 970150322859487600098493

theorem tailTrace_1889361 : CollatzResearch.WordTrace tailWord_1889361 prefixEnd_1889361 970150322859487600098493 := by
  unfold tailWord_1889361
  simp only [CollatzResearch.WordTrace]
  refine ⟨68910656908175249014267937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45940437938783499342845291 68910656908175249014267937)
  ·
    refine ⟨51682992681131436760700953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68910656908175249014267937 51682992681131436760700953)
    ·
      refine ⟨38762244510848577570525715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51682992681131436760700953 38762244510848577570525715)
      ·
        refine ⟨58143366766272866355788573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38762244510848577570525715 58143366766272866355788573)
        ·
          refine ⟨21803762537352324883420715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58143366766272866355788573 21803762537352324883420715)
          ·
            refine ⟨32705643806028487325131073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21803762537352324883420715 32705643806028487325131073)
            ·
              refine ⟨24529232854521365493848305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32705643806028487325131073 24529232854521365493848305)
              ·
                refine ⟨18396924640891024120386229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24529232854521365493848305 18396924640891024120386229)
                ·
                  refine ⟨1724711685083533511286209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18396924640891024120386229 1724711685083533511286209)
                  ·
                    refine ⟨1293533763812650133464657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1724711685083533511286209 1293533763812650133464657)
                    ·
                      refine ⟨970150322859487600098493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293533763812650133464657 970150322859487600098493)
                      ·
                        rfl

theorem cell23_1889361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 2, 2].length) (baseStart_1889361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889361 prefixEnd_1889361 := by exact prefixLift 1889361
  have htrace : WordTrace (prefixWord ++ tailWord_1889361) baseStart_1889361 baseEnd_1889361 := by
    simpa [prefixWord, tailWord_1889361, baseEnd_1889361] using wordTrace_append hprefix tailTrace_1889361
  have hstable : (prefixWord ++ tailWord_1889361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889361).length < 2 ^ (prefixWord ++ tailWord_1889361).sum := by decide
  have hdescent : baseEnd_1889361 < baseStart_1889361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889364 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_1889364 : Nat := 118140960795 + 1889364 * 2 ^ 59
def prefixEnd_1889364 : Nat := 4983230072969 + 3 ^ 40 * 1889364 * 2
def baseEnd_1889364 : Nat := 970151863301451088360979

theorem tailTrace_1889364 : CollatzResearch.WordTrace tailWord_1889364 prefixEnd_1889364 970151863301451088360979 := by
  unfold tailWord_1889364
  simp only [CollatzResearch.WordTrace]
  refine ⟨34455383163582190263313573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45940510884776253684418097 34455383163582190263313573)
  ·
    refine ⟨6460384343171660674371295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34455383163582190263313573 6460384343171660674371295)
    ·
      refine ⟨9690576514757491011556943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6460384343171660674371295 9690576514757491011556943)
      ·
        refine ⟨14535864772136236517335415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9690576514757491011556943 14535864772136236517335415)
        ·
          refine ⟨21803797158204354776003123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14535864772136236517335415 21803797158204354776003123)
          ·
            refine ⟨32705695737306532164004685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21803797158204354776003123 32705695737306532164004685)
            ·
              refine ⟨12264635901489949561501757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32705695737306532164004685 12264635901489949561501757)
              ·
                refine ⟨4599238463058731085563159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12264635901489949561501757 4599238463058731085563159)
                ·
                  refine ⟨6898857694588096628344739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4599238463058731085563159 6898857694588096628344739)
                  ·
                    refine ⟨10348286541882144942517109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6898857694588096628344739 10348286541882144942517109)
                    ·
                      refine ⟨970151863301451088360979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10348286541882144942517109 970151863301451088360979)
                      ·
                        rfl

theorem cell23_1889364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_1889364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889364 prefixEnd_1889364 := by exact prefixLift 1889364
  have htrace : WordTrace (prefixWord ++ tailWord_1889364) baseStart_1889364 baseEnd_1889364 := by
    simpa [prefixWord, tailWord_1889364, baseEnd_1889364] using wordTrace_append hprefix tailTrace_1889364
  have hstable : (prefixWord ++ tailWord_1889364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889364).length < 2 ^ (prefixWord ++ tailWord_1889364).sum := by decide
  have hdescent : baseEnd_1889364 < baseStart_1889364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889444 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_1889444 : Nat := 118140960795 + 1889444 * 2 ^ 59
def prefixEnd_1889444 : Nat := 4983230072969 + 3 ^ 40 * 1889444 * 2
def baseEnd_1889444 : Nat := 323397647251270258453537

theorem tailTrace_1889444 : CollatzResearch.WordTrace tailWord_1889444 prefixEnd_1889444 323397647251270258453537 := by
  unfold tailWord_1889444
  simp only [CollatzResearch.WordTrace]
  refine ⟨34456842083437277094769693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45942456111249702793026257 34456842083437277094769693)
  ·
    refine ⟨12921315781288978910538635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34456842083437277094769693 12921315781288978910538635)
    ·
      refine ⟨19381973671933468365807953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12921315781288978910538635 19381973671933468365807953)
      ·
        refine ⟨14536480253950101274355965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19381973671933468365807953 14536480253950101274355965)
        ·
          refine ⟨5451180095231287977883487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14536480253950101274355965 5451180095231287977883487)
          ·
            refine ⟨8176770142846931966825231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5451180095231287977883487 8176770142846931966825231)
            ·
              refine ⟨12265155214270397950237847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8176770142846931966825231 12265155214270397950237847)
              ·
                refine ⟨18397732821405596925356771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12265155214270397950237847 18397732821405596925356771)
                ·
                  refine ⟨27596599232108395388035157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18397732821405596925356771 27596599232108395388035157)
                  ·
                    refine ⟨323397647251270258453537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27596599232108395388035157 323397647251270258453537)
                    ·
                      rfl

theorem cell23_1889444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_1889444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889444 prefixEnd_1889444 := by exact prefixLift 1889444
  have htrace : WordTrace (prefixWord ++ tailWord_1889444) baseStart_1889444 baseEnd_1889444 := by
    simpa [prefixWord, tailWord_1889444, baseEnd_1889444] using wordTrace_append hprefix tailTrace_1889444
  have hstable : (prefixWord ++ tailWord_1889444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889444).length < 2 ^ (prefixWord ++ tailWord_1889444).sum := by decide
  have hdescent : baseEnd_1889444 < baseStart_1889444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889468 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 1, 4, 2]
def baseStart_1889468 : Nat := 118140960795 + 1889468 * 2 ^ 59
def prefixEnd_1889468 : Nat := 4983230072969 + 3 ^ 40 * 1889468 * 2
def baseEnd_1889468 : Nat := 970205265289518681460501

theorem tailTrace_1889468 : CollatzResearch.WordTrace tailWord_1889468 prefixEnd_1889468 970205265289518681460501 := by
  unfold tailWord_1889468
  simp only [CollatzResearch.WordTrace]
  refine ⟨34457279759393803144206529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45943039679191737525608705 34457279759393803144206529)
  ·
    refine ⟨25842959819545352358154897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34457279759393803144206529 25842959819545352358154897)
    ·
      refine ⟨19382219864659014268616173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25842959819545352358154897 19382219864659014268616173)
      ·
        refine ⟨7268332449247130350731065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19382219864659014268616173 7268332449247130350731065)
        ·
          refine ⟨5451249336935347763048299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7268332449247130350731065 5451249336935347763048299)
          ·
            refine ⟨8176874005403021644572449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5451249336935347763048299 8176874005403021644572449)
            ·
              refine ⟨6132655504052266233429337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8176874005403021644572449 6132655504052266233429337)
              ·
                refine ⟨4599491628039199675072003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6132655504052266233429337 4599491628039199675072003)
                ·
                  refine ⟨6899237442058799512608005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4599491628039199675072003 6899237442058799512608005)
                  ·
                    refine ⟨1293607020386024908614001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6899237442058799512608005 1293607020386024908614001)
                    ·
                      refine ⟨970205265289518681460501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293607020386024908614001 970205265289518681460501)
                      ·
                        rfl

theorem cell23_1889468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_1889468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889468 prefixEnd_1889468 := by exact prefixLift 1889468
  have htrace : WordTrace (prefixWord ++ tailWord_1889468) baseStart_1889468 baseEnd_1889468 := by
    simpa [prefixWord, tailWord_1889468, baseEnd_1889468] using wordTrace_append hprefix tailTrace_1889468
  have hstable : (prefixWord ++ tailWord_1889468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889468).length < 2 ^ (prefixWord ++ tailWord_1889468).sum := by decide
  have hdescent : baseEnd_1889468 < baseStart_1889468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889472 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 1, 3, 2]
def baseStart_1889472 : Nat := 118140960795 + 1889472 * 2 ^ 59
def prefixEnd_1889472 : Nat := 4983230072969 + 3 ^ 40 * 1889472 * 2
def baseEnd_1889472 : Nat := 970207319212136665810483

theorem tailTrace_1889472 : CollatzResearch.WordTrace tailWord_1889472 prefixEnd_1889472 970207319212136665810483 := by
  unfold tailWord_1889472
  simp only [CollatzResearch.WordTrace]
  refine ⟨34457352705386557485779335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45943136940515409981039113 34457352705386557485779335)
  ·
    refine ⟨51686029058079836228669003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34457352705386557485779335 51686029058079836228669003)
    ·
      refine ⟨77529043587119754343003505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51686029058079836228669003 77529043587119754343003505)
      ·
        refine ⟨58146782690339815757252629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77529043587119754343003505 58146782690339815757252629)
        ·
          refine ⟨2725630438609678863621217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58146782690339815757252629 2725630438609678863621217)
          ·
            refine ⟨2044222828957259147715913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2725630438609678863621217 2044222828957259147715913)
            ·
              refine ⟨1533167121717944360786935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044222828957259147715913 1533167121717944360786935)
              ·
                refine ⟨2299750682576916541180403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533167121717944360786935 2299750682576916541180403)
                ·
                  refine ⟨3449626023865374811770605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299750682576916541180403 3449626023865374811770605)
                  ·
                    refine ⟨1293609758949515554413977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3449626023865374811770605 1293609758949515554413977)
                    ·
                      refine ⟨970207319212136665810483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293609758949515554413977 970207319212136665810483)
                      ·
                        rfl

theorem cell23_1889472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 3, 2].length) (baseStart_1889472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889472 prefixEnd_1889472 := by exact prefixLift 1889472
  have htrace : WordTrace (prefixWord ++ tailWord_1889472) baseStart_1889472 baseEnd_1889472 := by
    simpa [prefixWord, tailWord_1889472, baseEnd_1889472] using wordTrace_append hprefix tailTrace_1889472
  have hstable : (prefixWord ++ tailWord_1889472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889472).length < 2 ^ (prefixWord ++ tailWord_1889472).sum := by decide
  have hdescent : baseEnd_1889472 < baseStart_1889472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889504 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 1, 7]
def baseStart_1889504 : Nat := 118140960795 + 1889504 * 2 ^ 59
def prefixEnd_1889504 : Nat := 4983230072969 + 3 ^ 40 * 1889504 * 2
def baseEnd_1889504 : Nat := 323407916864360180203445

theorem tailTrace_1889504 : CollatzResearch.WordTrace tailWord_1889504 prefixEnd_1889504 323407916864360180203445 := by
  unfold tailWord_1889504
  simp only [CollatzResearch.WordTrace]
  refine ⟨34457936273328592218361783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45943915031104789624482377 34457936273328592218361783)
  ·
    refine ⟨51686904409992888327542675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34457936273328592218361783 51686904409992888327542675)
    ·
      refine ⟨77530356614989332491314013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51686904409992888327542675 77530356614989332491314013)
      ·
        refine ⟨29073883730620999684242755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77530356614989332491314013 29073883730620999684242755)
        ·
          refine ⟨43610825595931499526364133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29073883730620999684242755 43610825595931499526364133)
          ·
            refine ⟨8177029799237156161193275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43610825595931499526364133 8177029799237156161193275)
            ·
              refine ⟨12265544698855734241789913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8177029799237156161193275 12265544698855734241789913)
              ·
                refine ⟨9199158524141800681342435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12265544698855734241789913 9199158524141800681342435)
                ·
                  refine ⟨13798737786212701022013653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9199158524141800681342435 13798737786212701022013653)
                  ·
                    refine ⟨323407916864360180203445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13798737786212701022013653 323407916864360180203445)
                    ·
                      rfl

theorem cell23_1889504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_1889504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889504 prefixEnd_1889504 := by exact prefixLift 1889504
  have htrace : WordTrace (prefixWord ++ tailWord_1889504) baseStart_1889504 baseEnd_1889504 := by
    simpa [prefixWord, tailWord_1889504, baseEnd_1889504] using wordTrace_append hprefix tailTrace_1889504
  have hstable : (prefixWord ++ tailWord_1889504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889504).length < 2 ^ (prefixWord ++ tailWord_1889504).sum := by decide
  have hdescent : baseEnd_1889504 < baseStart_1889504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889541 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_1889541 : Nat := 118140960795 + 1889541 * 2 ^ 59
def prefixEnd_1889541 : Nat := 4983230072969 + 3 ^ 40 * 1889541 * 2
def baseEnd_1889541 : Nat := 970242749377296895847665

theorem tailTrace_1889541 : CollatzResearch.WordTrace tailWord_1889541 prefixEnd_1889541 970242749377296895847665 := by
  unfold tailWord_1889541
  simp only [CollatzResearch.WordTrace]
  refine ⟨68917222047523139755820477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45944814698348759837213651 68917222047523139755820477)
  ·
    refine ⟨25843958267821177408432679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68917222047523139755820477 25843958267821177408432679)
    ·
      refine ⟨38765937401731766112649019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25843958267821177408432679 38765937401731766112649019)
      ·
        refine ⟨58148906102597649168973529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38765937401731766112649019 58148906102597649168973529)
        ·
          refine ⟨43611679576948236876730147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58148906102597649168973529 43611679576948236876730147)
          ·
            refine ⟨65417519365422355315095221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43611679576948236876730147 65417519365422355315095221)
            ·
              refine ⟨6132892440508345810790177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65417519365422355315095221 6132892440508345810790177)
              ·
                refine ⟨4599669330381259358092633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6132892440508345810790177 4599669330381259358092633)
                ·
                  refine ⟨3449751997785944518569475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4599669330381259358092633 3449751997785944518569475)
                  ·
                    refine ⟨5174627996678916777854213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3449751997785944518569475 5174627996678916777854213)
                    ·
                      refine ⟨970242749377296895847665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5174627996678916777854213 970242749377296895847665)
                      ·
                        rfl

theorem cell23_1889541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_1889541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889541 prefixEnd_1889541 := by exact prefixLift 1889541
  have htrace : WordTrace (prefixWord ++ tailWord_1889541) baseStart_1889541 baseEnd_1889541 := by
    simpa [prefixWord, tailWord_1889541, baseEnd_1889541] using wordTrace_append hprefix tailTrace_1889541
  have hstable : (prefixWord ++ tailWord_1889541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889541).length < 2 ^ (prefixWord ++ tailWord_1889541).sum := by decide
  have hdescent : baseEnd_1889541 < baseStart_1889541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889598 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_1889598 : Nat := 118140960795 + 1889598 * 2 ^ 59
def prefixEnd_1889598 : Nat := 4983230072969 + 3 ^ 40 * 1889598 * 2
def baseEnd_1889598 : Nat := 107808001974955908092767

theorem tailTrace_1889598 : CollatzResearch.WordTrace tailWord_1889598 prefixEnd_1889598 107808001974955908092767 := by
  unfold tailWord_1889598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8614912626039579811330681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45946200672211092327096965 8614912626039579811330681)
  ·
    refine ⟨6461184469529684858498011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8614912626039579811330681 6461184469529684858498011)
    ·
      refine ⟨9691776704294527287747017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6461184469529684858498011 9691776704294527287747017)
      ·
        refine ⟨7268832528220895465810263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9691776704294527287747017 7268832528220895465810263)
        ·
          refine ⟨10903248792331343198715395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7268832528220895465810263 10903248792331343198715395)
          ·
            refine ⟨16354873188497014798073093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10903248792331343198715395 16354873188497014798073093)
            ·
              refine ⟨3066538722843190274638705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16354873188497014798073093 3066538722843190274638705)
              ·
                refine ⟨2299904042132392705979029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066538722843190274638705 2299904042132392705979029)
                ·
                  refine ⟨107808001974955908092767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2299904042132392705979029 107808001974955908092767)
                  ·
                    rfl

theorem cell23_1889598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_1889598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889598 prefixEnd_1889598 := by exact prefixLift 1889598
  have htrace : WordTrace (prefixWord ++ tailWord_1889598) baseStart_1889598 baseEnd_1889598 := by
    simpa [prefixWord, tailWord_1889598, baseEnd_1889598] using wordTrace_append hprefix tailTrace_1889598
  have hstable : (prefixWord ++ tailWord_1889598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889598).length < 2 ^ (prefixWord ++ tailWord_1889598).sum := by decide
  have hdescent : baseEnd_1889598 < baseStart_1889598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889608 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_1889608 : Nat := 118140960795 + 1889608 * 2 ^ 59
def prefixEnd_1889608 : Nat := 4983230072969 + 3 ^ 40 * 1889608 * 2
def baseEnd_1889608 : Nat := 970277152581148133709857

theorem tailTrace_1889608 : CollatzResearch.WordTrace tailWord_1889608 prefixEnd_1889608 970277152581148133709857 := by
  unfold tailWord_1889608
  simp only [CollatzResearch.WordTrace]
  refine ⟨34459832869140205099254739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45946443825520273465672985 34459832869140205099254739)
  ·
    refine ⟨51689749303710307648882109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34459832869140205099254739 51689749303710307648882109)
    ·
      refine ⟨19383655988891365368330791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51689749303710307648882109 19383655988891365368330791)
      ·
        refine ⟨29075483983337048052496187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19383655988891365368330791 29075483983337048052496187)
        ·
          refine ⟨43613225975005572078744281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29075483983337048052496187 43613225975005572078744281)
          ·
            refine ⟨32709919481254179059058211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43613225975005572078744281 32709919481254179059058211)
            ·
              refine ⟨49064879221881268588587317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32709919481254179059058211 49064879221881268588587317)
              ·
                refine ⟨4599832427051368930180061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49064879221881268588587317 4599832427051368930180061)
                ·
                  refine ⟨1724937160144263348817523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4599832427051368930180061 1724937160144263348817523)
                  ·
                    refine ⟨2587405740216395023226285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1724937160144263348817523 2587405740216395023226285)
                    ·
                      refine ⟨970277152581148133709857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2587405740216395023226285 970277152581148133709857)
                      ·
                        rfl

theorem cell23_1889608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_1889608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889608 prefixEnd_1889608 := by exact prefixLift 1889608
  have htrace : WordTrace (prefixWord ++ tailWord_1889608) baseStart_1889608 baseEnd_1889608 := by
    simpa [prefixWord, tailWord_1889608, baseEnd_1889608] using wordTrace_append hprefix tailTrace_1889608
  have hstable : (prefixWord ++ tailWord_1889608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889608).length < 2 ^ (prefixWord ++ tailWord_1889608).sum := by decide
  have hdescent : baseEnd_1889608 < baseStart_1889608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889618 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_1889618 : Nat := 118140960795 + 1889618 * 2 ^ 59
def prefixEnd_1889618 : Nat := 4983230072969 + 3 ^ 40 * 1889618 * 2
def baseEnd_1889618 : Nat := 970282287387693094584811

theorem tailTrace_1889618 : CollatzResearch.WordTrace tailWord_1889618 prefixEnd_1889618 970282287387693094584811 := by
  unfold tailWord_1889618
  simp only [CollatzResearch.WordTrace]
  refine ⟨17230007617061045476593377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45946686978829454604249005 17230007617061045476593377)
  ·
    refine ⟨12922505712795784107445033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17230007617061045476593377 12922505712795784107445033)
    ·
      refine ⟨9691879284596838080583775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12922505712795784107445033 9691879284596838080583775)
      ·
        refine ⟨14537818926895257120875663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9691879284596838080583775 14537818926895257120875663)
        ·
          refine ⟨21806728390342885681313495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14537818926895257120875663 21806728390342885681313495)
          ·
            refine ⟨32710092585514328521970243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21806728390342885681313495 32710092585514328521970243)
            ·
              refine ⟨49065138878271492782955365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32710092585514328521970243 49065138878271492782955365)
              ·
                refine ⟨9199713539675904896804131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49065138878271492782955365 9199713539675904896804131)
                ·
                  refine ⟨13799570309513857345206197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9199713539675904896804131 13799570309513857345206197)
                  ·
                    refine ⟨1293709716516924126113081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13799570309513857345206197 1293709716516924126113081)
                    ·
                      refine ⟨970282287387693094584811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293709716516924126113081 970282287387693094584811)
                      ·
                        rfl

theorem cell23_1889618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_1889618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889618 prefixEnd_1889618 := by exact prefixLift 1889618
  have htrace : WordTrace (prefixWord ++ tailWord_1889618) baseStart_1889618 baseEnd_1889618 := by
    simpa [prefixWord, tailWord_1889618, baseEnd_1889618] using wordTrace_append hprefix tailTrace_1889618
  have hstable : (prefixWord ++ tailWord_1889618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889618).length < 2 ^ (prefixWord ++ tailWord_1889618).sum := by decide
  have hdescent : baseEnd_1889618 < baseStart_1889618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889635 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 2, 3, 2]
def baseStart_1889635 : Nat := 118140960795 + 1889635 * 2 ^ 59
def prefixEnd_1889635 : Nat := 4983230072969 + 3 ^ 40 * 1889635 * 2
def baseEnd_1889635 : Nat := 970291016558819528072233

theorem tailTrace_1889635 : CollatzResearch.WordTrace tailWord_1889635 prefixEnd_1889635 970291016558819528072233 := by
  unfold tailWord_1889635
  simp only [CollatzResearch.WordTrace]
  refine ⟨68920650509182593809742359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45947100339455062539828239 68920650509182593809742359)
  ·
    refine ⟨103380975763773890714613539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68920650509182593809742359 103380975763773890714613539)
    ·
      refine ⟨155071463645660836071920309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103380975763773890714613539 155071463645660836071920309)
      ·
        refine ⟨14537949716780703381742529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155071463645660836071920309 14537949716780703381742529)
        ·
          refine ⟨10903462287585527536306897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14537949716780703381742529 10903462287585527536306897)
          ·
            refine ⟨8177596715689145652230173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10903462287585527536306897 8177596715689145652230173)
            ·
              refine ⟨3066598768383429619586315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8177596715689145652230173 3066598768383429619586315)
              ·
                refine ⟨4599898152575144429379473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066598768383429619586315 4599898152575144429379473)
                ·
                  refine ⟨3449923614431358322034605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4599898152575144429379473 3449923614431358322034605)
                  ·
                    refine ⟨1293721355411759370762977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3449923614431358322034605 1293721355411759370762977)
                    ·
                      refine ⟨970291016558819528072233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293721355411759370762977 970291016558819528072233)
                      ·
                        rfl

theorem cell23_1889635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_1889635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889635 prefixEnd_1889635 := by exact prefixLift 1889635
  have htrace : WordTrace (prefixWord ++ tailWord_1889635) baseStart_1889635 baseEnd_1889635 := by
    simpa [prefixWord, tailWord_1889635, baseEnd_1889635] using wordTrace_append hprefix tailTrace_1889635
  have hstable : (prefixWord ++ tailWord_1889635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889635).length < 2 ^ (prefixWord ++ tailWord_1889635).sum := by decide
  have hdescent : baseEnd_1889635 < baseStart_1889635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889645 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_1889645 : Nat := 118140960795 + 1889645 * 2 ^ 59
def prefixEnd_1889645 : Nat := 4983230072969 + 3 ^ 40 * 1889645 * 2
def baseEnd_1889645 : Nat := 323432050455121496315729

theorem tailTrace_1889645 : CollatzResearch.WordTrace tailWord_1889645 prefixEnd_1889645 323432050455121496315729 := by
  unfold tailWord_1889645
  simp only [CollatzResearch.WordTrace]
  refine ⟨68921015239146365517606389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45947343492764243678404259 68921015239146365517606389)
  ·
    refine ⟨6461345178669971767275599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68921015239146365517606389 6461345178669971767275599)
    ·
      refine ⟨9692017768004957650913399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6461345178669971767275599 9692017768004957650913399)
      ·
        refine ⟨14538026652007436476370099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9692017768004957650913399 14538026652007436476370099)
        ·
          refine ⟨21807039978011154714555149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14538026652007436476370099 21807039978011154714555149)
          ·
            refine ⟨8177639991754183017958181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21807039978011154714555149 8177639991754183017958181)
            ·
              refine ⟨1533307498453909315867159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8177639991754183017958181 1533307498453909315867159)
              ·
                refine ⟨2299961247680863973800739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533307498453909315867159 2299961247680863973800739)
                ·
                  refine ⟨3449941871521295960701109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299961247680863973800739 3449941871521295960701109)
                  ·
                    refine ⟨323432050455121496315729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3449941871521295960701109 323432050455121496315729)
                    ·
                      rfl

theorem cell23_1889645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_1889645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889645 prefixEnd_1889645 := by exact prefixLift 1889645
  have htrace : WordTrace (prefixWord ++ tailWord_1889645) baseStart_1889645 baseEnd_1889645 := by
    simpa [prefixWord, tailWord_1889645, baseEnd_1889645] using wordTrace_append hprefix tailTrace_1889645
  have hstable : (prefixWord ++ tailWord_1889645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889645).length < 2 ^ (prefixWord ++ tailWord_1889645).sum := by decide
  have hdescent : baseEnd_1889645 < baseStart_1889645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889648 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 4]
def baseStart_1889648 : Nat := 118140960795 + 1889648 * 2 ^ 59
def prefixEnd_1889648 : Nat := 4983230072969 + 3 ^ 40 * 1889648 * 2
def baseEnd_1889648 : Nat := 970297691807327977209673

theorem tailTrace_1889648 : CollatzResearch.WordTrace tailWord_1889648 prefixEnd_1889648 970297691807327977209673 := by
  unfold tailWord_1889648
  simp only [CollatzResearch.WordTrace]
  refine ⟨34460562329067748514982799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45947416438756998019977065 34460562329067748514982799)
  ·
    refine ⟨51690843493601622772474199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34460562329067748514982799 51690843493601622772474199)
    ·
      refine ⟨77536265240402434158711299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51690843493601622772474199 77536265240402434158711299)
      ·
        refine ⟨116304397860603651238066949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77536265240402434158711299 116304397860603651238066949)
        ·
          refine ⟨21807074598863184607137553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116304397860603651238066949 21807074598863184607137553)
          ·
            refine ⟨16355305949147388455353165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21807074598863184607137553 16355305949147388455353165)
            ·
              refine ⟨6133239730930270670757437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16355305949147388455353165 6133239730930270670757437)
              ·
                refine ⟨2299964899098851501534039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6133239730930270670757437 2299964899098851501534039)
                ·
                  refine ⟨3449947348648277252301059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299964899098851501534039 3449947348648277252301059)
                  ·
                    refine ⟨5174921022972415878451589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3449947348648277252301059 5174921022972415878451589)
                    ·
                      refine ⟨970297691807327977209673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5174921022972415878451589 970297691807327977209673)
                      ·
                        rfl

theorem cell23_1889648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 4].length) (baseStart_1889648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889648 prefixEnd_1889648 := by exact prefixLift 1889648
  have htrace : WordTrace (prefixWord ++ tailWord_1889648) baseStart_1889648 baseEnd_1889648 := by
    simpa [prefixWord, tailWord_1889648, baseEnd_1889648] using wordTrace_append hprefix tailTrace_1889648
  have hstable : (prefixWord ++ tailWord_1889648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889648).length < 2 ^ (prefixWord ++ tailWord_1889648).sum := by decide
  have hdescent : baseEnd_1889648 < baseStart_1889648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889661 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_1889661 : Nat := 118140960795 + 1889661 * 2 ^ 59
def prefixEnd_1889661 : Nat := 4983230072969 + 3 ^ 40 * 1889661 * 2
def baseEnd_1889661 : Nat := 970304367055836426347113

theorem tailTrace_1889661 : CollatzResearch.WordTrace tailWord_1889661 prefixEnd_1889661 970304367055836426347113 := by
  unfold tailWord_1889661
  simp only [CollatzResearch.WordTrace]
  refine ⟨68921598807088400250188837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45947732538058933500125891 68921598807088400250188837)
  ·
    refine ⟨12922799776329075046910407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68921598807088400250188837 12922799776329075046910407)
    ·
      refine ⟨19384199664493612570365611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12922799776329075046910407 19384199664493612570365611)
      ·
        refine ⟨29076299496740418855548417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19384199664493612570365611 29076299496740418855548417)
        ·
          refine ⟨21807224622555314141661313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29076299496740418855548417 21807224622555314141661313)
          ·
            refine ⟨16355418466916485606245985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21807224622555314141661313 16355418466916485606245985)
            ·
              refine ⟨12266563850187364204684489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16355418466916485606245985 12266563850187364204684489)
              ·
                refine ⟨9199922887640523153513367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12266563850187364204684489 9199922887640523153513367)
                ·
                  refine ⟨13799884331460784730270051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9199922887640523153513367 13799884331460784730270051)
                  ·
                    refine ⟨20699826497191177095405077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13799884331460784730270051 20699826497191177095405077)
                    ·
                      refine ⟨970304367055836426347113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20699826497191177095405077 970304367055836426347113)
                      ·
                        rfl

theorem cell23_1889661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_1889661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889661 prefixEnd_1889661 := by exact prefixLift 1889661
  have htrace : WordTrace (prefixWord ++ tailWord_1889661) baseStart_1889661 baseEnd_1889661 := by
    simpa [prefixWord, tailWord_1889661, baseEnd_1889661] using wordTrace_append hprefix tailTrace_1889661
  have hstable : (prefixWord ++ tailWord_1889661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889661).length < 2 ^ (prefixWord ++ tailWord_1889661).sum := by decide
  have hdescent : baseEnd_1889661 < baseStart_1889661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889668 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1889668 : Nat := 118140960795 + 1889668 * 2 ^ 59
def prefixEnd_1889668 : Nat := 4983230072969 + 3 ^ 40 * 1889668 * 2
def baseEnd_1889668 : Nat := 970307961420417898959581

theorem tailTrace_1889668 : CollatzResearch.WordTrace tailWord_1889668 prefixEnd_1889668 970307961420417898959581 := by
  unfold tailWord_1889668
  simp only [CollatzResearch.WordTrace]
  refine ⟨34460927059031520222846829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45947902745375360297129105 34460927059031520222846829)
  ·
    refine ⟨12922847647136820083567561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34460927059031520222846829 12922847647136820083567561)
    ·
      refine ⟨9692135735352615062675671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12922847647136820083567561 9692135735352615062675671)
      ·
        refine ⟨14538203603028922594013507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9692135735352615062675671 14538203603028922594013507)
        ·
          refine ⟨21807305404543383891020261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14538203603028922594013507 21807305404543383891020261)
          ·
            refine ⟨4088869763351884479566299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21807305404543383891020261 4088869763351884479566299)
            ·
              refine ⟨6133304645027826719349449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088869763351884479566299 6133304645027826719349449)
              ·
                refine ⟨4599978483770870039512087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6133304645027826719349449 4599978483770870039512087)
                ·
                  refine ⟨6899967725656305059268131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4599978483770870039512087 6899967725656305059268131)
                  ·
                    refine ⟨10349951588484457588902197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6899967725656305059268131 10349951588484457588902197)
                    ·
                      refine ⟨970307961420417898959581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10349951588484457588902197 970307961420417898959581)
                      ·
                        rfl

theorem cell23_1889668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1889668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889668 prefixEnd_1889668 := by exact prefixLift 1889668
  have htrace : WordTrace (prefixWord ++ tailWord_1889668) baseStart_1889668 baseEnd_1889668 := by
    simpa [prefixWord, tailWord_1889668, baseEnd_1889668] using wordTrace_append hprefix tailTrace_1889668
  have hstable : (prefixWord ++ tailWord_1889668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889668).length < 2 ^ (prefixWord ++ tailWord_1889668).sum := by decide
  have hdescent : baseEnd_1889668 < baseStart_1889668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889675 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 2, 4]
def baseStart_1889675 : Nat := 118140960795 + 1889675 * 2 ^ 59
def prefixEnd_1889675 : Nat := 4983230072969 + 3 ^ 40 * 1889675 * 2
def baseEnd_1889675 : Nat := 323437185261666457190683

theorem tailTrace_1889675 : CollatzResearch.WordTrace tailWord_1889675 prefixEnd_1889675 323437185261666457190683 := by
  unfold tailWord_1889675
  simp only [CollatzResearch.WordTrace]
  refine ⟨68922109429037680641198479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45948072952691787094132319 68922109429037680641198479)
  ·
    refine ⟨103383164143556520961797719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68922109429037680641198479 103383164143556520961797719)
    ·
      refine ⟨155074746215334781442696579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103383164143556520961797719 155074746215334781442696579)
      ·
        refine ⟨232612119323002172164044869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155074746215334781442696579 232612119323002172164044869)
        ·
          refine ⟨43614772373062907280758413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232612119323002172164044869 43614772373062907280758413)
          ·
            refine ⟨16355539639898590230284405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43614772373062907280758413 16355539639898590230284405)
            ·
              refine ⟨1533331841240492834089163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16355539639898590230284405 1533331841240492834089163)
              ·
                refine ⟨2299997761860739251133745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533331841240492834089163 2299997761860739251133745)
                ·
                  refine ⟨1724998321395554438350309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2299997761860739251133745 1724998321395554438350309)
                  ·
                    refine ⟨323437185261666457190683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1724998321395554438350309 323437185261666457190683)
                    ·
                      rfl

theorem cell23_1889675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 2, 4].length) (baseStart_1889675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889675 prefixEnd_1889675 := by exact prefixLift 1889675
  have htrace : WordTrace (prefixWord ++ tailWord_1889675) baseStart_1889675 baseEnd_1889675 := by
    simpa [prefixWord, tailWord_1889675, baseEnd_1889675] using wordTrace_append hprefix tailTrace_1889675
  have hstable : (prefixWord ++ tailWord_1889675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889675).length < 2 ^ (prefixWord ++ tailWord_1889675).sum := by decide
  have hdescent : baseEnd_1889675 < baseStart_1889675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889688 : List Nat := [2, 1, 2, 5, 2, 1, 1, 9]
def baseStart_1889688 : Nat := 118140960795 + 1889688 * 2 ^ 59
def prefixEnd_1889688 : Nat := 4983230072969 + 3 ^ 40 * 1889688 * 2
def baseEnd_1889688 : Nat := 35937712260500289655907

theorem tailTrace_1889688 : CollatzResearch.WordTrace tailWord_1889688 prefixEnd_1889688 35937712260500289655907 := by
  unfold tailWord_1889688
  simp only [CollatzResearch.WordTrace]
  refine ⟨34461291788995291930710859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45948389051993722574281145 34461291788995291930710859)
  ·
    refine ⟨51691937683492937896066289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34461291788995291930710859 51691937683492937896066289)
    ·
      refine ⟨38768953262619703422049717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51691937683492937896066289 38768953262619703422049717)
      ·
        refine ⟨3634589368370597195817161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38768953262619703422049717 3634589368370597195817161)
        ·
          refine ⟨2725942026277947896862871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3634589368370597195817161 2725942026277947896862871)
          ·
            refine ⟨4088913039416921845294307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725942026277947896862871 4088913039416921845294307)
            ·
              refine ⟨6133369559125382767941461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088913039416921845294307 6133369559125382767941461)
              ·
                refine ⟨35937712260500289655907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6133369559125382767941461 35937712260500289655907)
                ·
                  rfl

theorem cell23_1889688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 9].length) (baseStart_1889688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889688 prefixEnd_1889688 := by exact prefixLift 1889688
  have htrace : WordTrace (prefixWord ++ tailWord_1889688) baseStart_1889688 baseEnd_1889688 := by
    simpa [prefixWord, tailWord_1889688, baseEnd_1889688] using wordTrace_append hprefix tailTrace_1889688
  have hstable : (prefixWord ++ tailWord_1889688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889688).length < 2 ^ (prefixWord ++ tailWord_1889688).sum := by decide
  have hdescent : baseEnd_1889688 < baseStart_1889688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889725 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 3, 3, 2]
def baseStart_1889725 : Nat := 118140960795 + 1889725 * 2 ^ 59
def prefixEnd_1889725 : Nat := 4983230072969 + 3 ^ 40 * 1889725 * 2
def baseEnd_1889725 : Nat := 970337229817724175946819

theorem tailTrace_1889725 : CollatzResearch.WordTrace tailWord_1889725 prefixEnd_1889725 970337229817724175946819 := by
  unfold tailWord_1889725
  simp only [CollatzResearch.WordTrace]
  refine ⟨68923933078856539180518629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45949288719237692787012419 68923933078856539180518629)
  ·
    refine ⟨12923237452285601096347243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68923933078856539180518629 12923237452285601096347243)
    ·
      refine ⟨19384856178428401644520865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12923237452285601096347243 19384856178428401644520865)
      ·
        refine ⟨14538642133821301233390649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19384856178428401644520865 14538642133821301233390649)
        ·
          refine ⟨10903981600365975925042987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14538642133821301233390649 10903981600365975925042987)
          ·
            refine ⟨16355972400548963887564481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10903981600365975925042987 16355972400548963887564481)
            ·
              refine ⟨12266979300411722915673361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16355972400548963887564481 12266979300411722915673361)
              ·
                refine ⟨9200234475308792186755021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12266979300411722915673361 9200234475308792186755021)
                ·
                  refine ⟨3450087928240797070033133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9200234475308792186755021 3450087928240797070033133)
                  ·
                    refine ⟨1293782973090298901262425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3450087928240797070033133 1293782973090298901262425)
                    ·
                      refine ⟨970337229817724175946819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293782973090298901262425 970337229817724175946819)
                      ·
                        rfl

theorem cell23_1889725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_1889725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889725 prefixEnd_1889725 := by exact prefixLift 1889725
  have htrace : WordTrace (prefixWord ++ tailWord_1889725) baseStart_1889725 baseEnd_1889725 := by
    simpa [prefixWord, tailWord_1889725, baseEnd_1889725] using wordTrace_append hprefix tailTrace_1889725
  have hstable : (prefixWord ++ tailWord_1889725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889725).length < 2 ^ (prefixWord ++ tailWord_1889725).sum := by decide
  have hdescent : baseEnd_1889725 < baseStart_1889725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889731 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 2, 6]
def baseStart_1889731 : Nat := 118140960795 + 1889731 * 2 ^ 59
def prefixEnd_1889731 : Nat := 4983230072969 + 3 ^ 40 * 1889731 * 2
def baseEnd_1889731 : Nat := 323446770233883717490597

theorem tailTrace_1889731 : CollatzResearch.WordTrace tailWord_1889731 prefixEnd_1889731 323446770233883717490597 := by
  unfold tailWord_1889731
  simp only [CollatzResearch.WordTrace]
  refine ⟨68924151916834802205237047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45949434611223201470158031 68924151916834802205237047)
  ·
    refine ⟨103386227875252203307855571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68924151916834802205237047 103386227875252203307855571)
    ·
      refine ⟨155079341812878304961783357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103386227875252203307855571 155079341812878304961783357)
      ·
        refine ⟨58154753179829364360668759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155079341812878304961783357 58154753179829364360668759)
        ·
          refine ⟨87232129769744046541003139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58154753179829364360668759 87232129769744046541003139)
          ·
            refine ⟨130848194654616069811504709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87232129769744046541003139 130848194654616069811504709)
            ·
              refine ⟨24534036497740513089657133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130848194654616069811504709 24534036497740513089657133)
              ·
                refine ⟨9200263686652692408621425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24534036497740513089657133 9200263686652692408621425)
                ·
                  refine ⟨6900197764989519306466069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9200263686652692408621425 6900197764989519306466069)
                  ·
                    refine ⟨323446770233883717490597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6900197764989519306466069 323446770233883717490597)
                    ·
                      rfl

theorem cell23_1889731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 6].length) (baseStart_1889731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889731 prefixEnd_1889731 := by exact prefixLift 1889731
  have htrace : WordTrace (prefixWord ++ tailWord_1889731) baseStart_1889731 baseEnd_1889731 := by
    simpa [prefixWord, tailWord_1889731, baseEnd_1889731] using wordTrace_append hprefix tailTrace_1889731
  have hstable : (prefixWord ++ tailWord_1889731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889731).length < 2 ^ (prefixWord ++ tailWord_1889731).sum := by decide
  have hdescent : baseEnd_1889731 < baseStart_1889731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889742 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2]
def baseStart_1889742 : Nat := 118140960795 + 1889742 * 2 ^ 59
def prefixEnd_1889742 : Nat := 4983230072969 + 3 ^ 40 * 1889742 * 2
def baseEnd_1889742 : Nat := 970345958988850609434241

theorem tailTrace_1889742 : CollatzResearch.WordTrace tailWord_1889742 prefixEnd_1889742 970345958988850609434241 := by
  unfold tailWord_1889742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8615569139974368885485935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45949702079863300722591653 8615569139974368885485935)
  ·
    refine ⟨12923353709961553328228903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8615569139974368885485935 12923353709961553328228903)
    ·
      refine ⟨19385030564942329992343355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12923353709961553328228903 19385030564942329992343355)
      ·
        refine ⟨29077545847413494988515033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19385030564942329992343355 29077545847413494988515033)
        ·
          refine ⟨21808159385560121241386275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29077545847413494988515033 21808159385560121241386275)
          ·
            refine ⟨32712239078340181862079413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21808159385560121241386275 32712239078340181862079413)
            ·
              refine ⟨3066772413594392049569945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32712239078340181862079413 3066772413594392049569945)
              ·
                refine ⟨2300079310195794037177459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066772413594392049569945 2300079310195794037177459)
                ·
                  refine ⟨3450118965293691055766189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300079310195794037177459 3450118965293691055766189)
                  ·
                    refine ⟨1293794611985134145912321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3450118965293691055766189 1293794611985134145912321)
                    ·
                      refine ⟨970345958988850609434241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293794611985134145912321 970345958988850609434241)
                      ·
                        rfl

theorem cell23_1889742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_1889742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889742 prefixEnd_1889742 := by exact prefixLift 1889742
  have htrace : WordTrace (prefixWord ++ tailWord_1889742) baseStart_1889742 baseEnd_1889742 := by
    simpa [prefixWord, tailWord_1889742, baseEnd_1889742] using wordTrace_append hprefix tailTrace_1889742
  have hstable : (prefixWord ++ tailWord_1889742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889742).length < 2 ^ (prefixWord ++ tailWord_1889742).sum := by decide
  have hdescent : baseEnd_1889742 < baseStart_1889742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889768 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1889768 : Nat := 118140960795 + 1889768 * 2 ^ 59
def prefixEnd_1889768 : Nat := 4983230072969 + 3 ^ 40 * 1889768 * 2
def baseEnd_1889768 : Nat := 970359309485867507709121

theorem tailTrace_1889768 : CollatzResearch.WordTrace tailWord_1889768 prefixEnd_1889768 970359309485867507709121 := by
  unfold tailWord_1889768
  simp only [CollatzResearch.WordTrace]
  refine ⟨34462750708850378762166979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45950334278467171682889305 34462750708850378762166979)
  ·
    refine ⟨51694126063275568143250469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34462750708850378762166979 51694126063275568143250469)
    ·
      refine ⟨9692648636864169026859463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51694126063275568143250469 9692648636864169026859463)
      ·
        refine ⟨14538972955296253540289195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9692648636864169026859463 14538972955296253540289195)
        ·
          refine ⟨21808459432944380310433793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14538972955296253540289195 21808459432944380310433793)
          ·
            refine ⟨16356344574708285232825345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21808459432944380310433793 16356344574708285232825345)
            ·
              refine ⟨12267258431031213924619009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16356344574708285232825345 12267258431031213924619009)
              ·
                refine ⟨9200443823273410443464257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12267258431031213924619009 9200443823273410443464257)
                ·
                  refine ⟨6900332867455057832598193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9200443823273410443464257 6900332867455057832598193)
                  ·
                    refine ⟨5175249650591293374448645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6900332867455057832598193 5175249650591293374448645)
                    ·
                      refine ⟨970359309485867507709121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5175249650591293374448645 970359309485867507709121)
                      ·
                        rfl

theorem cell23_1889768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1889768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889768 prefixEnd_1889768 := by exact prefixLift 1889768
  have htrace : WordTrace (prefixWord ++ tailWord_1889768) baseStart_1889768 baseEnd_1889768 := by
    simpa [prefixWord, tailWord_1889768, baseEnd_1889768] using wordTrace_append hprefix tailTrace_1889768
  have hstable : (prefixWord ++ tailWord_1889768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889768).length < 2 ^ (prefixWord ++ tailWord_1889768).sum := by decide
  have hdescent : baseEnd_1889768 < baseStart_1889768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889788 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_1889788 : Nat := 118140960795 + 1889788 * 2 ^ 59
def prefixEnd_1889788 : Nat := 4983230072969 + 3 ^ 40 * 1889788 * 2
def baseEnd_1889788 : Nat := 970369579098957429459029

theorem tailTrace_1889788 : CollatzResearch.WordTrace tailWord_1889788 prefixEnd_1889788 970369579098957429459029 := by
  unfold tailWord_1889788
  simp only [CollatzResearch.WordTrace]
  refine ⟨34463115438814150470031009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45950820585085533960041345 34463115438814150470031009)
  ·
    refine ⟨25847336579110612852523257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34463115438814150470031009 25847336579110612852523257)
    ·
      refine ⟨19385502434332959639392443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25847336579110612852523257 19385502434332959639392443)
      ·
        refine ⟨29078253651499439459088665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19385502434332959639392443 29078253651499439459088665)
        ·
          refine ⟨21808690238624579594316499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29078253651499439459088665 21808690238624579594316499)
          ·
            refine ⟨32713035357936869391474749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21808690238624579594316499 32713035357936869391474749)
            ·
              refine ⟨12267388259226326021803031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32713035357936869391474749 12267388259226326021803031)
              ·
                refine ⟨18401082388839489032704547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267388259226326021803031 18401082388839489032704547)
                ·
                  refine ⟨27601623583259233549056821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18401082388839489032704547 27601623583259233549056821)
                  ·
                    refine ⟨2587652210930553145224077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27601623583259233549056821 2587652210930553145224077)
                    ·
                      refine ⟨970369579098957429459029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2587652210930553145224077 970369579098957429459029)
                      ·
                        rfl

theorem cell23_1889788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_1889788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889788 prefixEnd_1889788 := by exact prefixLift 1889788
  have htrace : WordTrace (prefixWord ++ tailWord_1889788) baseStart_1889788 baseEnd_1889788 := by
    simpa [prefixWord, tailWord_1889788, baseEnd_1889788] using wordTrace_append hprefix tailTrace_1889788
  have hstable : (prefixWord ++ tailWord_1889788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889788).length < 2 ^ (prefixWord ++ tailWord_1889788).sum := by decide
  have hdescent : baseEnd_1889788 < baseStart_1889788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889855 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 3, 4]
def baseStart_1889855 : Nat := 118140960795 + 1889855 * 2 ^ 59
def prefixEnd_1889855 : Nat := 4983230072969 + 3 ^ 40 * 1889855 * 2
def baseEnd_1889855 : Nat := 323467994100936222440407

theorem tailTrace_1889855 : CollatzResearch.WordTrace tailWord_1889855 prefixEnd_1889855 323467994100936222440407 := by
  unfold tailWord_1889855
  simp only [CollatzResearch.WordTrace]
  refine ⟨68928674568385571382751019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45952449712257047588500679 68928674568385571382751019)
  ·
    refine ⟨103393011852578357074126529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68928674568385571382751019 103393011852578357074126529)
    ·
      refine ⟨77544758889433767805594897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103393011852578357074126529 77544758889433767805594897)
      ·
        refine ⟨58158569167075325854196173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77544758889433767805594897 58158569167075325854196173)
        ·
          refine ⟨21809463437653247195323565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58158569167075325854196173 21809463437653247195323565)
          ·
            refine ⟨8178548789119967698246337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21809463437653247195323565 8178548789119967698246337)
            ·
              refine ⟨6133911591839975773684753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8178548789119967698246337 6133911591839975773684753)
              ·
                refine ⟨4600433693879981830263565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6133911591839975773684753 4600433693879981830263565)
                ·
                  refine ⟨1725162635204993186348837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4600433693879981830263565 1725162635204993186348837)
                  ·
                    refine ⟨323467994100936222440407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1725162635204993186348837 323467994100936222440407)
                    ·
                      rfl

theorem cell23_1889855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 4].length) (baseStart_1889855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889855 prefixEnd_1889855 := by exact prefixLift 1889855
  have htrace : WordTrace (prefixWord ++ tailWord_1889855) baseStart_1889855 baseEnd_1889855 := by
    simpa [prefixWord, tailWord_1889855, baseEnd_1889855] using wordTrace_append hprefix tailTrace_1889855
  have hstable : (prefixWord ++ tailWord_1889855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889855).length < 2 ^ (prefixWord ++ tailWord_1889855).sum := by decide
  have hdescent : baseEnd_1889855 < baseStart_1889855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889868 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 8]
def baseStart_1889868 : Nat := 118140960795 + 1889868 * 2 ^ 59
def prefixEnd_1889868 : Nat := 4983230072969 + 3 ^ 40 * 1889868 * 2
def baseEnd_1889868 : Nat := 107823406394590790717629

theorem tailTrace_1889868 : CollatzResearch.WordTrace tailWord_1889868 prefixEnd_1889868 107823406394590790717629 := by
  unfold tailWord_1889868
  simp only [CollatzResearch.WordTrace]
  refine ⟨34464574358669237301487129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45952765811558983068649505 34464574358669237301487129)
  ·
    refine ⟨25848430769001927976115347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34464574358669237301487129 25848430769001927976115347)
    ·
      refine ⟨38772646153502891964173021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25848430769001927976115347 38772646153502891964173021)
      ·
        refine ⟨14539742307563584486564883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38772646153502891964173021 14539742307563584486564883)
        ·
          refine ⟨21809613461345376729847325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14539742307563584486564883 21809613461345376729847325)
          ·
            refine ⟨8178605048004516273692747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21809613461345376729847325 8178605048004516273692747)
            ·
              refine ⟨12267907572006774410539121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178605048004516273692747 12267907572006774410539121)
              ·
                refine ⟨9200930679005080807904341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12267907572006774410539121 9200930679005080807904341)
                ·
                  refine ⟨107823406394590790717629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9200930679005080807904341 107823406394590790717629)
                  ·
                    rfl

theorem cell23_1889868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_1889868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889868 prefixEnd_1889868 := by exact prefixLift 1889868
  have htrace : WordTrace (prefixWord ++ tailWord_1889868) baseStart_1889868 baseEnd_1889868 := by
    simpa [prefixWord, tailWord_1889868, baseEnd_1889868] using wordTrace_append hprefix tailTrace_1889868
  have hstable : (prefixWord ++ tailWord_1889868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889868).length < 2 ^ (prefixWord ++ tailWord_1889868).sum := by decide
  have hdescent : baseEnd_1889868 < baseStart_1889868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889889 : List Nat := [1, 2, 3, 1, 1, 3, 5, 2, 1, 4]
def baseStart_1889889 : Nat := 118140960795 + 1889889 * 2 ^ 59
def prefixEnd_1889889 : Nat := 4983230072969 + 3 ^ 40 * 1889889 * 2
def baseEnd_1889889 : Nat := 323473813548353844765355

theorem tailTrace_1889889 : CollatzResearch.WordTrace tailWord_1889889 prefixEnd_1889889 323473813548353844765355 := by
  unfold tailWord_1889889
  simp only [CollatzResearch.WordTrace]
  refine ⟨68929914650262395189488721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45953276433508263459659147 68929914650262395189488721)
  ·
    refine ⟨51697435987696796392116541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68929914650262395189488721 51697435987696796392116541)
    ·
      refine ⟨19386538495386298647043703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51697435987696796392116541 19386538495386298647043703)
      ·
        refine ⟨29079807743079447970565555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19386538495386298647043703 29079807743079447970565555)
        ·
          refine ⟨43619711614619171955848333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29079807743079447970565555 43619711614619171955848333)
          ·
            refine ⟨16357391855482189483443125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43619711614619171955848333 16357391855482189483443125)
            ·
              refine ⟨1533505486451455264072793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16357391855482189483443125 1533505486451455264072793)
              ·
                refine ⟨1150129114838591448054595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1533505486451455264072793 1150129114838591448054595)
                ·
                  refine ⟨1725193672257887172081893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150129114838591448054595 1725193672257887172081893)
                  ·
                    refine ⟨323473813548353844765355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1725193672257887172081893 323473813548353844765355)
                    ·
                      rfl

theorem cell23_1889889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_1889889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889889 prefixEnd_1889889 := by exact prefixLift 1889889
  have htrace : WordTrace (prefixWord ++ tailWord_1889889) baseStart_1889889 baseEnd_1889889 := by
    simpa [prefixWord, tailWord_1889889, baseEnd_1889889] using wordTrace_append hprefix tailTrace_1889889
  have hstable : (prefixWord ++ tailWord_1889889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889889).length < 2 ^ (prefixWord ++ tailWord_1889889).sum := by decide
  have hdescent : baseEnd_1889889 < baseStart_1889889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889902 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_1889902 : Nat := 118140960795 + 1889902 * 2 ^ 59
def prefixEnd_1889902 : Nat := 4983230072969 + 3 ^ 40 * 1889902 * 2
def baseEnd_1889902 : Nat := 107825346210396664825945

theorem tailTrace_1889902 : CollatzResearch.WordTrace tailWord_1889902 prefixEnd_1889902 107825346210396664825945 := by
  unfold tailWord_1889902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8616298599901912301213995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45953592532810198939807973 8616298599901912301213995)
  ·
    refine ⟨12924447899852868451820993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8616298599901912301213995 12924447899852868451820993)
    ·
      refine ⟨9693335924889651338865745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12924447899852868451820993 9693335924889651338865745)
      ·
        refine ⟨7270001943667238504149309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9693335924889651338865745 7270001943667238504149309)
        ·
          refine ⟨2726250728875214439055991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7270001943667238504149309 2726250728875214439055991)
          ·
            refine ⟨4089376093312821658583987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726250728875214439055991 4089376093312821658583987)
            ·
              refine ⟨6134064139969232487875981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4089376093312821658583987 6134064139969232487875981)
              ·
                refine ⟨2300274052488462182953493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6134064139969232487875981 2300274052488462182953493)
                ·
                  refine ⟨107825346210396664825945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2300274052488462182953493 107825346210396664825945)
                  ·
                    rfl

theorem cell23_1889902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_1889902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889902 prefixEnd_1889902 := by exact prefixLift 1889902
  have htrace : WordTrace (prefixWord ++ tailWord_1889902) baseStart_1889902 baseEnd_1889902 := by
    simpa [prefixWord, tailWord_1889902, baseEnd_1889902] using wordTrace_append hprefix tailTrace_1889902
  have hstable : (prefixWord ++ tailWord_1889902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889902).length < 2 ^ (prefixWord ++ tailWord_1889902).sum := by decide
  have hdescent : baseEnd_1889902 < baseStart_1889902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889905 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 3, 5, 2]
def baseStart_1889905 : Nat := 118140960795 + 1889905 * 2 ^ 59
def prefixEnd_1889905 : Nat := 4983230072969 + 3 ^ 40 * 1889905 * 2
def baseEnd_1889905 : Nat := 970429656335533471695991

theorem tailTrace_1889905 : CollatzResearch.WordTrace tailWord_1889905 prefixEnd_1889905 970429656335533471695991 := by
  unfold tailWord_1889905
  simp only [CollatzResearch.WordTrace]
  refine ⟨68930498218204429922071169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45953665478802953281380779 68930498218204429922071169)
  ·
    refine ⟨51697873663653322441553377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68930498218204429922071169 51697873663653322441553377)
    ·
      refine ⟨38773405247739991831165033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51697873663653322441553377 38773405247739991831165033)
      ·
        refine ⟨29080053935804993873373775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38773405247739991831165033 29080053935804993873373775)
        ·
          refine ⟨43620080903707490810060663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29080053935804993873373775 43620080903707490810060663)
          ·
            refine ⟨65430121355561236215090995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43620080903707490810060663 65430121355561236215090995)
            ·
              refine ⟨98145182033341854322636493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65430121355561236215090995 98145182033341854322636493)
              ·
                refine ⟨36804443262503195370988685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98145182033341854322636493 36804443262503195370988685)
                ·
                  refine ⟨13801666223438698264120757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36804443262503195370988685 13801666223438698264120757)
                  ·
                    refine ⟨1293906208447377962261321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13801666223438698264120757 1293906208447377962261321)
                    ·
                      refine ⟨970429656335533471695991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293906208447377962261321 970429656335533471695991)
                      ·
                        rfl

theorem cell23_1889905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_1889905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889905 prefixEnd_1889905 := by exact prefixLift 1889905
  have htrace : WordTrace (prefixWord ++ tailWord_1889905) baseStart_1889905 baseEnd_1889905 := by
    simpa [prefixWord, tailWord_1889905, baseEnd_1889905] using wordTrace_append hprefix tailTrace_1889905
  have hstable : (prefixWord ++ tailWord_1889905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889905).length < 2 ^ (prefixWord ++ tailWord_1889905).sum := by decide
  have hdescent : baseEnd_1889905 < baseStart_1889905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889932 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 1, 5]
def baseStart_1889932 : Nat := 118140960795 + 1889932 * 2 ^ 59
def prefixEnd_1889932 : Nat := 4983230072969 + 3 ^ 40 * 1889932 * 2
def baseEnd_1889932 : Nat := 323481173437734955352789

theorem tailTrace_1889932 : CollatzResearch.WordTrace tailWord_1889932 prefixEnd_1889932 323481173437734955352789 := by
  unfold tailWord_1889932
  simp only [CollatzResearch.WordTrace]
  refine ⟨34465741494553306766652025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45954321992737742355536033 34465741494553306766652025)
  ·
    refine ⟨25849306120914980074989019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34465741494553306766652025 25849306120914980074989019)
    ·
      refine ⟨38773959181372470112483529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25849306120914980074989019 38773959181372470112483529)
      ·
        refine ⟨29080469386029352584362647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38773959181372470112483529 29080469386029352584362647)
        ·
          refine ⟨43620704079044028876543971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29080469386029352584362647 43620704079044028876543971)
          ·
            refine ⟨65431056118566043314815957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43620704079044028876543971 65431056118566043314815957)
            ·
              refine ⟨1533540377778891640190999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 65431056118566043314815957 1533540377778891640190999)
              ·
                refine ⟨2300310566668337460286499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533540377778891640190999 2300310566668337460286499)
                ·
                  refine ⟨3450465850002506190429749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300310566668337460286499 3450465850002506190429749)
                  ·
                    refine ⟨323481173437734955352789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3450465850002506190429749 323481173437734955352789)
                    ·
                      rfl

theorem cell23_1889932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_1889932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889932 prefixEnd_1889932 := by exact prefixLift 1889932
  have htrace : WordTrace (prefixWord ++ tailWord_1889932) baseStart_1889932 baseEnd_1889932 := by
    simpa [prefixWord, tailWord_1889932, baseEnd_1889932] using wordTrace_append hprefix tailTrace_1889932
  have hstable : (prefixWord ++ tailWord_1889932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889932).length < 2 ^ (prefixWord ++ tailWord_1889932).sum := by decide
  have hdescent : baseEnd_1889932 < baseStart_1889932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889940 : List Nat := [2, 4, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1889940 : Nat := 118140960795 + 1889940 * 2 ^ 59
def prefixEnd_1889940 : Nat := 4983230072969 + 3 ^ 40 * 1889940 * 2
def baseEnd_1889940 : Nat := 323482542719480278252777

theorem tailTrace_1889940 : CollatzResearch.WordTrace tailWord_1889940 prefixEnd_1889940 323482542719480278252777 := by
  unfold tailWord_1889940
  simp only [CollatzResearch.WordTrace]
  refine ⟨34465887386538815449797637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45954516515385087266396849 34465887386538815449797637)
  ·
    refine ⟨6462353884976027896837057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34465887386538815449797637 6462353884976027896837057)
    ·
      refine ⟨4846765413732020922627793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6462353884976027896837057 4846765413732020922627793)
      ·
        refine ⟨3635074060299015691970845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4846765413732020922627793 3635074060299015691970845)
        ·
          refine ⟨1363152772612130884489067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3635074060299015691970845 1363152772612130884489067)
          ·
            refine ⟨2044729158918196326733601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363152772612130884489067 2044729158918196326733601)
            ·
              refine ⟨1533546869188647245050201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044729158918196326733601 1533546869188647245050201)
              ·
                refine ⟨1150160151891485433787651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1533546869188647245050201 1150160151891485433787651)
                ·
                  refine ⟨1725240227837228150681477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150160151891485433787651 1725240227837228150681477)
                  ·
                    refine ⟨323482542719480278252777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1725240227837228150681477 323482542719480278252777)
                    ·
                      rfl

theorem cell23_1889940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1889940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889940 prefixEnd_1889940 := by exact prefixLift 1889940
  have htrace : WordTrace (prefixWord ++ tailWord_1889940) baseStart_1889940 baseEnd_1889940 := by
    simpa [prefixWord, tailWord_1889940, baseEnd_1889940] using wordTrace_append hprefix tailTrace_1889940
  have hstable : (prefixWord ++ tailWord_1889940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889940).length < 2 ^ (prefixWord ++ tailWord_1889940).sum := by decide
  have hdescent : baseEnd_1889940 < baseStart_1889940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889955 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 3]
def baseStart_1889955 : Nat := 118140960795 + 1889955 * 2 ^ 59
def prefixEnd_1889955 : Nat := 4983230072969 + 3 ^ 40 * 1889955 * 2
def baseEnd_1889955 : Nat := 970455330368258276070761

theorem tailTrace_1889955 : CollatzResearch.WordTrace tailWord_1889955 prefixEnd_1889955 970455330368258276070761 := by
  unfold tailWord_1889955
  simp only [CollatzResearch.WordTrace]
  refine ⟨68932321868023288461391319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45954881245348858974260879 68932321868023288461391319)
  ·
    refine ⟨103398482802034932692086979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68932321868023288461391319 103398482802034932692086979)
    ·
      refine ⟨155097724203052399038130469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103398482802034932692086979 155097724203052399038130469)
      ·
        refine ⟨29080823288072324819649463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155097724203052399038130469 29080823288072324819649463)
        ·
          refine ⟨43621234932108487229474195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29080823288072324819649463 43621234932108487229474195)
          ·
            refine ⟨65431852398162730844211293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43621234932108487229474195 65431852398162730844211293)
            ·
              refine ⟨24536944649311024066579235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65431852398162730844211293 24536944649311024066579235)
              ·
                refine ⟨36805416973966536099868853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24536944649311024066579235 36805416973966536099868853)
                ·
                  refine ⟨3450507841309362759362705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36805416973966536099868853 3450507841309362759362705)
                  ·
                    refine ⟨2587880880982022069522029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3450507841309362759362705 2587880880982022069522029)
                    ·
                      refine ⟨970455330368258276070761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2587880880982022069522029 970455330368258276070761)
                      ·
                        rfl

theorem cell23_1889955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_1889955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889955 prefixEnd_1889955 := by exact prefixLift 1889955
  have htrace : WordTrace (prefixWord ++ tailWord_1889955) baseStart_1889955 baseEnd_1889955 := by
    simpa [prefixWord, tailWord_1889955, baseEnd_1889955] using wordTrace_append hprefix tailTrace_1889955
  have hstable : (prefixWord ++ tailWord_1889955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889955).length < 2 ^ (prefixWord ++ tailWord_1889955).sum := by decide
  have hdescent : baseEnd_1889955 < baseStart_1889955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889973 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_1889973 : Nat := 118140960795 + 1889973 * 2 ^ 59
def prefixEnd_1889973 : Nat := 4983230072969 + 3 ^ 40 * 1889973 * 2
def baseEnd_1889973 : Nat := 970464573020039205645679

theorem tailTrace_1889973 : CollatzResearch.WordTrace tailWord_1889973 prefixEnd_1889973 970464573020039205645679 := by
  unfold tailWord_1889973
  simp only [CollatzResearch.WordTrace]
  refine ⟨68932978381958077535546573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45955318921305385023697715 68932978381958077535546573)
  ·
    refine ⟨25849866893234279075829965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68932978381958077535546573 25849866893234279075829965)
    ·
      refine ⟨9693700084962854653436237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25849866893234279075829965 9693700084962854653436237)
      ·
        refine ⟨3635137531861070495038589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9693700084962854653436237 3635137531861070495038589)
        ·
          refine ⟨1363176574447901435639471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3635137531861070495038589 1363176574447901435639471)
          ·
            refine ⟨2044764861671852153459207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363176574447901435639471 2044764861671852153459207)
            ·
              refine ⟨3067147292507778230188811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044764861671852153459207 3067147292507778230188811)
              ·
                refine ⟨4600720938761667345283217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067147292507778230188811 4600720938761667345283217)
                ·
                  refine ⟨3450540704071250508962413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4600720938761667345283217 3450540704071250508962413)
                  ·
                    refine ⟨1293952764026718940860905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3450540704071250508962413 1293952764026718940860905)
                    ·
                      refine ⟨970464573020039205645679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1293952764026718940860905 970464573020039205645679)
                      ·
                        rfl

theorem cell23_1889973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_1889973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889973 prefixEnd_1889973 := by exact prefixLift 1889973
  have htrace : WordTrace (prefixWord ++ tailWord_1889973) baseStart_1889973 baseEnd_1889973 := by
    simpa [prefixWord, tailWord_1889973, baseEnd_1889973] using wordTrace_append hprefix tailTrace_1889973
  have hstable : (prefixWord ++ tailWord_1889973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889973).length < 2 ^ (prefixWord ++ tailWord_1889973).sum := by decide
  have hdescent : baseEnd_1889973 < baseStart_1889973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889982 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1889982 : Nat := 118140960795 + 1889982 * 2 ^ 59
def prefixEnd_1889982 : Nat := 4983230072969 + 3 ^ 40 * 1889982 * 2
def baseEnd_1889982 : Nat := 970469194345929670433137

theorem tailTrace_1889982 : CollatzResearch.WordTrace tailWord_1889982 prefixEnd_1889982 970469194345929670433137 := by
  unfold tailWord_1889982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8616663329865684009078025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45955537759283648048416133 8616663329865684009078025)
  ·
    refine ⟨6462497497399263006808519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8616663329865684009078025 6462497497399263006808519)
    ·
      refine ⟨9693746246098894510212779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6462497497399263006808519 9693746246098894510212779)
      ·
        refine ⟨14540619369148341765319169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9693746246098894510212779 14540619369148341765319169)
        ·
          refine ⟨10905464526861256323989377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14540619369148341765319169 10905464526861256323989377)
          ·
            refine ⟨8179098395145942242992033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10905464526861256323989377 8179098395145942242992033)
            ·
              refine ⟨6134323796359456682244025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8179098395145942242992033 6134323796359456682244025)
              ·
                refine ⟨4600742847269592511683019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6134323796359456682244025 4600742847269592511683019)
                ·
                  refine ⟨6901114270904388767524529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600742847269592511683019 6901114270904388767524529)
                  ·
                    refine ⟨5175835703178291575643397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6901114270904388767524529 5175835703178291575643397)
                    ·
                      refine ⟨970469194345929670433137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5175835703178291575643397 970469194345929670433137)
                      ·
                        rfl

theorem cell23_1889982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1889982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889982 prefixEnd_1889982 := by exact prefixLift 1889982
  have htrace : WordTrace (prefixWord ++ tailWord_1889982) baseStart_1889982 baseEnd_1889982 := by
    simpa [prefixWord, tailWord_1889982, baseEnd_1889982] using wordTrace_append hprefix tailTrace_1889982
  have hstable : (prefixWord ++ tailWord_1889982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889982).length < 2 ^ (prefixWord ++ tailWord_1889982).sum := by decide
  have hdescent : baseEnd_1889982 < baseStart_1889982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889996 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 2, 4]
def baseStart_1889996 : Nat := 118140960795 + 1889996 * 2 ^ 59
def prefixEnd_1889996 : Nat := 4983230072969 + 3 ^ 40 * 1889996 * 2
def baseEnd_1889996 : Nat := 323492127691697538552691

theorem tailTrace_1889996 : CollatzResearch.WordTrace tailWord_1889996 prefixEnd_1889996 323492127691697538552691 := by
  unfold tailWord_1889996
  simp only [CollatzResearch.WordTrace]
  refine ⟨34466908630437376231816921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45955878173916501642422561 34466908630437376231816921)
  ·
    refine ⟨25850181472828032173862691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34466908630437376231816921 25850181472828032173862691)
    ·
      refine ⟨38775272209242048260794037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25850181472828032173862691 38775272209242048260794037)
      ·
        refine ⟨3635181769616442024449441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38775272209242048260794037 3635181769616442024449441)
        ·
          refine ⟨2726386327212331518337081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3635181769616442024449441 2726386327212331518337081)
          ·
            refine ⟨2044789745409248638752811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2726386327212331518337081 2044789745409248638752811)
            ·
              refine ⟨3067184618113872958129217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044789745409248638752811 3067184618113872958129217)
              ·
                refine ⟨2300388463585404718596913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3067184618113872958129217 2300388463585404718596913)
                ·
                  refine ⟨1725291347689053538947685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2300388463585404718596913 1725291347689053538947685)
                  ·
                    refine ⟨323492127691697538552691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1725291347689053538947685 323492127691697538552691)
                    ·
                      rfl

theorem cell23_1889996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_1889996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1889996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1889996 prefixEnd_1889996 := by exact prefixLift 1889996
  have htrace : WordTrace (prefixWord ++ tailWord_1889996) baseStart_1889996 baseEnd_1889996 := by
    simpa [prefixWord, tailWord_1889996, baseEnd_1889996] using wordTrace_append hprefix tailTrace_1889996
  have hstable : (prefixWord ++ tailWord_1889996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889996).length < 2 ^ (prefixWord ++ tailWord_1889996).sum := by decide
  have hdescent : baseEnd_1889996 < baseStart_1889996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890006 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1890006 : Nat := 118140960795 + 1890006 * 2 ^ 59
def prefixEnd_1890006 : Nat := 4983230072969 + 3 ^ 40 * 1890006 * 2
def baseEnd_1890006 : Nat := 970481517881637576533027

theorem tailTrace_1890006 : CollatzResearch.WordTrace tailWord_1890006 prefixEnd_1890006 970481517881637576533027 := by
  unfold tailWord_1890006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308386374427407760718617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45956121327225682780998581 4308386374427407760718617)
  ·
    refine ⟨3231289780820555820538963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4308386374427407760718617 3231289780820555820538963)
    ·
      refine ⟨4846934671230833730808445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3231289780820555820538963 4846934671230833730808445)
      ·
        refine ⟨1817600501711562649053167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4846934671230833730808445 1817600501711562649053167)
        ·
          refine ⟨2726400752567343973579751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1817600501711562649053167 2726400752567343973579751)
          ·
            refine ⟨4089601128851015960369627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726400752567343973579751 4089601128851015960369627)
            ·
              refine ⟨6134401693276523940554441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4089601128851015960369627 6134401693276523940554441)
              ·
                refine ⟨4600801269957392955415831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6134401693276523940554441 4600801269957392955415831)
                ·
                  refine ⟨6901201904936089433123747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4600801269957392955415831 6901201904936089433123747)
                  ·
                    refine ⟨10351802857404134149685621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6901201904936089433123747 10351802857404134149685621)
                    ·
                      refine ⟨970481517881637576533027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10351802857404134149685621 970481517881637576533027)
                      ·
                        rfl

theorem cell23_1890006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1890006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890006 prefixEnd_1890006 := by exact prefixLift 1890006
  have htrace : WordTrace (prefixWord ++ tailWord_1890006) baseStart_1890006 baseEnd_1890006 := by
    simpa [prefixWord, tailWord_1890006, baseEnd_1890006] using wordTrace_append hprefix tailTrace_1890006
  have hstable : (prefixWord ++ tailWord_1890006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890006).length < 2 ^ (prefixWord ++ tailWord_1890006).sum := by decide
  have hdescent : baseEnd_1890006 < baseStart_1890006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890013 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1890013 : Nat := 118140960795 + 1890013 * 2 ^ 59
def prefixEnd_1890013 : Nat := 4983230072969 + 3 ^ 40 * 1890013 * 2
def baseEnd_1890013 : Nat := 323495037415406349715165

theorem tailTrace_1890013 : CollatzResearch.WordTrace tailWord_1890013 prefixEnd_1890013 323495037415406349715165 := by
  unfold tailWord_1890013
  simp only [CollatzResearch.WordTrace]
  refine ⟨68934437301813164367002693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45956291534542109578001795 68934437301813164367002693)
  ·
    refine ⟨12925206994089968318813005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68934437301813164367002693 12925206994089968318813005)
    ·
      refine ⟨4846952622783738119554877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12925206994089968318813005 4846952622783738119554877)
      ·
        refine ⟨1817607233543901794833079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4846952622783738119554877 1817607233543901794833079)
        ·
          refine ⟨2726410850315852692249619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1817607233543901794833079 2726410850315852692249619)
          ·
            refine ⟨4089616275473779038374429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726410850315852692249619 4089616275473779038374429)
            ·
              refine ⟨1533606103302667139390411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4089616275473779038374429 1533606103302667139390411)
              ·
                refine ⟨2300409154954000709085617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533606103302667139390411 2300409154954000709085617)
                ·
                  refine ⟨1725306866215500531814213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2300409154954000709085617 1725306866215500531814213)
                  ·
                    refine ⟨323495037415406349715165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1725306866215500531814213 323495037415406349715165)
                    ·
                      rfl

theorem cell23_1890013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1890013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890013 prefixEnd_1890013 := by exact prefixLift 1890013
  have htrace : WordTrace (prefixWord ++ tailWord_1890013) baseStart_1890013 baseEnd_1890013 := by
    simpa [prefixWord, tailWord_1890013, baseEnd_1890013] using wordTrace_append hprefix tailTrace_1890013
  have hstable : (prefixWord ++ tailWord_1890013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890013).length < 2 ^ (prefixWord ++ tailWord_1890013).sum := by decide
  have hdescent : baseEnd_1890013 < baseStart_1890013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890042 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2]
def baseStart_1890042 : Nat := 118140960795 + 1890042 * 2 ^ 59
def prefixEnd_1890042 : Nat := 4983230072969 + 3 ^ 40 * 1890042 * 2
def baseEnd_1890042 : Nat := 970500003185199435682861

theorem tailTrace_1890042 : CollatzResearch.WordTrace tailWord_1890042 prefixEnd_1890042 970500003185199435682861 := by
  unfold tailWord_1890042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17233873754677025579952095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45956996679138734879872253 17233873754677025579952095)
  ·
    refine ⟨25850810632015538369928143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17233873754677025579952095 25850810632015538369928143)
    ·
      refine ⟨38776215948023307554892215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25850810632015538369928143 38776215948023307554892215)
      ·
        refine ⟨58164323922034961332338323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38776215948023307554892215 58164323922034961332338323)
        ·
          refine ⟨87246485883052441998507485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58164323922034961332338323 87246485883052441998507485)
          ·
            refine ⟨32717432206144665749440307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87246485883052441998507485 32717432206144665749440307)
            ·
              refine ⟨49076148309216998624160461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32717432206144665749440307 49076148309216998624160461)
              ·
                refine ⟨18403555615956374484060173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49076148309216998624160461 18403555615956374484060173)
                ·
                  refine ⟨6901333355983640431522565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18403555615956374484060173 6901333355983640431522565)
                  ·
                    refine ⟨1294000004246932580910481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6901333355983640431522565 1294000004246932580910481)
                    ·
                      refine ⟨970500003185199435682861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294000004246932580910481 970500003185199435682861)
                      ·
                        rfl

theorem cell23_1890042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2].length) (baseStart_1890042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890042 prefixEnd_1890042 := by exact prefixLift 1890042
  have htrace : WordTrace (prefixWord ++ tailWord_1890042) baseStart_1890042 baseEnd_1890042 := by
    simpa [prefixWord, tailWord_1890042, baseEnd_1890042] using wordTrace_append hprefix tailTrace_1890042
  have hstable : (prefixWord ++ tailWord_1890042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890042).length < 2 ^ (prefixWord ++ tailWord_1890042).sum := by decide
  have hdescent : baseEnd_1890042 < baseStart_1890042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890059 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 4, 2, 2]
def baseStart_1890059 : Nat := 118140960795 + 1890059 * 2 ^ 59
def prefixEnd_1890059 : Nat := 4983230072969 + 3 ^ 40 * 1890059 * 2
def baseEnd_1890059 : Nat := 970508732356325869170283

theorem tailTrace_1890059 : CollatzResearch.WordTrace tailWord_1890059 prefixEnd_1890059 970508732356325869170283 := by
  unfold tailWord_1890059
  simp only [CollatzResearch.WordTrace]
  refine ⟨68936115059646514223177231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45957410039764342815451487 68936115059646514223177231)
  ·
    refine ⟨103404172589469771334765847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68936115059646514223177231 103404172589469771334765847)
    ·
      refine ⟨155106258884204657002148771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103404172589469771334765847 155106258884204657002148771)
      ·
        refine ⟨232659388326306985503223157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155106258884204657002148771 232659388326306985503223157)
        ·
          refine ⟨21811817655591279890927171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232659388326306985503223157 21811817655591279890927171)
          ·
            refine ⟨32717726483386919836390757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21811817655591279890927171 32717726483386919836390757)
            ·
              refine ⟨6134573715635047469323267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32717726483386919836390757 6134573715635047469323267)
              ·
                refine ⟨9201860573452571203984901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6134573715635047469323267 9201860573452571203984901)
                ·
                  refine ⟨1725348857522357100747169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9201860573452571203984901 1725348857522357100747169)
                  ·
                    refine ⟨1294011643141767825560377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1725348857522357100747169 1294011643141767825560377)
                    ·
                      refine ⟨970508732356325869170283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294011643141767825560377 970508732356325869170283)
                      ·
                        rfl

theorem cell23_1890059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 2, 2].length) (baseStart_1890059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890059 prefixEnd_1890059 := by exact prefixLift 1890059
  have htrace : WordTrace (prefixWord ++ tailWord_1890059) baseStart_1890059 baseEnd_1890059 := by
    simpa [prefixWord, tailWord_1890059, baseEnd_1890059] using wordTrace_append hprefix tailTrace_1890059
  have hstable : (prefixWord ++ tailWord_1890059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890059).length < 2 ^ (prefixWord ++ tailWord_1890059).sum := by decide
  have hdescent : baseEnd_1890059 < baseStart_1890059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890076 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_1890076 : Nat := 118140960795 + 1890076 * 2 ^ 59
def prefixEnd_1890076 : Nat := 4983230072969 + 3 ^ 40 * 1890076 * 2
def baseEnd_1890076 : Nat := 970517461527452302657705

theorem tailTrace_1890076 : CollatzResearch.WordTrace tailWord_1890076 prefixEnd_1890076 970517461527452302657705 := by
  unfold tailWord_1890076
  simp only [CollatzResearch.WordTrace]
  refine ⟨34468367550292463063273041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45957823400389950751030721 34468367550292463063273041)
  ·
    refine ⟨25851275662719347297454781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34468367550292463063273041 25851275662719347297454781)
    ·
      refine ⟨9694228373519755236545543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25851275662719347297454781 9694228373519755236545543)
      ·
        refine ⟨14541342560279632854818315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9694228373519755236545543 14541342560279632854818315)
        ·
          refine ⟨21812013840419449282227473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14541342560279632854818315 21812013840419449282227473)
          ·
            refine ⟨16359010380314586961670605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21812013840419449282227473 16359010380314586961670605)
            ·
              refine ⟨6134628892617970110626477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16359010380314586961670605 6134628892617970110626477)
              ·
                refine ⟨2300485834731738791484929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6134628892617970110626477 2300485834731738791484929)
                ·
                  refine ⟨1725364376048804093613697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2300485834731738791484929 1725364376048804093613697)
                  ·
                    refine ⟨1294023282036603070210273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1725364376048804093613697 1294023282036603070210273)
                    ·
                      refine ⟨970517461527452302657705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294023282036603070210273 970517461527452302657705)
                      ·
                        rfl

theorem cell23_1890076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_1890076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890076 prefixEnd_1890076 := by exact prefixLift 1890076
  have htrace : WordTrace (prefixWord ++ tailWord_1890076) baseStart_1890076 baseEnd_1890076 := by
    simpa [prefixWord, tailWord_1890076, baseEnd_1890076] using wordTrace_append hprefix tailTrace_1890076
  have hstable : (prefixWord ++ tailWord_1890076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890076).length < 2 ^ (prefixWord ++ tailWord_1890076).sum := by decide
  have hdescent : baseEnd_1890076 < baseStart_1890076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890095 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 6, 5]
def baseStart_1890095 : Nat := 118140960795 + 1890095 * 2 ^ 59
def prefixEnd_1890095 : Nat := 4983230072969 + 3 ^ 40 * 1890095 * 2
def baseEnd_1890095 : Nat := 323509072553295909440039

theorem tailTrace_1890095 : CollatzResearch.WordTrace tailWord_1890095 prefixEnd_1890095 323509072553295909440039 := by
  unfold tailWord_1890095
  simp only [CollatzResearch.WordTrace]
  refine ⟨68937428087516092371487739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45958285391677394914325159 68937428087516092371487739)
  ·
    refine ⟨103406142131274138557231609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68937428087516092371487739 103406142131274138557231609)
    ·
      refine ⟨77554606598455603917923707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103406142131274138557231609 77554606598455603917923707)
      ·
        refine ⟨116331909897683405876885561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77554606598455603917923707 116331909897683405876885561)
        ·
          refine ⟨87248932423262554407664171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116331909897683405876885561 87248932423262554407664171)
          ·
            refine ⟨130873398634893831611496257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87248932423262554407664171 130873398634893831611496257)
            ·
              refine ⟨98155048976170373708622193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130873398634893831611496257 98155048976170373708622193)
              ·
                refine ⟨73616286732127780281466645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98155048976170373708622193 73616286732127780281466645)
                ·
                  refine ⟨3450763440568489700693749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73616286732127780281466645 3450763440568489700693749)
                  ·
                    refine ⟨323509072553295909440039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3450763440568489700693749 323509072553295909440039)
                    ·
                      rfl

theorem cell23_1890095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_1890095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890095 prefixEnd_1890095 := by exact prefixLift 1890095
  have htrace : WordTrace (prefixWord ++ tailWord_1890095) baseStart_1890095 baseEnd_1890095 := by
    simpa [prefixWord, tailWord_1890095, baseEnd_1890095] using wordTrace_append hprefix tailTrace_1890095
  have hstable : (prefixWord ++ tailWord_1890095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890095).length < 2 ^ (prefixWord ++ tailWord_1890095).sum := by decide
  have hdescent : baseEnd_1890095 < baseStart_1890095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890146 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1890146 : Nat := 118140960795 + 1890146 * 2 ^ 59
def prefixEnd_1890146 : Nat := 4983230072969 + 3 ^ 40 * 1890146 * 2
def baseEnd_1890146 : Nat := 323517801724422342927461

theorem tailTrace_1890146 : CollatzResearch.WordTrace tailWord_1890146 prefixEnd_1890146 323517801724422342927461 := by
  unfold tailWord_1890146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17234822052582832020398573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45959525473554218721062861 17234822052582832020398573)
  ·
    refine ⟨6463058269718562007649465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17234822052582832020398573 6463058269718562007649465)
    ·
      refine ⟨4847293702288921505737099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6463058269718562007649465 4847293702288921505737099)
      ·
        refine ⟨7270940553433382258605649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4847293702288921505737099 7270940553433382258605649)
        ·
          refine ⟨5453205415075036693954237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7270940553433382258605649 5453205415075036693954237)
          ·
            refine ⟨2044952030653138760232839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5453205415075036693954237 2044952030653138760232839)
            ·
              refine ⟨3067428045979708140349259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044952030653138760232839 3067428045979708140349259)
              ·
                refine ⟨4601142068969562210523889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067428045979708140349259 4601142068969562210523889)
                ·
                  refine ⟨3450856551727171657892917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4601142068969562210523889 3450856551727171657892917)
                  ·
                    refine ⟨323517801724422342927461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3450856551727171657892917 323517801724422342927461)
                    ·
                      rfl

theorem cell23_1890146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1890146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890146 prefixEnd_1890146 := by exact prefixLift 1890146
  have htrace : WordTrace (prefixWord ++ tailWord_1890146) baseStart_1890146 baseEnd_1890146 := by
    simpa [prefixWord, tailWord_1890146, baseEnd_1890146] using wordTrace_append hprefix tailTrace_1890146
  have hstable : (prefixWord ++ tailWord_1890146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890146).length < 2 ^ (prefixWord ++ tailWord_1890146).sum := by decide
  have hdescent : baseEnd_1890146 < baseStart_1890146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890155 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 8]
def baseStart_1890155 : Nat := 118140960795 + 1890155 * 2 ^ 59
def prefixEnd_1890155 : Nat := 4983230072969 + 3 ^ 40 * 1890155 * 2
def baseEnd_1890155 : Nat := 107839780722128610396649

theorem tailTrace_1890155 : CollatzResearch.WordTrace tailWord_1890155 prefixEnd_1890155 107839780722128610396649 := by
  unfold tailWord_1890155
  simp only [CollatzResearch.WordTrace]
  refine ⟨68939616467298722618671919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45959744311532481745781279 68939616467298722618671919)
  ·
    refine ⟨103409424700948083928007879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68939616467298722618671919 103409424700948083928007879)
    ·
      refine ⟨155114137051422125892011819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103409424700948083928007879 155114137051422125892011819)
      ·
        refine ⟨232671205577133188838017729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155114137051422125892011819 232671205577133188838017729)
        ·
          refine ⟨174503404182849891628513297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232671205577133188838017729 174503404182849891628513297)
          ·
            refine ⟨130877553137137418721384973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174503404182849891628513297 130877553137137418721384973)
            ·
              refine ⟨49079082426426532020519365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130877553137137418721384973 49079082426426532020519365)
              ·
                refine ⟨9202327954954974753847381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49079082426426532020519365 9202327954954974753847381)
                ·
                  refine ⟨107839780722128610396649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9202327954954974753847381 107839780722128610396649)
                  ·
                    rfl

theorem cell23_1890155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 8].length) (baseStart_1890155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890155 prefixEnd_1890155 := by exact prefixLift 1890155
  have htrace : WordTrace (prefixWord ++ tailWord_1890155) baseStart_1890155 baseEnd_1890155 := by
    simpa [prefixWord, tailWord_1890155, baseEnd_1890155] using wordTrace_append hprefix tailTrace_1890155
  have hstable : (prefixWord ++ tailWord_1890155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890155).length < 2 ^ (prefixWord ++ tailWord_1890155).sum := by decide
  have hdescent : baseEnd_1890155 < baseStart_1890155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890210 : List Nat := [3, 3, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_1890210 : Nat := 118140960795 + 1890210 * 2 ^ 59
def prefixEnd_1890210 : Nat := 4983230072969 + 3 ^ 40 * 1890210 * 2
def baseEnd_1890210 : Nat := 323528755978384926127363

theorem tailTrace_1890210 : CollatzResearch.WordTrace tailWord_1890210 prefixEnd_1890210 323528755978384926127363 := by
  unfold tailWord_1890210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17235405620524866752981021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45961081654732978007949389 17235405620524866752981021)
  ·
    refine ⟨6463277107696825032367883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17235405620524866752981021 6463277107696825032367883)
    ·
      refine ⟨9694915661545237548551825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6463277107696825032367883 9694915661545237548551825)
      ·
        refine ⟨7271186746158928161413869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9694915661545237548551825 7271186746158928161413869)
        ·
          refine ⟨2726695029809598060530201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7271186746158928161413869 2726695029809598060530201)
          ·
            refine ⟨2045021272357198545397651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2726695029809598060530201 2045021272357198545397651)
            ·
              refine ⟨3067531908535797818096477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045021272357198545397651 3067531908535797818096477)
              ·
                refine ⟨1150324465700924181786179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3067531908535797818096477 1150324465700924181786179)
                ·
                  refine ⟨1725486698551386272679269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150324465700924181786179 1725486698551386272679269)
                  ·
                    refine ⟨323528755978384926127363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1725486698551386272679269 323528755978384926127363)
                    ·
                      rfl

theorem cell23_1890210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_1890210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890210 prefixEnd_1890210 := by exact prefixLift 1890210
  have htrace : WordTrace (prefixWord ++ tailWord_1890210) baseStart_1890210 baseEnd_1890210 := by
    simpa [prefixWord, tailWord_1890210, baseEnd_1890210] using wordTrace_append hprefix tailTrace_1890210
  have hstable : (prefixWord ++ tailWord_1890210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890210).length < 2 ^ (prefixWord ++ tailWord_1890210).sum := by decide
  have hdescent : baseEnd_1890210 < baseStart_1890210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890249 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 2, 4]
def baseStart_1890249 : Nat := 118140960795 + 1890249 * 2 ^ 59
def prefixEnd_1890249 : Nat := 4983230072969 + 3 ^ 40 * 1890249 * 2
def baseEnd_1890249 : Nat := 323535431226893375264803

theorem tailTrace_1890249 : CollatzResearch.WordTrace tailWord_1890249 prefixEnd_1890249 323535431226893375264803 := by
  unfold tailWord_1890249
  simp only [CollatzResearch.WordTrace]
  refine ⟨68943044928958176672593801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45962029952638784448395867 68943044928958176672593801)
  ·
    refine ⟨51707283696718632504445351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68943044928958176672593801 51707283696718632504445351)
    ·
      refine ⟨77560925545077948756668027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51707283696718632504445351 77560925545077948756668027)
      ·
        refine ⟨116341388317616923135002041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77560925545077948756668027 116341388317616923135002041)
        ·
          refine ⟨87256041238212692351251531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116341388317616923135002041 87256041238212692351251531)
          ·
            refine ⟨130884061857319038526877297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87256041238212692351251531 130884061857319038526877297)
            ·
              refine ⟨98163046392989278895157973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130884061857319038526877297 98163046392989278895157973)
              ·
                refine ⟨2300696399835686224105265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98163046392989278895157973 2300696399835686224105265)
                ·
                  refine ⟨1725522299876764668078949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2300696399835686224105265 1725522299876764668078949)
                  ·
                    refine ⟨323535431226893375264803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1725522299876764668078949 323535431226893375264803)
                    ·
                      rfl

theorem cell23_1890249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 4].length) (baseStart_1890249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890249 prefixEnd_1890249 := by exact prefixLift 1890249
  have htrace : WordTrace (prefixWord ++ tailWord_1890249) baseStart_1890249 baseEnd_1890249 := by
    simpa [prefixWord, tailWord_1890249, baseEnd_1890249] using wordTrace_append hprefix tailTrace_1890249
  have hstable : (prefixWord ++ tailWord_1890249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890249).length < 2 ^ (prefixWord ++ tailWord_1890249).sum := by decide
  have hdescent : baseEnd_1890249 < baseStart_1890249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890256 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 3, 2, 2]
def baseStart_1890256 : Nat := 118140960795 + 1890256 * 2 ^ 59
def prefixEnd_1890256 : Nat := 4983230072969 + 3 ^ 40 * 1890256 * 2
def baseEnd_1890256 : Nat := 970609888045261598406877

theorem tailTrace_1890256 : CollatzResearch.WordTrace tailWord_1890256 prefixEnd_1890256 970609888045261598406877 := by
  unfold tailWord_1890256
  simp only [CollatzResearch.WordTrace]
  refine ⟨34471650119966408434049311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45962200159955211245399081 34471650119966408434049311)
  ·
    refine ⟨51707475179949612651073967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34471650119966408434049311 51707475179949612651073967)
    ·
      refine ⟨77561212769924418976610951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51707475179949612651073967 77561212769924418976610951)
      ·
        refine ⟨116341819154886628464916427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77561212769924418976610951 116341819154886628464916427)
        ·
          refine ⟨174512728732329942697374641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116341819154886628464916427 174512728732329942697374641)
          ·
            refine ⟨130884546549247457023030981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174512728732329942697374641 130884546549247457023030981)
            ·
              refine ⟨24540852477983898191818309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130884546549247457023030981 24540852477983898191818309)
              ·
                refine ⟨4601409839621980910965933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24540852477983898191818309 4601409839621980910965933)
                ·
                  refine ⟨1725528689858242841612225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4601409839621980910965933 1725528689858242841612225)
                  ·
                    refine ⟨1294146517393682131209169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1725528689858242841612225 1294146517393682131209169)
                    ·
                      refine ⟨970609888045261598406877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294146517393682131209169 970609888045261598406877)
                      ·
                        rfl

theorem cell23_1890256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3, 2, 2].length) (baseStart_1890256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890256 prefixEnd_1890256 := by exact prefixLift 1890256
  have htrace : WordTrace (prefixWord ++ tailWord_1890256) baseStart_1890256 baseEnd_1890256 := by
    simpa [prefixWord, tailWord_1890256, baseEnd_1890256] using wordTrace_append hprefix tailTrace_1890256
  have hstable : (prefixWord ++ tailWord_1890256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890256).length < 2 ^ (prefixWord ++ tailWord_1890256).sum := by decide
  have hdescent : baseEnd_1890256 < baseStart_1890256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890279 : List Nat := [1, 1, 5, 2, 4, 10]
def baseStart_1890279 : Nat := 118140960795 + 1890279 * 2 ^ 59
def prefixEnd_1890279 : Nat := 4983230072969 + 3 ^ 40 * 1890279 * 2
def baseEnd_1890279 : Nat := 3994327975721460939997

theorem tailTrace_1890279 : CollatzResearch.WordTrace tailWord_1890279 prefixEnd_1890279 3994327975721460939997 := by
  unfold tailWord_1890279
  simp only [CollatzResearch.WordTrace]
  refine ⟨68944139118849491796185891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45962759412566327864123927 68944139118849491796185891)
  ·
    refine ⟨103416208678274237694278837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68944139118849491796185891 103416208678274237694278837)
    ·
      refine ⟨9695269563588209783838641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103416208678274237694278837 9695269563588209783838641)
      ·
        refine ⟨7271452172691157337878981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9695269563588209783838641 7271452172691157337878981)
        ·
          refine ⟨1363397282379592000852309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7271452172691157337878981 1363397282379592000852309)
          ·
            refine ⟨3994327975721460939997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1363397282379592000852309 3994327975721460939997)
            ·
              rfl

theorem cell23_1890279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 10].length) (baseStart_1890279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890279 prefixEnd_1890279 := by exact prefixLift 1890279
  have htrace : WordTrace (prefixWord ++ tailWord_1890279) baseStart_1890279 baseEnd_1890279 := by
    simpa [prefixWord, tailWord_1890279, baseEnd_1890279] using wordTrace_append hprefix tailTrace_1890279
  have hstable : (prefixWord ++ tailWord_1890279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890279).length < 2 ^ (prefixWord ++ tailWord_1890279).sum := by decide
  have hdescent : baseEnd_1890279 < baseStart_1890279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890316 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 3, 3, 2]
def baseStart_1890316 : Nat := 118140960795 + 1890316 * 2 ^ 59
def prefixEnd_1890316 : Nat := 4983230072969 + 3 ^ 40 * 1890316 * 2
def baseEnd_1890316 : Nat := 970640696884531363656601

theorem tailTrace_1890316 : CollatzResearch.WordTrace tailWord_1890316 prefixEnd_1890316 970640696884531363656601 := by
  unfold tailWord_1890316
  simp only [CollatzResearch.WordTrace]
  refine ⟨34472744309857723557641401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45963659079810298076855201 34472744309857723557641401)
  ·
    refine ⟨25854558232393292668231051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34472744309857723557641401 25854558232393292668231051)
    ·
      refine ⟨38781837348589939002346577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25854558232393292668231051 38781837348589939002346577)
      ·
        refine ⟨29086378011442454251759933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38781837348589939002346577 29086378011442454251759933)
        ·
          refine ⟨10907391754290920344409975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29086378011442454251759933 10907391754290920344409975)
          ·
            refine ⟨16361087631436380516614963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10907391754290920344409975 16361087631436380516614963)
            ·
              refine ⟨24541631447154570774922445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16361087631436380516614963 24541631447154570774922445)
              ·
                refine ⟨9203111792682964040595917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24541631447154570774922445 9203111792682964040595917)
                ·
                  refine ⟨3451166922256111515223469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9203111792682964040595917 3451166922256111515223469)
                  ·
                    refine ⟨1294187595846041818208801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451166922256111515223469 1294187595846041818208801)
                    ·
                      refine ⟨970640696884531363656601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294187595846041818208801 970640696884531363656601)
                      ·
                        rfl

theorem cell23_1890316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_1890316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890316 prefixEnd_1890316 := by exact prefixLift 1890316
  have htrace : WordTrace (prefixWord ++ tailWord_1890316) baseStart_1890316 baseEnd_1890316 := by
    simpa [prefixWord, tailWord_1890316, baseEnd_1890316] using wordTrace_append hprefix tailTrace_1890316
  have hstable : (prefixWord ++ tailWord_1890316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890316).length < 2 ^ (prefixWord ++ tailWord_1890316).sum := by decide
  have hdescent : baseEnd_1890316 < baseStart_1890316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890324 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_1890324 : Nat := 118140960795 + 1890324 * 2 ^ 59
def prefixEnd_1890324 : Nat := 4983230072969 + 3 ^ 40 * 1890324 * 2
def baseEnd_1890324 : Nat := 970644804729767332356565

theorem tailTrace_1890324 : CollatzResearch.WordTrace tailWord_1890324 prefixEnd_1890324 970644804729767332356565 := by
  unfold tailWord_1890324
  simp only [CollatzResearch.WordTrace]
  refine ⟨34472890201843232240787013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45963853602457642987716017 34472890201843232240787013)
  ·
    refine ⟨6463666912845606045147565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34472890201843232240787013 6463666912845606045147565)
    ·
      refine ⟨2423875092317102266930337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6463666912845606045147565 2423875092317102266930337)
      ·
        refine ⟨1817906319237826700197753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2423875092317102266930337 1817906319237826700197753)
        ·
          refine ⟨1363429739428370025148315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1817906319237826700197753 1363429739428370025148315)
          ·
            refine ⟨2045144609142555037722473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363429739428370025148315 2045144609142555037722473)
            ·
              refine ⟨1533858456856916278291855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2045144609142555037722473 1533858456856916278291855)
              ·
                refine ⟨2300787685285374417437783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533858456856916278291855 2300787685285374417437783)
                ·
                  refine ⟨3451181527928061626156675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300787685285374417437783 3451181527928061626156675)
                  ·
                    refine ⟨5176772291892092439235013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3451181527928061626156675 5176772291892092439235013)
                    ·
                      refine ⟨970644804729767332356565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5176772291892092439235013 970644804729767332356565)
                      ·
                        rfl

theorem cell23_1890324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_1890324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890324 prefixEnd_1890324 := by exact prefixLift 1890324
  have htrace : WordTrace (prefixWord ++ tailWord_1890324) baseStart_1890324 baseEnd_1890324 := by
    simpa [prefixWord, tailWord_1890324, baseEnd_1890324] using wordTrace_append hprefix tailTrace_1890324
  have hstable : (prefixWord ++ tailWord_1890324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890324).length < 2 ^ (prefixWord ++ tailWord_1890324).sum := by decide
  have hdescent : baseEnd_1890324 < baseStart_1890324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890327 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 1, 2, 3]
def baseStart_1890327 : Nat := 118140960795 + 1890327 * 2 ^ 59
def prefixEnd_1890327 : Nat := 4983230072969 + 3 ^ 40 * 1890327 * 2
def baseEnd_1890327 : Nat := 970646345171730820619051

theorem tailTrace_1890327 : CollatzResearch.WordTrace tailWord_1890327 prefixEnd_1890327 970646345171730820619051 := by
  unfold tailWord_1890327
  simp only [CollatzResearch.WordTrace]
  refine ⟨68945889822675595993933235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45963926548450397329288823 68945889822675595993933235)
  ·
    refine ⟨103418834734013393990899853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68945889822675595993933235 103418834734013393990899853)
    ·
      refine ⟨38782063025255022746587445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103418834734013393990899853 38782063025255022746587445)
      ·
        refine ⟨3635818408617658382492573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38782063025255022746587445 3635818408617658382492573)
        ·
          refine ⟨1363431903231621893434715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3635818408617658382492573 1363431903231621893434715)
          ·
            refine ⟨2045147854847432840152073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363431903231621893434715 2045147854847432840152073)
            ·
              refine ⟨1533860891135574630114055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2045147854847432840152073 1533860891135574630114055)
              ·
                refine ⟨2300791336703361945171083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533860891135574630114055 2300791336703361945171083)
                ·
                  refine ⟨3451187005055042917756625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300791336703361945171083 3451187005055042917756625)
                  ·
                    refine ⟨2588390253791282188317469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3451187005055042917756625 2588390253791282188317469)
                    ·
                      refine ⟨970646345171730820619051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2588390253791282188317469 970646345171730820619051)
                      ·
                        rfl

theorem cell23_1890327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_1890327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890327 prefixEnd_1890327 := by exact prefixLift 1890327
  have htrace : WordTrace (prefixWord ++ tailWord_1890327) baseStart_1890327 baseEnd_1890327 := by
    simpa [prefixWord, tailWord_1890327, baseEnd_1890327] using wordTrace_append hprefix tailTrace_1890327
  have hstable : (prefixWord ++ tailWord_1890327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890327).length < 2 ^ (prefixWord ++ tailWord_1890327).sum := by decide
  have hdescent : baseEnd_1890327 < baseStart_1890327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890359 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_1890359 : Nat := 118140960795 + 1890359 * 2 ^ 59
def prefixEnd_1890359 : Nat := 4983230072969 + 3 ^ 40 * 1890359 * 2
def baseEnd_1890359 : Nat := 970662776552674695418903

theorem tailTrace_1890359 : CollatzResearch.WordTrace tailWord_1890359 prefixEnd_1890359 970662776552674695418903 := by
  unfold tailWord_1890359
  simp only [CollatzResearch.WordTrace]
  refine ⟨68947056958559665459098131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45964704639039776972732087 68947056958559665459098131)
  ·
    refine ⟨103420585437839498188647197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68947056958559665459098131 103420585437839498188647197)
    ·
      refine ⟨38782719539189811820742699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103420585437839498188647197 38782719539189811820742699)
      ·
        refine ⟨58174079308784717731114049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38782719539189811820742699 58174079308784717731114049)
        ·
          refine ⟨43630559481588538298335537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58174079308784717731114049 43630559481588538298335537)
          ·
            refine ⟨32722919611191403723751653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43630559481588538298335537 32722919611191403723751653)
            ·
              refine ⟨6135547427098388198203435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32722919611191403723751653 6135547427098388198203435)
              ·
                refine ⟨9203321140647582297305153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6135547427098388198203435 9203321140647582297305153)
                ·
                  refine ⟨6902490855485686722978865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9203321140647582297305153 6902490855485686722978865)
                  ·
                    refine ⟨5176868141614265042234149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6902490855485686722978865 5176868141614265042234149)
                    ·
                      refine ⟨970662776552674695418903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5176868141614265042234149 970662776552674695418903)
                      ·
                        rfl

theorem cell23_1890359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_1890359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890359 prefixEnd_1890359 := by exact prefixLift 1890359
  have htrace : WordTrace (prefixWord ++ tailWord_1890359) baseStart_1890359 baseEnd_1890359 := by
    simpa [prefixWord, tailWord_1890359, baseEnd_1890359] using wordTrace_append hprefix tailTrace_1890359
  have hstable : (prefixWord ++ tailWord_1890359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890359).length < 2 ^ (prefixWord ++ tailWord_1890359).sum := by decide
  have hdescent : baseEnd_1890359 < baseStart_1890359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890409 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 5]
def baseStart_1890409 : Nat := 118140960795 + 1890409 * 2 ^ 59
def prefixEnd_1890409 : Nat := 4983230072969 + 3 ^ 40 * 1890409 * 2
def baseEnd_1890409 : Nat := 970688450585399499793673

theorem tailTrace_1890409 : CollatzResearch.WordTrace tailWord_1890409 prefixEnd_1890409 970688450585399499793673 := by
  unfold tailWord_1890409
  simp only [CollatzResearch.WordTrace]
  refine ⟨68948880608378523998418281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45965920405585682665612187 68948880608378523998418281)
  ·
    refine ⟨51711660456283892998813711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68948880608378523998418281 51711660456283892998813711)
    ·
      refine ⟨77567490684425839498220567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51711660456283892998813711 77567490684425839498220567)
      ·
        refine ⟨116351236026638759247330851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77567490684425839498220567 116351236026638759247330851)
        ·
          refine ⟨174526854039958138870996277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116351236026638759247330851 174526854039958138870996277)
          ·
            refine ⟨16361892566246075519155901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174526854039958138870996277 16361892566246075519155901)
            ·
              refine ⟨6135709712342278319683463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16361892566246075519155901 6135709712342278319683463)
              ·
                refine ⟨9203564568513417479525195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6135709712342278319683463 9203564568513417479525195)
                ·
                  refine ⟨13805346852770126219287793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9203564568513417479525195 13805346852770126219287793)
                  ·
                    refine ⟨10354010139577594664465845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13805346852770126219287793 10354010139577594664465845)
                    ·
                      refine ⟨970688450585399499793673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10354010139577594664465845 970688450585399499793673)
                      ·
                        rfl

theorem cell23_1890409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_1890409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890409 prefixEnd_1890409 := by exact prefixLift 1890409
  have htrace : WordTrace (prefixWord ++ tailWord_1890409) baseStart_1890409 baseEnd_1890409 := by
    simpa [prefixWord, tailWord_1890409, baseEnd_1890409] using wordTrace_append hprefix tailTrace_1890409
  have hstable : (prefixWord ++ tailWord_1890409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890409).length < 2 ^ (prefixWord ++ tailWord_1890409).sum := by decide
  have hdescent : baseEnd_1890409 < baseStart_1890409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890433 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 2, 5]
def baseStart_1890433 : Nat := 118140960795 + 1890433 * 2 ^ 59
def prefixEnd_1890433 : Nat := 4983230072969 + 3 ^ 40 * 1890433 * 2
def baseEnd_1890433 : Nat := 323566924707035801964521

theorem tailTrace_1890433 : CollatzResearch.WordTrace tailWord_1890433 prefixEnd_1890433 323566924707035801964521 := by
  unfold tailWord_1890433
  simp only [CollatzResearch.WordTrace]
  refine ⟨68949755960291576097291953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45966503973527717398194635 68949755960291576097291953)
  ·
    refine ⟨51712316970218682072968965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68949755960291576097291953 51712316970218682072968965)
    ·
      refine ⟨9696059431916002888681681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51712316970218682072968965 9696059431916002888681681)
      ·
        refine ⟨7272044573937002166511261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9696059431916002888681681 7272044573937002166511261)
        ·
          refine ⟨2727016715226375812441723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7272044573937002166511261 2727016715226375812441723)
          ·
            refine ⟨4090525072839563718662585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727016715226375812441723 4090525072839563718662585)
            ·
              refine ⟨3067893804629672788996939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4090525072839563718662585 3067893804629672788996939)
              ·
                refine ⟨4601840706944509183495409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067893804629672788996939 4601840706944509183495409)
                ·
                  refine ⟨3451380530208381887621557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4601840706944509183495409 3451380530208381887621557)
                  ·
                    refine ⟨323566924707035801964521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3451380530208381887621557 323566924707035801964521)
                    ·
                      rfl

theorem cell23_1890433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_1890433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890433 prefixEnd_1890433 := by exact prefixLift 1890433
  have htrace : WordTrace (prefixWord ++ tailWord_1890433) baseStart_1890433 baseEnd_1890433 := by
    simpa [prefixWord, tailWord_1890433, baseEnd_1890433] using wordTrace_append hprefix tailTrace_1890433
  have hstable : (prefixWord ++ tailWord_1890433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890433).length < 2 ^ (prefixWord ++ tailWord_1890433).sum := by decide
  have hdescent : baseEnd_1890433 < baseStart_1890433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890484 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1890484 : Nat := 118140960795 + 1890484 * 2 ^ 59
def prefixEnd_1890484 : Nat := 4983230072969 + 3 ^ 40 * 1890484 * 2
def baseEnd_1890484 : Nat := 323575653878162235451943

theorem tailTrace_1890484 : CollatzResearch.WordTrace tailWord_1890484 prefixEnd_1890484 323575653878162235451943 := by
  unfold tailWord_1890484
  simp only [CollatzResearch.WordTrace]
  refine ⟨34475808041553405903699253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45967744055404541204932337 34475808041553405903699253)
  ·
    refine ⟨3232107003895631803471805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34475808041553405903699253 3232107003895631803471805)
    ·
      refine ⟨1212040126460861926301927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3232107003895631803471805 1212040126460861926301927)
      ·
        refine ⟨1818060189691292889452891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212040126460861926301927 1818060189691292889452891)
        ·
          refine ⟨2727090284536939334179337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818060189691292889452891 2727090284536939334179337)
          ·
            refine ⟨2045317713402704500634503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2727090284536939334179337 2045317713402704500634503)
            ·
              refine ⟨3067976570104056750951755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045317713402704500634503 3067976570104056750951755)
              ·
                refine ⟨4601964855156085126427633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067976570104056750951755 4601964855156085126427633)
                ·
                  refine ⟨3451473641367063844820725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4601964855156085126427633 3451473641367063844820725)
                  ·
                    refine ⟨323575653878162235451943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3451473641367063844820725 323575653878162235451943)
                    ·
                      rfl

theorem cell23_1890484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1890484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890484 prefixEnd_1890484 := by exact prefixLift 1890484
  have htrace : WordTrace (prefixWord ++ tailWord_1890484) baseStart_1890484 baseEnd_1890484 := by
    simpa [prefixWord, tailWord_1890484, baseEnd_1890484] using wordTrace_append hprefix tailTrace_1890484
  have hstable : (prefixWord ++ tailWord_1890484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890484).length < 2 ^ (prefixWord ++ tailWord_1890484).sum := by decide
  have hdescent : baseEnd_1890484 < baseStart_1890484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890513 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 2, 3, 2]
def baseStart_1890513 : Nat := 118140960795 + 1890513 * 2 ^ 59
def prefixEnd_1890513 : Nat := 4983230072969 + 3 ^ 40 * 1890513 * 2
def baseEnd_1890513 : Nat := 970741852573467092893195

theorem tailTrace_1890513 : CollatzResearch.WordTrace tailWord_1890513 prefixEnd_1890513 970741852573467092893195 := by
  unfold tailWord_1890513
  simp only [CollatzResearch.WordTrace]
  refine ⟨68952673800001749760204193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45968449200001166506802795 68952673800001749760204193)
  ·
    refine ⟨51714505350001312320153145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68952673800001749760204193 51714505350001312320153145)
    ·
      refine ⟨38785879012500984240114859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51714505350001312320153145 38785879012500984240114859)
      ·
        refine ⟨58178818518751476360172289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38785879012500984240114859 58178818518751476360172289)
        ·
          refine ⟨43634113889063607270129217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58178818518751476360172289 43634113889063607270129217)
          ·
            refine ⟨32725585416797705452596913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43634113889063607270129217 32725585416797705452596913)
            ·
              refine ⟨24544189062598279089447685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32725585416797705452596913 24544189062598279089447685)
              ·
                refine ⟨4602035449237177329271441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24544189062598279089447685 4602035449237177329271441)
                ·
                  refine ⟨3451526586927882996953581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4602035449237177329271441 3451526586927882996953581)
                  ·
                    refine ⟨1294322470097956123857593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451526586927882996953581 1294322470097956123857593)
                    ·
                      refine ⟨970741852573467092893195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294322470097956123857593 970741852573467092893195)
                      ·
                        rfl

theorem cell23_1890513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 3, 2].length) (baseStart_1890513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890513 prefixEnd_1890513 := by exact prefixLift 1890513
  have htrace : WordTrace (prefixWord ++ tailWord_1890513) baseStart_1890513 baseEnd_1890513 := by
    simpa [prefixWord, tailWord_1890513, baseEnd_1890513] using wordTrace_append hprefix tailTrace_1890513
  have hstable : (prefixWord ++ tailWord_1890513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890513).length < 2 ^ (prefixWord ++ tailWord_1890513).sum := by decide
  have hdescent : baseEnd_1890513 < baseStart_1890513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890520 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 3, 1, 3]
def baseStart_1890520 : Nat := 118140960795 + 1890520 * 2 ^ 59
def prefixEnd_1890520 : Nat := 4983230072969 + 3 ^ 40 * 1890520 * 2
def baseEnd_1890520 : Nat := 970745446938048565505663

theorem tailTrace_1890520 : CollatzResearch.WordTrace tailWord_1890520 prefixEnd_1890520 970745446938048565505663 := by
  unfold tailWord_1890520
  simp only [CollatzResearch.WordTrace]
  refine ⟨34476464555488194977854507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45968619407317593303806009 34476464555488194977854507)
  ·
    refine ⟨51714696833232292466781761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34476464555488194977854507 51714696833232292466781761)
    ·
      refine ⟨38786022624924219350086321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51714696833232292466781761 38786022624924219350086321)
      ·
        refine ⟨29089516968693164512564741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38786022624924219350086321 29089516968693164512564741)
        ·
          refine ⟨5454284431629968346105889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29089516968693164512564741 5454284431629968346105889)
          ·
            refine ⟨4090713323722476259579417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5454284431629968346105889 4090713323722476259579417)
            ·
              refine ⟨3068034992791857194684563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4090713323722476259579417 3068034992791857194684563)
              ·
                refine ⟨4602052489187785792026845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068034992791857194684563 4602052489187785792026845)
                ·
                  refine ⟨1725769683445419672010067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4602052489187785792026845 1725769683445419672010067)
                  ·
                    refine ⟨2588654525168129508015101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1725769683445419672010067 2588654525168129508015101)
                    ·
                      refine ⟨970745446938048565505663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2588654525168129508015101 970745446938048565505663)
                      ·
                        rfl

theorem cell23_1890520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_1890520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890520 prefixEnd_1890520 := by exact prefixLift 1890520
  have htrace : WordTrace (prefixWord ++ tailWord_1890520) baseStart_1890520 baseEnd_1890520 := by
    simpa [prefixWord, tailWord_1890520, baseEnd_1890520] using wordTrace_append hprefix tailTrace_1890520
  have hstable : (prefixWord ++ tailWord_1890520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890520).length < 2 ^ (prefixWord ++ tailWord_1890520).sum := by decide
  have hdescent : baseEnd_1890520 < baseStart_1890520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890543 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 4]
def baseStart_1890543 : Nat := 118140960795 + 1890543 * 2 ^ 59
def prefixEnd_1890543 : Nat := 4983230072969 + 3 ^ 40 * 1890543 * 2
def baseEnd_1890543 : Nat := 970757256993101975518057

theorem tailTrace_1890543 : CollatzResearch.WordTrace tailWord_1890543 prefixEnd_1890543 970757256993101975518057 := by
  unfold tailWord_1890543
  simp only [CollatzResearch.WordTrace]
  refine ⟨68953767989893064883796283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45969178659928709922530855 68953767989893064883796283)
  ·
    refine ⟨103430651984839597325694425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68953767989893064883796283 103430651984839597325694425)
    ·
      refine ⟨77572988988629697994270819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103430651984839597325694425 77572988988629697994270819)
      ·
        refine ⟨116359483482944546991406229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77572988988629697994270819 116359483482944546991406229)
        ·
          refine ⟨5454350788263025640222167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116359483482944546991406229 5454350788263025640222167)
          ·
            refine ⟨8181526182394538460333251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454350788263025640222167 8181526182394538460333251)
            ·
              refine ⟨12272289273591807690499877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8181526182394538460333251 12272289273591807690499877)
              ·
                refine ⟨2301054238798463941968727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12272289273591807690499877 2301054238798463941968727)
                ·
                  refine ⟨3451581358197695912953091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301054238798463941968727 3451581358197695912953091)
                  ·
                    refine ⟨5177372037296543869429637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3451581358197695912953091 5177372037296543869429637)
                    ·
                      refine ⟨970757256993101975518057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5177372037296543869429637 970757256993101975518057)
                      ·
                        rfl

theorem cell23_1890543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 4].length) (baseStart_1890543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890543 prefixEnd_1890543 := by exact prefixLift 1890543
  have htrace : WordTrace (prefixWord ++ tailWord_1890543) baseStart_1890543 baseEnd_1890543 := by
    simpa [prefixWord, tailWord_1890543, baseEnd_1890543] using wordTrace_append hprefix tailTrace_1890543
  have hstable : (prefixWord ++ tailWord_1890543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890543).length < 2 ^ (prefixWord ++ tailWord_1890543).sum := by decide
  have hdescent : baseEnd_1890543 < baseStart_1890543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890563 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 1, 2, 3]
def baseStart_1890563 : Nat := 118140960795 + 1890563 * 2 ^ 59
def prefixEnd_1890563 : Nat := 4983230072969 + 3 ^ 40 * 1890563 * 2
def baseEnd_1890563 : Nat := 970767526606191897267965

theorem tailTrace_1890563 : CollatzResearch.WordTrace tailWord_1890563 prefixEnd_1890563 970767526606191897267965 := by
  unfold tailWord_1890563
  simp only [CollatzResearch.WordTrace]
  refine ⟨68954497449820608299524343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45969664966547072199682895 68954497449820608299524343)
  ·
    refine ⟨103431746174730912449286515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68954497449820608299524343 103431746174730912449286515)
    ·
      refine ⟨155147619262096368673929773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103431746174730912449286515 155147619262096368673929773)
      ·
        refine ⟨58180357223286138252723665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155147619262096368673929773 58180357223286138252723665)
        ·
          refine ⟨43635267917464603689542749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58180357223286138252723665 43635267917464603689542749)
          ·
            refine ⟨16363225469049226383578531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43635267917464603689542749 16363225469049226383578531)
            ·
              refine ⟨24544838203573839575367797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16363225469049226383578531 24544838203573839575367797)
              ·
                refine ⟨2301078581585047460190731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24544838203573839575367797 2301078581585047460190731)
                ·
                  refine ⟨3451617872377571190286097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301078581585047460190731 3451617872377571190286097)
                  ·
                    refine ⟨2588713404283178392714573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3451617872377571190286097 2588713404283178392714573)
                    ·
                      refine ⟨970767526606191897267965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2588713404283178392714573 970767526606191897267965)
                      ·
                        rfl

theorem cell23_1890563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_1890563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890563 prefixEnd_1890563 := by exact prefixLift 1890563
  have htrace : WordTrace (prefixWord ++ tailWord_1890563) baseStart_1890563 baseEnd_1890563 := by
    simpa [prefixWord, tailWord_1890563, baseEnd_1890563] using wordTrace_append hprefix tailTrace_1890563
  have hstable : (prefixWord ++ tailWord_1890563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890563).length < 2 ^ (prefixWord ++ tailWord_1890563).sum := by decide
  have hdescent : baseEnd_1890563 < baseStart_1890563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890577 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 3, 2, 2]
def baseStart_1890577 : Nat := 118140960795 + 1890577 * 2 ^ 59
def prefixEnd_1890577 : Nat := 4983230072969 + 3 ^ 40 * 1890577 * 2
def baseEnd_1890577 : Nat := 970774715335354842492901

theorem tailTrace_1890577 : CollatzResearch.WordTrace tailWord_1890577 prefixEnd_1890577 970774715335354842492901 := by
  unfold tailWord_1890577
  simp only [CollatzResearch.WordTrace]
  refine ⟨68955008071769888690533985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45970005381179925793689323 68955008071769888690533985)
  ·
    refine ⟨51716256053827416517900489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68955008071769888690533985 51716256053827416517900489)
    ·
      refine ⟨38787192040370562388425367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51716256053827416517900489 38787192040370562388425367)
      ·
        refine ⟨58180788060555843582638051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38787192040370562388425367 58180788060555843582638051)
        ·
          refine ⟨87271182090833765373957077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58180788060555843582638051 87271182090833765373957077)
          ·
            refine ⟨2045418330253916375952119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 87271182090833765373957077 2045418330253916375952119)
            ·
              refine ⟨3068127495380874563928179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045418330253916375952119 3068127495380874563928179)
              ·
                refine ⟨4602191243071311845892269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068127495380874563928179 4602191243071311845892269)
                ·
                  refine ⟨1725821716151741942209601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4602191243071311845892269 1725821716151741942209601)
                  ·
                    refine ⟨1294366287113806456657201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1725821716151741942209601 1294366287113806456657201)
                    ·
                      refine ⟨970774715335354842492901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294366287113806456657201 970774715335354842492901)
                      ·
                        rfl

theorem cell23_1890577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 2, 2].length) (baseStart_1890577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890577 prefixEnd_1890577 := by exact prefixLift 1890577
  have htrace : WordTrace (prefixWord ++ tailWord_1890577) baseStart_1890577 baseEnd_1890577 := by
    simpa [prefixWord, tailWord_1890577, baseEnd_1890577] using wordTrace_append hprefix tailTrace_1890577
  have hstable : (prefixWord ++ tailWord_1890577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890577).length < 2 ^ (prefixWord ++ tailWord_1890577).sum := by decide
  have hdescent : baseEnd_1890577 < baseStart_1890577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890590 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1890590 : Nat := 118140960795 + 1890590 * 2 ^ 59
def prefixEnd_1890590 : Nat := 4983230072969 + 3 ^ 40 * 1890590 * 2
def baseEnd_1890590 : Nat := 970781390583863291630341

theorem tailTrace_1890590 : CollatzResearch.WordTrace tailWord_1890590 prefixEnd_1890590 970781390583863291630341 := by
  unfold tailWord_1890590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8619435277590348988844653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45970321480481861273838149 8619435277590348988844653)
  ·
    refine ⟨3232288229096380870816745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8619435277590348988844653 3232288229096380870816745)
    ·
      refine ⟨2424216171822285653112559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3232288229096380870816745 2424216171822285653112559)
      ·
        refine ⟨3636324257733428479668839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424216171822285653112559 3636324257733428479668839)
        ·
          refine ⟨5454486386600142719503259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636324257733428479668839 5454486386600142719503259)
          ·
            refine ⟨8181729579900214079254889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454486386600142719503259 8181729579900214079254889)
            ·
              refine ⟨6136297184925160559441167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8181729579900214079254889 6136297184925160559441167)
              ·
                refine ⟨9204445777387740839161751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6136297184925160559441167 9204445777387740839161751)
                ·
                  refine ⟨13806668666081611258742627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9204445777387740839161751 13806668666081611258742627)
                  ·
                    refine ⟨20710002999122416888113941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13806668666081611258742627 20710002999122416888113941)
                    ·
                      refine ⟨970781390583863291630341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20710002999122416888113941 970781390583863291630341)
                      ·
                        rfl

theorem cell23_1890590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1890590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890590 prefixEnd_1890590 := by exact prefixLift 1890590
  have htrace : WordTrace (prefixWord ++ tailWord_1890590) baseStart_1890590 baseEnd_1890590 := by
    simpa [prefixWord, tailWord_1890590, baseEnd_1890590] using wordTrace_append hprefix tailTrace_1890590
  have hstable : (prefixWord ++ tailWord_1890590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890590).length < 2 ^ (prefixWord ++ tailWord_1890590).sum := by decide
  have hdescent : baseEnd_1890590 < baseStart_1890590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890597 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 1, 2, 3]
def baseStart_1890597 : Nat := 118140960795 + 1890597 * 2 ^ 59
def prefixEnd_1890597 : Nat := 4983230072969 + 3 ^ 40 * 1890597 * 2
def baseEnd_1890597 : Nat := 970784984948444764242809

theorem tailTrace_1890597 : CollatzResearch.WordTrace tailWord_1890597 prefixEnd_1890597 970784984948444764242809 := by
  unfold tailWord_1890597
  simp only [CollatzResearch.WordTrace]
  refine ⟨68955737531697432106262045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45970491687798288070841363 68955737531697432106262045)
  ·
    refine ⟨25858401574386537039848267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68955737531697432106262045 25858401574386537039848267)
    ·
      refine ⟨38787602361579805559772401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25858401574386537039848267 38787602361579805559772401)
      ·
        refine ⟨29090701771184854169829301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38787602361579805559772401 29090701771184854169829301)
        ·
          refine ⟨2727253291048580078421497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29090701771184854169829301 2727253291048580078421497)
          ·
            refine ⟨2045439968286435058816123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2727253291048580078421497 2045439968286435058816123)
            ·
              refine ⟨3068159952429652588224185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045439968286435058816123 3068159952429652588224185)
              ·
                refine ⟨2301119964322239441168139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068159952429652588224185 2301119964322239441168139)
                ·
                  refine ⟨3451679946483359161752209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301119964322239441168139 3451679946483359161752209)
                  ·
                    refine ⟨2588759959862519371314157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3451679946483359161752209 2588759959862519371314157)
                    ·
                      refine ⟨970784984948444764242809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2588759959862519371314157 970784984948444764242809)
                      ·
                        rfl

theorem cell23_1890597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_1890597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890597 prefixEnd_1890597 := by exact prefixLift 1890597
  have htrace : WordTrace (prefixWord ++ tailWord_1890597) baseStart_1890597 baseEnd_1890597 := by
    simpa [prefixWord, tailWord_1890597, baseEnd_1890597] using wordTrace_append hprefix tailTrace_1890597
  have hstable : (prefixWord ++ tailWord_1890597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890597).length < 2 ^ (prefixWord ++ tailWord_1890597).sum := by decide
  have hdescent : baseEnd_1890597 < baseStart_1890597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890610 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_1890610 : Nat := 118140960795 + 1890610 * 2 ^ 59
def prefixEnd_1890610 : Nat := 4983230072969 + 3 ^ 40 * 1890610 * 2
def baseEnd_1890610 : Nat := 970791660196953213380249

theorem tailTrace_1890610 : CollatzResearch.WordTrace tailWord_1890610 prefixEnd_1890610 970791660196953213380249 := by
  unfold tailWord_1890610
  simp only [CollatzResearch.WordTrace]
  refine ⟨17239052920162583831621321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45970807787100223550990189 17239052920162583831621321)
  ·
    refine ⟨12929289690121937873715991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17239052920162583831621321 12929289690121937873715991)
    ·
      refine ⟨19393934535182906810573987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12929289690121937873715991 19393934535182906810573987)
      ·
        refine ⟨29090901802774360215860981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19393934535182906810573987 29090901802774360215860981)
        ·
          refine ⟨2727272044010096270236967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29090901802774360215860981 2727272044010096270236967)
          ·
            refine ⟨4090908066015144405355451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727272044010096270236967 4090908066015144405355451)
            ·
              refine ⟨6136362099022716608033177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090908066015144405355451 6136362099022716608033177)
              ·
                refine ⟨4602271574267037456024883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6136362099022716608033177 4602271574267037456024883)
                ·
                  refine ⟨6903407361400556184037325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602271574267037456024883 6903407361400556184037325)
                  ·
                    refine ⟨2588777760525208569013997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6903407361400556184037325 2588777760525208569013997)
                    ·
                      refine ⟨970791660196953213380249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2588777760525208569013997 970791660196953213380249)
                      ·
                        rfl

theorem cell23_1890610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_1890610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890610 prefixEnd_1890610 := by exact prefixLift 1890610
  have htrace : WordTrace (prefixWord ++ tailWord_1890610) baseStart_1890610 baseEnd_1890610 := by
    simpa [prefixWord, tailWord_1890610, baseEnd_1890610] using wordTrace_append hprefix tailTrace_1890610
  have hstable : (prefixWord ++ tailWord_1890610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890610).length < 2 ^ (prefixWord ++ tailWord_1890610).sum := by decide
  have hdescent : baseEnd_1890610 < baseStart_1890610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890633 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 5, 4, 2]
def baseStart_1890633 : Nat := 118140960795 + 1890633 * 2 ^ 59
def prefixEnd_1890633 : Nat := 4983230072969 + 3 ^ 40 * 1890633 * 2
def baseEnd_1890633 : Nat := 970803470252006623392643

theorem tailTrace_1890633 : CollatzResearch.WordTrace tailWord_1890633 prefixEnd_1890633 970803470252006623392643 := by
  unfold tailWord_1890633
  simp only [CollatzResearch.WordTrace]
  refine ⟨68957050559567010254572553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45971367039711340169715035 68957050559567010254572553)
  ·
    refine ⟨51717787919675257690929415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68957050559567010254572553 51717787919675257690929415)
    ·
      refine ⟨77576681879512886536394123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51717787919675257690929415 77576681879512886536394123)
      ·
        refine ⟨116365022819269329804591185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77576681879512886536394123 116365022819269329804591185)
        ·
          refine ⟨87273767114451997353443389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116365022819269329804591185 87273767114451997353443389)
          ·
            refine ⟨32727662667919499007541271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87273767114451997353443389 32727662667919499007541271)
            ·
              refine ⟨49091494001879248511311907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32727662667919499007541271 49091494001879248511311907)
              ·
                refine ⟨73637241002818872766967861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49091494001879248511311907 73637241002818872766967861)
                ·
                  refine ⟨6903491344014269321903237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73637241002818872766967861 6903491344014269321903237)
                  ·
                    refine ⟨1294404627002675497856857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6903491344014269321903237 1294404627002675497856857)
                    ·
                      refine ⟨970803470252006623392643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294404627002675497856857 970803470252006623392643)
                      ·
                        rfl

theorem cell23_1890633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 4, 2].length) (baseStart_1890633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890633 prefixEnd_1890633 := by exact prefixLift 1890633
  have htrace : WordTrace (prefixWord ++ tailWord_1890633) baseStart_1890633 baseEnd_1890633 := by
    simpa [prefixWord, tailWord_1890633, baseEnd_1890633] using wordTrace_append hprefix tailTrace_1890633
  have hstable : (prefixWord ++ tailWord_1890633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890633).length < 2 ^ (prefixWord ++ tailWord_1890633).sum := by decide
  have hdescent : baseEnd_1890633 < baseStart_1890633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890650 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2]
def baseStart_1890650 : Nat := 118140960795 + 1890650 * 2 ^ 59
def prefixEnd_1890650 : Nat := 4983230072969 + 3 ^ 40 * 1890650 * 2
def baseEnd_1890650 : Nat := 970812199423133056880065

theorem tailTrace_1890650 : CollatzResearch.WordTrace tailWord_1890650 prefixEnd_1890650 970812199423133056880065 := by
  unfold tailWord_1890650
  simp only [CollatzResearch.WordTrace]
  refine ⟨17239417650126355539485351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45971780400336948105294269 17239417650126355539485351)
  ·
    refine ⟨25859126475189533309228027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17239417650126355539485351 25859126475189533309228027)
    ·
      refine ⟨38788689712784299963842041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25859126475189533309228027 38788689712784299963842041)
      ·
        refine ⟨29091517284588224972881531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38788689712784299963842041 29091517284588224972881531)
        ·
          refine ⟨43637275926882337459322297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29091517284588224972881531 43637275926882337459322297)
          ·
            refine ⟨32727956945161753094491723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43637275926882337459322297 32727956945161753094491723)
            ·
              refine ⟨49091935417742629641737585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32727956945161753094491723 49091935417742629641737585)
              ·
                refine ⟨36818951563306972231303189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49091935417742629641737585 36818951563306972231303189)
                ·
                  refine ⟨1725888354530014323342337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36818951563306972231303189 1725888354530014323342337)
                  ·
                    refine ⟨1294416265897510742506753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1725888354530014323342337 1294416265897510742506753)
                    ·
                      refine ⟨970812199423133056880065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294416265897510742506753 970812199423133056880065)
                      ·
                        rfl

theorem cell23_1890650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_1890650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890650 prefixEnd_1890650 := by exact prefixLift 1890650
  have htrace : WordTrace (prefixWord ++ tailWord_1890650) baseStart_1890650 baseEnd_1890650 := by
    simpa [prefixWord, tailWord_1890650, baseEnd_1890650] using wordTrace_append hprefix tailTrace_1890650
  have hstable : (prefixWord ++ tailWord_1890650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890650).length < 2 ^ (prefixWord ++ tailWord_1890650).sum := by decide
  have hdescent : baseEnd_1890650 < baseStart_1890650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890678 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1890678 : Nat := 118140960795 + 1890678 * 2 ^ 59
def prefixEnd_1890678 : Nat := 4983230072969 + 3 ^ 40 * 1890678 * 2
def baseEnd_1890678 : Nat := 970826576881458947329937

theorem tailTrace_1890678 : CollatzResearch.WordTrace tailWord_1890678 prefixEnd_1890678 970826576881458947329937 := by
  unfold tailWord_1890678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4309918240275248933747543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45972461229602655293307125 4309918240275248933747543)
  ·
    refine ⟨6464877360412873400621315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4309918240275248933747543 6464877360412873400621315)
    ·
      refine ⟨9697316040619310100931973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6464877360412873400621315 9697316040619310100931973)
      ·
        refine ⟨1818246757616120643924745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9697316040619310100931973 1818246757616120643924745)
        ·
          refine ⟨1363685068212090482943559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818246757616120643924745 1363685068212090482943559)
          ·
            refine ⟨2045527602318135724415339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363685068212090482943559 2045527602318135724415339)
            ·
              refine ⟨3068291403477203586623009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045527602318135724415339 3068291403477203586623009)
              ·
                refine ⟨2301218552607902689967257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068291403477203586623009 2301218552607902689967257)
                ·
                  refine ⟨1725913914455927017475443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2301218552607902689967257 1725913914455927017475443)
                  ·
                    refine ⟨2588870871683890526213165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1725913914455927017475443 2588870871683890526213165)
                    ·
                      refine ⟨970826576881458947329937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2588870871683890526213165 970826576881458947329937)
                      ·
                        rfl

theorem cell23_1890678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1890678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890678 prefixEnd_1890678 := by exact prefixLift 1890678
  have htrace : WordTrace (prefixWord ++ tailWord_1890678) baseStart_1890678 baseEnd_1890678 := by
    simpa [prefixWord, tailWord_1890678, baseEnd_1890678] using wordTrace_append hprefix tailTrace_1890678
  have hstable : (prefixWord ++ tailWord_1890678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890678).length < 2 ^ (prefixWord ++ tailWord_1890678).sum := by decide
  have hdescent : baseEnd_1890678 < baseStart_1890678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890683 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 3]
def baseStart_1890683 : Nat := 118140960795 + 1890683 * 2 ^ 59
def prefixEnd_1890683 : Nat := 4983230072969 + 3 ^ 40 * 1890683 * 2
def baseEnd_1890683 : Nat := 970829144284731427767413

theorem tailTrace_1890683 : CollatzResearch.WordTrace tailWord_1890683 prefixEnd_1890683 970829144284731427767413 := by
  unfold tailWord_1890683
  simp only [CollatzResearch.WordTrace]
  refine ⟨68958874209385868793892703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45972582806257245862595135 68958874209385868793892703)
  ·
    refine ⟨103438311314078803190839055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68958874209385868793892703 103438311314078803190839055)
    ·
      refine ⟨155157466971118204786258583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103438311314078803190839055 155157466971118204786258583)
      ·
        refine ⟨232736200456677307179387875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155157466971118204786258583 232736200456677307179387875)
        ·
          refine ⟨349104300685015960769081813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232736200456677307179387875 349104300685015960769081813)
          ·
            refine ⟨8182132047305061580525355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 349104300685015960769081813 8182132047305061580525355)
            ·
              refine ⟨12273198070957592370788033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8182132047305061580525355 12273198070957592370788033)
              ·
                refine ⟨9204898553218194278091025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12273198070957592370788033 9204898553218194278091025)
                ·
                  refine ⟨6903673914913645708568269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9204898553218194278091025 6903673914913645708568269)
                  ·
                    refine ⟨2588877718092617140713101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6903673914913645708568269 2588877718092617140713101)
                    ·
                      refine ⟨970829144284731427767413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2588877718092617140713101 970829144284731427767413)
                      ·
                        rfl

theorem cell23_1890683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 3].length) (baseStart_1890683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890683 prefixEnd_1890683 := by exact prefixLift 1890683
  have htrace : WordTrace (prefixWord ++ tailWord_1890683) baseStart_1890683 baseEnd_1890683 := by
    simpa [prefixWord, tailWord_1890683, baseEnd_1890683] using wordTrace_append hprefix tailTrace_1890683
  have hstable : (prefixWord ++ tailWord_1890683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890683).length < 2 ^ (prefixWord ++ tailWord_1890683).sum := by decide
  have hdescent : baseEnd_1890683 < baseStart_1890683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890723 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 4]
def baseStart_1890723 : Nat := 118140960795 + 1890723 * 2 ^ 59
def prefixEnd_1890723 : Nat := 4983230072969 + 3 ^ 40 * 1890723 * 2
def baseEnd_1890723 : Nat := 970849683510911271267229

theorem tailTrace_1890723 : CollatzResearch.WordTrace tailWord_1890723 prefixEnd_1890723 970849683510911271267229 := by
  unfold tailWord_1890723
  simp only [CollatzResearch.WordTrace]
  refine ⟨68960333129240955625348823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45973555419493970416899215 68960333129240955625348823)
  ·
    refine ⟨103440499693861433438023235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68960333129240955625348823 103440499693861433438023235)
    ·
      refine ⟨155160749540792150157034853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103440499693861433438023235 155160749540792150157034853)
      ·
        refine ⟨29092640538898528154444035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155160749540792150157034853 29092640538898528154444035)
        ·
          refine ⟨43638960808347792231666053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29092640538898528154444035 43638960808347792231666053)
          ·
            refine ⟨8182305151565211043437385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43638960808347792231666053 8182305151565211043437385)
            ·
              refine ⟨6136728863673908282578039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8182305151565211043437385 6136728863673908282578039)
              ·
                refine ⟨9205093295510862423867059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6136728863673908282578039 9205093295510862423867059)
                ·
                  refine ⟨13807639943266293635800589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9205093295510862423867059 13807639943266293635800589)
                  ·
                    refine ⟨5177864978724860113425221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13807639943266293635800589 5177864978724860113425221)
                    ·
                      refine ⟨970849683510911271267229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5177864978724860113425221 970849683510911271267229)
                      ·
                        rfl

theorem cell23_1890723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_1890723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890723 prefixEnd_1890723 := by exact prefixLift 1890723
  have htrace : WordTrace (prefixWord ++ tailWord_1890723) baseStart_1890723 baseEnd_1890723 := by
    simpa [prefixWord, tailWord_1890723, baseEnd_1890723] using wordTrace_append hprefix tailTrace_1890723
  have hstable : (prefixWord ++ tailWord_1890723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890723).length < 2 ^ (prefixWord ++ tailWord_1890723).sum := by decide
  have hdescent : baseEnd_1890723 < baseStart_1890723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890797 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 6]
def baseStart_1890797 : Nat := 118140960795 + 1890797 * 2 ^ 59
def prefixEnd_1890797 : Nat := 4983230072969 + 3 ^ 40 * 1890797 * 2
def baseEnd_1890797 : Nat := 107876409008815997971321

theorem tailTrace_1890797 : CollatzResearch.WordTrace tailWord_1890797 prefixEnd_1890797 107876409008815997971321 := by
  unfold tailWord_1890797
  simp only [CollatzResearch.WordTrace]
  refine ⟨68963032130972866263542645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45975354753981910842361763 68963032130972866263542645)
  ·
    refine ⟨6465284262278706212207123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68963032130972866263542645 6465284262278706212207123)
    ·
      refine ⟨9697926393418059318310685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6465284262278706212207123 9697926393418059318310685)
      ·
        refine ⟨3636722397531772244366507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9697926393418059318310685 3636722397531772244366507)
        ·
          refine ⟨5455083596297658366549761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636722397531772244366507 5455083596297658366549761)
          ·
            refine ⟨4091312697223243774912321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5455083596297658366549761 4091312697223243774912321)
            ·
              refine ⟨3068484522917432831184241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4091312697223243774912321 3068484522917432831184241)
              ·
                refine ⟨2301363392188074623388181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068484522917432831184241 2301363392188074623388181)
                ·
                  refine ⟨107876409008815997971321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2301363392188074623388181 107876409008815997971321)
                  ·
                    rfl

theorem cell23_1890797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_1890797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890797 prefixEnd_1890797 := by exact prefixLift 1890797
  have htrace : WordTrace (prefixWord ++ tailWord_1890797) baseStart_1890797 baseEnd_1890797 := by
    simpa [prefixWord, tailWord_1890797, baseEnd_1890797] using wordTrace_append hprefix tailTrace_1890797
  have hstable : (prefixWord ++ tailWord_1890797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890797).length < 2 ^ (prefixWord ++ tailWord_1890797).sum := by decide
  have hdescent : baseEnd_1890797 < baseStart_1890797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890833 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_1890833 : Nat := 118140960795 + 1890833 * 2 ^ 59
def prefixEnd_1890833 : Nat := 4983230072969 + 3 ^ 40 * 1890833 * 2
def baseEnd_1890833 : Nat := 970906166382905840891723

theorem tailTrace_1890833 : CollatzResearch.WordTrace tailWord_1890833 prefixEnd_1890833 970906166382905840891723 := by
  unfold tailWord_1890833
  simp only [CollatzResearch.WordTrace]
  refine ⟨68964345158842444411853153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45976230105894962941235435 68964345158842444411853153)
  ·
    refine ⟨51723258869131833308889865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68964345158842444411853153 51723258869131833308889865)
    ·
      refine ⟨38792444151848874981667399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51723258869131833308889865 38792444151848874981667399)
      ·
        refine ⟨58188666227773312472501099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38792444151848874981667399 58188666227773312472501099)
        ·
          refine ⟨87282999341659968708751649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58188666227773312472501099 87282999341659968708751649)
          ·
            refine ⟨65462249506244976531563737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87282999341659968708751649 65462249506244976531563737)
            ·
              refine ⟨49096687129683732398672803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65462249506244976531563737 49096687129683732398672803)
              ·
                refine ⟨73645030694525598598009205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49096687129683732398672803 73645030694525598598009205)
                ·
                  refine ⟨6904221627611774868563363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73645030694525598598009205 6904221627611774868563363)
                  ·
                    refine ⟨10356332441417662302845045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6904221627611774868563363 10356332441417662302845045)
                    ·
                      refine ⟨970906166382905840891723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10356332441417662302845045 970906166382905840891723)
                      ·
                        rfl

theorem cell23_1890833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_1890833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890833 prefixEnd_1890833 := by exact prefixLift 1890833
  have htrace : WordTrace (prefixWord ++ tailWord_1890833) baseStart_1890833 baseEnd_1890833 := by
    simpa [prefixWord, tailWord_1890833, baseEnd_1890833] using wordTrace_append hprefix tailTrace_1890833
  have hstable : (prefixWord ++ tailWord_1890833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890833).length < 2 ^ (prefixWord ++ tailWord_1890833).sum := by decide
  have hdescent : baseEnd_1890833 < baseStart_1890833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890840 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 1, 6]
def baseStart_1890840 : Nat := 118140960795 + 1890840 * 2 ^ 59
def prefixEnd_1890840 : Nat := 4983230072969 + 3 ^ 40 * 1890840 * 2
def baseEnd_1890840 : Nat := 323636586915829104501397

theorem tailTrace_1890840 : CollatzResearch.WordTrace tailWord_1890840 prefixEnd_1890840 323636586915829104501397 := by
  unfold tailWord_1890840
  simp only [CollatzResearch.WordTrace]
  refine ⟨34482300234908542303678987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45976400313211389738238649 34482300234908542303678987)
  ·
    refine ⟨51723450352362813455518481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34482300234908542303678987 51723450352362813455518481)
    ·
      refine ⟨38792587764272110091638861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51723450352362813455518481 38792587764272110091638861)
      ·
        refine ⟨14547220411602041284364573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38792587764272110091638861 14547220411602041284364573)
        ·
          refine ⟨5455207654350765481636715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14547220411602041284364573 5455207654350765481636715)
          ·
            refine ⟨8182811481526148222455073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5455207654350765481636715 8182811481526148222455073)
            ·
              refine ⟨6137108611144611166841305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8182811481526148222455073 6137108611144611166841305)
              ·
                refine ⟨4602831458358458375130979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6137108611144611166841305 4602831458358458375130979)
                ·
                  refine ⟨6904247187537687562696469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602831458358458375130979 6904247187537687562696469)
                  ·
                    refine ⟨323636586915829104501397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6904247187537687562696469 323636586915829104501397)
                    ·
                      rfl

theorem cell23_1890840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_1890840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890840 prefixEnd_1890840 := by exact prefixLift 1890840
  have htrace : WordTrace (prefixWord ++ tailWord_1890840) baseStart_1890840 baseEnd_1890840 := by
    simpa [prefixWord, tailWord_1890840, baseEnd_1890840] using wordTrace_append hprefix tailTrace_1890840
  have hstable : (prefixWord ++ tailWord_1890840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890840).length < 2 ^ (prefixWord ++ tailWord_1890840).sum := by decide
  have hdescent : baseEnd_1890840 < baseStart_1890840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890844 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 1, 5]
def baseStart_1890844 : Nat := 118140960795 + 1890844 * 2 ^ 59
def prefixEnd_1890844 : Nat := 4983230072969 + 3 ^ 40 * 1890844 * 2
def baseEnd_1890844 : Nat := 323637271556701765951391

theorem tailTrace_1890844 : CollatzResearch.WordTrace tailWord_1890844 prefixEnd_1890844 323637271556701765951391 := by
  unfold tailWord_1890844
  simp only [CollatzResearch.WordTrace]
  refine ⟨34482373180901296645251793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45976497574535062193669057 34482373180901296645251793)
  ·
    refine ⟨25861779885675972483938845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34482373180901296645251793 25861779885675972483938845)
    ·
      refine ⟨9698167457128489681477067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25861779885675972483938845 9698167457128489681477067)
      ·
        refine ⟨14547251185692734522215601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9698167457128489681477067 14547251185692734522215601)
        ·
          refine ⟨10910438389269550891661701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14547251185692734522215601 10910438389269550891661701)
          ·
            refine ⟨2045707197988040792186569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10910438389269550891661701 2045707197988040792186569)
            ·
              refine ⟨1534280398491030594139927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2045707197988040792186569 1534280398491030594139927)
              ·
                refine ⟨2301420597736545891209891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534280398491030594139927 2301420597736545891209891)
                ·
                  refine ⟨3452130896604818836814837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301420597736545891209891 3452130896604818836814837)
                  ·
                    refine ⟨323637271556701765951391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3452130896604818836814837 323637271556701765951391)
                    ·
                      rfl

theorem cell23_1890844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_1890844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890844 prefixEnd_1890844 := by exact prefixLift 1890844
  have htrace : WordTrace (prefixWord ++ tailWord_1890844) baseStart_1890844 baseEnd_1890844 := by
    simpa [prefixWord, tailWord_1890844, baseEnd_1890844] using wordTrace_append hprefix tailTrace_1890844
  have hstable : (prefixWord ++ tailWord_1890844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890844).length < 2 ^ (prefixWord ++ tailWord_1890844).sum := by decide
  have hdescent : baseEnd_1890844 < baseStart_1890844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890847 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 7, 2, 2]
def baseStart_1890847 : Nat := 118140960795 + 1890847 * 2 ^ 59
def prefixEnd_1890847 : Nat := 4983230072969 + 3 ^ 40 * 1890847 * 2
def baseEnd_1890847 : Nat := 970913355112068786116659

theorem tailTrace_1890847 : CollatzResearch.WordTrace tailWord_1890847 prefixEnd_1890847 970913355112068786116659 := by
  unfold tailWord_1890847
  simp only [CollatzResearch.WordTrace]
  refine ⟨68964855780791724802862795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45976570520527816535241863 68964855780791724802862795)
  ·
    refine ⟨103447283671187587204294193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68964855780791724802862795 103447283671187587204294193)
    ·
      refine ⟨77585462753390690403220645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103447283671187587204294193 77585462753390690403220645)
      ·
        refine ⟨14547274266260754450603871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77585462753390690403220645 14547274266260754450603871)
        ·
          refine ⟨21820911399391131675905807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14547274266260754450603871 21820911399391131675905807)
          ·
            refine ⟨32731367099086697513858711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21820911399391131675905807 32731367099086697513858711)
            ·
              refine ⟨49097050648630046270788067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32731367099086697513858711 49097050648630046270788067)
              ·
                refine ⟨73645575972945069406182101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49097050648630046270788067 73645575972945069406182101)
                ·
                  refine ⟨1726068186865900064207393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 73645575972945069406182101 1726068186865900064207393)
                  ·
                    refine ⟨1294551140149425048155545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1726068186865900064207393 1294551140149425048155545)
                    ·
                      refine ⟨970913355112068786116659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294551140149425048155545 970913355112068786116659)
                      ·
                        rfl

theorem cell23_1890847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_1890847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890847 prefixEnd_1890847 := by exact prefixLift 1890847
  have htrace : WordTrace (prefixWord ++ tailWord_1890847) baseStart_1890847 baseEnd_1890847 := by
    simpa [prefixWord, tailWord_1890847, baseEnd_1890847] using wordTrace_append hprefix tailTrace_1890847
  have hstable : (prefixWord ++ tailWord_1890847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890847).length < 2 ^ (prefixWord ++ tailWord_1890847).sum := by decide
  have hdescent : baseEnd_1890847 < baseStart_1890847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890850 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_1890850 : Nat := 118140960795 + 1890850 * 2 ^ 59
def prefixEnd_1890850 : Nat := 4983230072969 + 3 ^ 40 * 1890850 * 2
def baseEnd_1890850 : Nat := 970914895554032274379145

theorem tailTrace_1890850 : CollatzResearch.WordTrace tailWord_1890850 prefixEnd_1890850 970914895554032274379145 := by
  unfold tailWord_1890850
  simp only [CollatzResearch.WordTrace]
  refine ⟨17241241299945214078805501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45976643466520570876814669 17241241299945214078805501)
  ·
    refine ⟨6465465487479455279552063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17241241299945214078805501 6465465487479455279552063)
    ·
      refine ⟨9698198231219182919328095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6465465487479455279552063 9698198231219182919328095)
      ·
        refine ⟨14547297346828774378992143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9698198231219182919328095 14547297346828774378992143)
        ·
          refine ⟨21820946020243161568488215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14547297346828774378992143 21820946020243161568488215)
          ·
            refine ⟨32731419030364742352732323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21820946020243161568488215 32731419030364742352732323)
            ·
              refine ⟨49097128545547113529098485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32731419030364742352732323 49097128545547113529098485)
              ·
                refine ⟨4602855801145041893352983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49097128545547113529098485 4602855801145041893352983)
                ·
                  refine ⟨6904283701717562840029475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602855801145041893352983 6904283701717562840029475)
                  ·
                    refine ⟨10356425552576344260044213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6904283701717562840029475 10356425552576344260044213)
                    ·
                      refine ⟨970914895554032274379145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10356425552576344260044213 970914895554032274379145)
                      ·
                        rfl

theorem cell23_1890850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_1890850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890850 prefixEnd_1890850 := by exact prefixLift 1890850
  have htrace : WordTrace (prefixWord ++ tailWord_1890850) baseStart_1890850 baseEnd_1890850 := by
    simpa [prefixWord, tailWord_1890850, baseEnd_1890850] using wordTrace_append hprefix tailTrace_1890850
  have hstable : (prefixWord ++ tailWord_1890850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890850).length < 2 ^ (prefixWord ++ tailWord_1890850).sum := by decide
  have hdescent : baseEnd_1890850 < baseStart_1890850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890874 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 2, 4]
def baseStart_1890874 : Nat := 118140960795 + 1890874 * 2 ^ 59
def prefixEnd_1890874 : Nat := 4983230072969 + 3 ^ 40 * 1890874 * 2
def baseEnd_1890874 : Nat := 323642406363246726826345

theorem tailTrace_1890874 : CollatzResearch.WordTrace tailWord_1890874 prefixEnd_1890874 323642406363246726826345 := by
  unfold tailWord_1890874
  simp only [CollatzResearch.WordTrace]
  refine ⟨17241460137923477103523919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45977227034462605609397117 17241460137923477103523919)
  ·
    refine ⟨25862190206885215655285879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17241460137923477103523919 25862190206885215655285879)
    ·
      refine ⟨38793285310327823482928819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25862190206885215655285879 38793285310327823482928819)
      ·
        refine ⟨58189927965491735224393229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38793285310327823482928819 58189927965491735224393229)
        ·
          refine ⟨21821222987059400709147461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58189927965491735224393229 21821222987059400709147461)
          ·
            refine ⟨4091479310073637632965149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21821222987059400709147461 4091479310073637632965149)
            ·
              refine ⟨1534304741277614112361931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4091479310073637632965149 1534304741277614112361931)
              ·
                refine ⟨2301457111916421168542897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534304741277614112361931 2301457111916421168542897)
                ·
                  refine ⟨1726092833937315876407173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2301457111916421168542897 1726092833937315876407173)
                  ·
                    refine ⟨323642406363246726826345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1726092833937315876407173 323642406363246726826345)
                    ·
                      rfl

theorem cell23_1890874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_1890874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890874 prefixEnd_1890874 := by exact prefixLift 1890874
  have htrace : WordTrace (prefixWord ++ tailWord_1890874) baseStart_1890874 baseEnd_1890874 := by
    simpa [prefixWord, tailWord_1890874, baseEnd_1890874] using wordTrace_append hprefix tailTrace_1890874
  have hstable : (prefixWord ++ tailWord_1890874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890874).length < 2 ^ (prefixWord ++ tailWord_1890874).sum := by decide
  have hdescent : baseEnd_1890874 < baseStart_1890874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890877 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1890877 : Nat := 118140960795 + 1890877 * 2 ^ 59
def prefixEnd_1890877 : Nat := 4983230072969 + 3 ^ 40 * 1890877 * 2
def baseEnd_1890877 : Nat := 970928759531703668741521

theorem tailTrace_1890877 : CollatzResearch.WordTrace tailWord_1890877 prefixEnd_1890877 970928759531703668741521 := by
  unfold tailWord_1890877
  simp only [CollatzResearch.WordTrace]
  refine ⟨68965949970683039926454885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45977299980455359950969923 68965949970683039926454885)
  ·
    refine ⟨12931115619503069986210291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68965949970683039926454885 12931115619503069986210291)
    ·
      refine ⟨19396673429254604979315437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12931115619503069986210291 19396673429254604979315437)
      ·
        refine ⟨7273752535970476867243289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19396673429254604979315437 7273752535970476867243289)
        ·
          refine ⟨5455314401977857650432467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7273752535970476867243289 5455314401977857650432467)
          ·
            refine ⟨8182971602966786475648701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5455314401977857650432467 8182971602966786475648701)
            ·
              refine ⟨3068614351112544928368263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8182971602966786475648701 3068614351112544928368263)
              ·
                refine ⟨4602921526668817392552395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068614351112544928368263 4602921526668817392552395)
                ·
                  refine ⟨6904382290003226088828593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4602921526668817392552395 6904382290003226088828593)
                  ·
                    refine ⟨5178286717502419566621445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6904382290003226088828593 5178286717502419566621445)
                    ·
                      refine ⟨970928759531703668741521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5178286717502419566621445 970928759531703668741521)
                      ·
                        rfl

theorem cell23_1890877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1890877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890877 prefixEnd_1890877 := by exact prefixLift 1890877
  have htrace : WordTrace (prefixWord ++ tailWord_1890877) baseStart_1890877 baseEnd_1890877 := by
    simpa [prefixWord, tailWord_1890877, baseEnd_1890877] using wordTrace_append hprefix tailTrace_1890877
  have hstable : (prefixWord ++ tailWord_1890877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890877).length < 2 ^ (prefixWord ++ tailWord_1890877).sum := by decide
  have hdescent : baseEnd_1890877 < baseStart_1890877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890883 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 2, 7]
def baseStart_1890883 : Nat := 118140960795 + 1890883 * 2 ^ 59
def prefixEnd_1890883 : Nat := 4983230072969 + 3 ^ 40 * 1890883 * 2
def baseEnd_1890883 : Nat := 323643946805210215088831

theorem tailTrace_1890883 : CollatzResearch.WordTrace tailWord_1890883 prefixEnd_1890883 323643946805210215088831 := by
  unfold tailWord_1890883
  simp only [CollatzResearch.WordTrace]
  refine ⟨68966168808661302951173303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45977445872440868634115535 68966168808661302951173303)
  ·
    refine ⟨103449253212991954426759955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68966168808661302951173303 103449253212991954426759955)
    ·
      refine ⟨155173879819487931640139933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103449253212991954426759955 155173879819487931640139933)
      ·
        refine ⟨58190204932307974365052475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155173879819487931640139933 58190204932307974365052475)
        ·
          refine ⟨87285307398461961547578713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58190204932307974365052475 87285307398461961547578713)
          ·
            refine ⟨65463980548846471160684035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87285307398461961547578713 65463980548846471160684035)
            ·
              refine ⟨98195970823269706741026053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65463980548846471160684035 98195970823269706741026053)
              ·
                refine ⟨18411744529363070013942385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98195970823269706741026053 18411744529363070013942385)
                ·
                  refine ⟨13808808397022302510456789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18411744529363070013942385 13808808397022302510456789)
                  ·
                    refine ⟨323643946805210215088831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13808808397022302510456789 323643946805210215088831)
                    ·
                      rfl

theorem cell23_1890883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 7].length) (baseStart_1890883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890883 prefixEnd_1890883 := by exact prefixLift 1890883
  have htrace : WordTrace (prefixWord ++ tailWord_1890883) baseStart_1890883 baseEnd_1890883 := by
    simpa [prefixWord, tailWord_1890883, baseEnd_1890883] using wordTrace_append hprefix tailTrace_1890883
  have hstable : (prefixWord ++ tailWord_1890883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890883).length < 2 ^ (prefixWord ++ tailWord_1890883).sum := by decide
  have hdescent : baseEnd_1890883 < baseStart_1890883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890887 : List Nat := [1, 1, 4, 1, 4, 3, 2, 7]
def baseStart_1890887 : Nat := 118140960795 + 1890887 * 2 ^ 59
def prefixEnd_1890887 : Nat := 4983230072969 + 3 ^ 40 * 1890887 * 2
def baseEnd_1890887 : Nat := 35960514605120319615425

theorem tailTrace_1890887 : CollatzResearch.WordTrace tailWord_1890887 prefixEnd_1890887 35960514605120319615425 := by
  unfold tailWord_1890887
  simp only [CollatzResearch.WordTrace]
  refine ⟨68966314700646811634318915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45977543133764541089545943 68966314700646811634318915)
  ·
    refine ⟨103449472050970217451478373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68966314700646811634318915 103449472050970217451478373)
    ·
      refine ⟨19396776009556915772152195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103449472050970217451478373 19396776009556915772152195)
      ·
        refine ⟨29095164014335373658228293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19396776009556915772152195 29095164014335373658228293)
        ·
          refine ⟨5455343252687882560917805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29095164014335373658228293 5455343252687882560917805)
          ·
            refine ⟨2045753719757955960344177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5455343252687882560917805 2045753719757955960344177)
            ·
              refine ⟨1534315289818466970258133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2045753719757955960344177 1534315289818466970258133)
              ·
                refine ⟨35960514605120319615425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1534315289818466970258133 35960514605120319615425)
                ·
                  rfl

theorem cell23_1890887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 7].length) (baseStart_1890887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890887 prefixEnd_1890887 := by exact prefixLift 1890887
  have htrace : WordTrace (prefixWord ++ tailWord_1890887) baseStart_1890887 baseEnd_1890887 := by
    simpa [prefixWord, tailWord_1890887, baseEnd_1890887] using wordTrace_append hprefix tailTrace_1890887
  have hstable : (prefixWord ++ tailWord_1890887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890887).length < 2 ^ (prefixWord ++ tailWord_1890887).sum := by decide
  have hdescent : baseEnd_1890887 < baseStart_1890887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890897 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 4, 1, 3]
def baseStart_1890897 : Nat := 118140960795 + 1890897 * 2 ^ 59
def prefixEnd_1890897 : Nat := 4983230072969 + 3 ^ 40 * 1890897 * 2
def baseEnd_1890897 : Nat := 970939029144793590491429

theorem tailTrace_1890897 : CollatzResearch.WordTrace tailWord_1890897 prefixEnd_1890897 970939029144793590491429 := by
  unfold tailWord_1890897
  simp only [CollatzResearch.WordTrace]
  refine ⟨68966679430610583342182945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45977786287073722228121963 68966679430610583342182945)
  ·
    refine ⟨51725009572957937506637209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68966679430610583342182945 51725009572957937506637209)
    ·
      refine ⟨38793757179718453129977907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51725009572957937506637209 38793757179718453129977907)
      ·
        refine ⟨58190635769577679694966861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38793757179718453129977907 58190635769577679694966861)
        ·
          refine ⟨21821488413591629885612573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58190635769577679694966861 21821488413591629885612573)
          ·
            refine ⟨8183058155096861207104715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21821488413591629885612573 8183058155096861207104715)
            ·
              refine ⟨12274587232645291810657073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183058155096861207104715 12274587232645291810657073)
              ·
                refine ⟨9205940424483968857992805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12274587232645291810657073 9205940424483968857992805)
                ·
                  refine ⟨1726113829590744160873651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9205940424483968857992805 1726113829590744160873651)
                  ·
                    refine ⟨2589170744386116241310477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1726113829590744160873651 2589170744386116241310477)
                    ·
                      refine ⟨970939029144793590491429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2589170744386116241310477 970939029144793590491429)
                      ·
                        rfl

theorem cell23_1890897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_1890897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890897 prefixEnd_1890897 := by exact prefixLift 1890897
  have htrace : WordTrace (prefixWord ++ tailWord_1890897) baseStart_1890897 baseEnd_1890897 := by
    simpa [prefixWord, tailWord_1890897, baseEnd_1890897] using wordTrace_append hprefix tailTrace_1890897
  have hstable : (prefixWord ++ tailWord_1890897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890897).length < 2 ^ (prefixWord ++ tailWord_1890897).sum := by decide
  have hdescent : baseEnd_1890897 < baseStart_1890897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890940 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1890940 : Nat := 118140960795 + 1890940 * 2 ^ 59
def prefixEnd_1890940 : Nat := 4983230072969 + 3 ^ 40 * 1890940 * 2
def baseEnd_1890940 : Nat := 970961108812936922253731

theorem tailTrace_1890940 : CollatzResearch.WordTrace tailWord_1890940 prefixEnd_1890940 970961108812936922253731 := by
  unfold tailWord_1890940
  simp only [CollatzResearch.WordTrace]
  refine ⟨34484123884727400842999137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45978831846303201123998849 34484123884727400842999137)
  ·
    refine ⟨25863092913545550632249353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34484123884727400842999137 25863092913545550632249353)
    ·
      refine ⟨19397319685159162974187015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25863092913545550632249353 19397319685159162974187015)
      ·
        refine ⟨29095979527738744461280523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19397319685159162974187015 29095979527738744461280523)
        ·
          refine ⟨43643969291608116691920785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29095979527738744461280523 43643969291608116691920785)
          ·
            refine ⟨32732976968706087518940589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43643969291608116691920785 32732976968706087518940589)
            ·
              refine ⟨12274866363264782819602721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32732976968706087518940589 12274866363264782819602721)
              ·
                refine ⟨9206149772448587114702041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12274866363264782819602721 9206149772448587114702041)
                ·
                  refine ⟨6904612329336440336026531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9206149772448587114702041 6904612329336440336026531)
                  ·
                    refine ⟨10356918494004660504039797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6904612329336440336026531 10356918494004660504039797)
                    ·
                      refine ⟨970961108812936922253731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10356918494004660504039797 970961108812936922253731)
                      ·
                        rfl

theorem cell23_1890940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1890940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1890940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1890940 prefixEnd_1890940 := by exact prefixLift 1890940
  have htrace : WordTrace (prefixWord ++ tailWord_1890940) baseStart_1890940 baseEnd_1890940 := by
    simpa [prefixWord, tailWord_1890940, baseEnd_1890940] using wordTrace_append hprefix tailTrace_1890940
  have hstable : (prefixWord ++ tailWord_1890940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890940).length < 2 ^ (prefixWord ++ tailWord_1890940).sum := by decide
  have hdescent : baseEnd_1890940 < baseStart_1890940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891007 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 2, 5]
def baseStart_1891007 : Nat := 118140960795 + 1891007 * 2 ^ 59
def prefixEnd_1891007 : Nat := 4983230072969 + 3 ^ 40 * 1891007 * 2
def baseEnd_1891007 : Nat := 323665170672262720038641

theorem tailTrace_1891007 : CollatzResearch.WordTrace tailWord_1891007 prefixEnd_1891007 323665170672262720038641 := by
  unfold tailWord_1891007
  simp only [CollatzResearch.WordTrace]
  refine ⟨68970691460212072128687275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45980460973474714752458183 68970691460212072128687275)
  ·
    refine ⟨103456037190318108193030913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68970691460212072128687275 103456037190318108193030913)
    ·
      refine ⟨77592027892738581144773185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103456037190318108193030913 77592027892738581144773185)
      ·
        refine ⟨58194020919553935858579889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77592027892738581144773185 58194020919553935858579889)
        ·
          refine ⟨43645515689665451893934917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58194020919553935858579889 43645515689665451893934917)
          ·
            refine ⟨8183534191812272230112797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43645515689665451893934917 8183534191812272230112797)
            ·
              refine ⟨3068825321929602086292299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8183534191812272230112797 3068825321929602086292299)
              ·
                refine ⟨4603237982894403129438449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068825321929602086292299 4603237982894403129438449)
                ·
                  refine ⟨3452428487170802347078837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4603237982894403129438449 3452428487170802347078837)
                  ·
                    refine ⟨323665170672262720038641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3452428487170802347078837 323665170672262720038641)
                    ·
                      rfl

theorem cell23_1891007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 5].length) (baseStart_1891007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891007 prefixEnd_1891007 := by exact prefixLift 1891007
  have htrace : WordTrace (prefixWord ++ tailWord_1891007) baseStart_1891007 baseEnd_1891007 := by
    simpa [prefixWord, tailWord_1891007, baseEnd_1891007] using wordTrace_append hprefix tailTrace_1891007
  have hstable : (prefixWord ++ tailWord_1891007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891007).length < 2 ^ (prefixWord ++ tailWord_1891007).sum := by decide
  have hdescent : baseEnd_1891007 < baseStart_1891007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891040 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1891040 : Nat := 118140960795 + 1891040 * 2 ^ 59
def prefixEnd_1891040 : Nat := 4983230072969 + 3 ^ 40 * 1891040 * 2
def baseEnd_1891040 : Nat := 971012456878386531003271

theorem tailTrace_1891040 : CollatzResearch.WordTrace tailWord_1891040 prefixEnd_1891040 971012456878386531003271 := by
  unfold tailWord_1891040
  simp only [CollatzResearch.WordTrace]
  refine ⟨34485947534546259382319287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45981263379395012509759049 34485947534546259382319287)
  ·
    refine ⟨51728921301819389073478931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34485947534546259382319287 51728921301819389073478931)
    ·
      refine ⟨77593381952729083610218397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51728921301819389073478931 77593381952729083610218397)
      ·
        refine ⟨29097518232273406353831899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77593381952729083610218397 29097518232273406353831899)
        ·
          refine ⟨43646277348410109530747849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29097518232273406353831899 43646277348410109530747849)
          ·
            refine ⟨32734708011307582148060887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43646277348410109530747849 32734708011307582148060887)
            ·
              refine ⟨49102062016961373222091331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32734708011307582148060887 49102062016961373222091331)
              ·
                refine ⟨73653093025442059833136997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49102062016961373222091331 73653093025442059833136997)
                ·
                  refine ⟨13809954942270386218713187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73653093025442059833136997 13809954942270386218713187)
                  ·
                    refine ⟨20714932413405579328069781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13809954942270386218713187 20714932413405579328069781)
                    ·
                      refine ⟨971012456878386531003271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20714932413405579328069781 971012456878386531003271)
                      ·
                        rfl

theorem cell23_1891040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1891040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891040 prefixEnd_1891040 := by exact prefixLift 1891040
  have htrace : WordTrace (prefixWord ++ tailWord_1891040) baseStart_1891040 baseEnd_1891040 := by
    simpa [prefixWord, tailWord_1891040, baseEnd_1891040] using wordTrace_append hprefix tailTrace_1891040
  have hstable : (prefixWord ++ tailWord_1891040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891040).length < 2 ^ (prefixWord ++ tailWord_1891040).sum := by decide
  have hdescent : baseEnd_1891040 < baseStart_1891040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891044 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 2, 4, 2]
def baseStart_1891044 : Nat := 118140960795 + 1891044 * 2 ^ 59
def prefixEnd_1891044 : Nat := 4983230072969 + 3 ^ 40 * 1891044 * 2
def baseEnd_1891044 : Nat := 971014510801004515353253

theorem tailTrace_1891044 : CollatzResearch.WordTrace tailWord_1891044 prefixEnd_1891044 971014510801004515353253 := by
  unfold tailWord_1891044
  simp only [CollatzResearch.WordTrace]
  refine ⟨34486020480539013723892093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45981360640718684965189457 34486020480539013723892093)
  ·
    refine ⟨12932257680202130146459535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34486020480539013723892093 12932257680202130146459535)
    ·
      refine ⟨19398386520303195219689303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12932257680202130146459535 19398386520303195219689303)
      ·
        refine ⟨29097579780454792829533955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19398386520303195219689303 29097579780454792829533955)
        ·
          refine ⟨43646369670682189244300933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29097579780454792829533955 43646369670682189244300933)
          ·
            refine ⟨8183694313252910483306425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43646369670682189244300933 8183694313252910483306425)
            ·
              refine ⟨6137770734939682862479819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8183694313252910483306425 6137770734939682862479819)
              ·
                refine ⟨9206656102409524293719729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137770734939682862479819 9206656102409524293719729)
                ·
                  refine ⟨6904992076807143220289797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9206656102409524293719729 6904992076807143220289797)
                  ·
                    refine ⟨1294686014401339353804337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6904992076807143220289797 1294686014401339353804337)
                    ·
                      refine ⟨971014510801004515353253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294686014401339353804337 971014510801004515353253)
                      ·
                        rfl

theorem cell23_1891044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_1891044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891044 prefixEnd_1891044 := by exact prefixLift 1891044
  have htrace : WordTrace (prefixWord ++ tailWord_1891044) baseStart_1891044 baseEnd_1891044 := by
    simpa [prefixWord, tailWord_1891044, baseEnd_1891044] using wordTrace_append hprefix tailTrace_1891044
  have hstable : (prefixWord ++ tailWord_1891044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891044).length < 2 ^ (prefixWord ++ tailWord_1891044).sum := by decide
  have hdescent : baseEnd_1891044 < baseStart_1891044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891054 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_1891054 : Nat := 118140960795 + 1891054 * 2 ^ 59
def prefixEnd_1891054 : Nat := 4983230072969 + 3 ^ 40 * 1891054 * 2
def baseEnd_1891054 : Nat := 323673215202516492076069

theorem tailTrace_1891054 : CollatzResearch.WordTrace tailWord_1891054 prefixEnd_1891054 323673215202516492076069 := by
  unfold tailWord_1891054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8621550711380224894456027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45981603794027866103765477 8621550711380224894456027)
  ·
    refine ⟨12932326067070337341684041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8621550711380224894456027 12932326067070337341684041)
    ·
      refine ⟨9699244550302753006263031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12932326067070337341684041 9699244550302753006263031)
      ·
        refine ⟨14548866825454129509394547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9699244550302753006263031 14548866825454129509394547)
        ·
          refine ⟨21823300238181194264091821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14548866825454129509394547 21823300238181194264091821)
          ·
            refine ⟨8183737589317947849034433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21823300238181194264091821 8183737589317947849034433)
            ·
              refine ⟨6137803191988460886775825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8183737589317947849034433 6137803191988460886775825)
              ·
                refine ⟨4603352393991345665081869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6137803191988460886775825 4603352393991345665081869)
                ·
                  refine ⟨1726257147746754624405701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4603352393991345665081869 1726257147746754624405701)
                  ·
                    refine ⟨323673215202516492076069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1726257147746754624405701 323673215202516492076069)
                    ·
                      rfl

theorem cell23_1891054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_1891054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891054 prefixEnd_1891054 := by exact prefixLift 1891054
  have htrace : WordTrace (prefixWord ++ tailWord_1891054) baseStart_1891054 baseEnd_1891054 := by
    simpa [prefixWord, tailWord_1891054, baseEnd_1891054] using wordTrace_append hprefix tailTrace_1891054
  have hstable : (prefixWord ++ tailWord_1891054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891054).length < 2 ^ (prefixWord ++ tailWord_1891054).sum := by decide
  have hdescent : baseEnd_1891054 < baseStart_1891054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891101 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 6]
def baseStart_1891101 : Nat := 118140960795 + 1891101 * 2 ^ 59
def prefixEnd_1891101 : Nat := 4983230072969 + 3 ^ 40 * 1891101 * 2
def baseEnd_1891101 : Nat := 107893753244256754704499

theorem tailTrace_1891101 : CollatzResearch.WordTrace tailWord_1891101 prefixEnd_1891101 107893753244256754704499 := by
  unfold tailWord_1891101
  simp only [CollatzResearch.WordTrace]
  refine ⟨68974119921871526182609157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45982746614581017455072771 68974119921871526182609157)
  ·
    refine ⟨12932647485350911159239217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68974119921871526182609157 12932647485350911159239217)
    ·
      refine ⟨9699485614013183369429413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12932647485350911159239217 9699485614013183369429413)
      ·
        refine ⟨1818653552627471881768015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9699485614013183369429413 1818653552627471881768015)
        ·
          refine ⟨2727980328941207822652023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818653552627471881768015 2727980328941207822652023)
          ·
            refine ⟨4091970493411811733978035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727980328941207822652023 4091970493411811733978035)
            ·
              refine ⟨6137955740117717600967053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4091970493411811733978035 6137955740117717600967053)
              ·
                refine ⟨2301733402544144100362645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6137955740117717600967053 2301733402544144100362645)
                ·
                  refine ⟨107893753244256754704499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2301733402544144100362645 107893753244256754704499)
                  ·
                    rfl

theorem cell23_1891101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_1891101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891101 prefixEnd_1891101 := by exact prefixLift 1891101
  have htrace : WordTrace (prefixWord ++ tailWord_1891101) baseStart_1891101 baseEnd_1891101 := by
    simpa [prefixWord, tailWord_1891101, baseEnd_1891101] using wordTrace_append hprefix tailTrace_1891101
  have hstable : (prefixWord ++ tailWord_1891101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891101).length < 2 ^ (prefixWord ++ tailWord_1891101).sum := by decide
  have hdescent : baseEnd_1891101 < baseStart_1891101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891121 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 2, 3, 2]
def baseStart_1891121 : Nat := 118140960795 + 1891121 * 2 ^ 59
def prefixEnd_1891121 : Nat := 4983230072969 + 3 ^ 40 * 1891121 * 2
def baseEnd_1891121 : Nat := 971054048811400714090399

theorem tailTrace_1891121 : CollatzResearch.WordTrace tailWord_1891121 prefixEnd_1891121 971054048811400714090399 := by
  unfold tailWord_1891121
  simp only [CollatzResearch.WordTrace]
  refine ⟨68974849381799069598337217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45983232921199379732224811 68974849381799069598337217)
  ·
    refine ⟨51731137036349302198752913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68974849381799069598337217 51731137036349302198752913)
    ·
      refine ⟨38798352777261976649064685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51731137036349302198752913 38798352777261976649064685)
      ·
        refine ⟨14549382291473241243399257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38798352777261976649064685 14549382291473241243399257)
        ·
          refine ⟨10912036718604930932549443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14549382291473241243399257 10912036718604930932549443)
          ·
            refine ⟨16368055077907396398824165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10912036718604930932549443 16368055077907396398824165)
            ·
              refine ⟨3069010327107636824779531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16368055077907396398824165 3069010327107636824779531)
              ·
                refine ⟨4603515490661455237169297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069010327107636824779531 4603515490661455237169297)
                ·
                  refine ⟨3452636617996091427876973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4603515490661455237169297 3452636617996091427876973)
                  ·
                    refine ⟨1294738731748534285453865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3452636617996091427876973 1294738731748534285453865)
                    ·
                      refine ⟨971054048811400714090399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294738731748534285453865 971054048811400714090399)
                      ·
                        rfl

theorem cell23_1891121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_1891121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891121 prefixEnd_1891121 := by exact prefixLift 1891121
  have htrace : WordTrace (prefixWord ++ tailWord_1891121) baseStart_1891121 baseEnd_1891121 := by
    simpa [prefixWord, tailWord_1891121, baseEnd_1891121] using wordTrace_append hprefix tailTrace_1891121
  have hstable : (prefixWord ++ tailWord_1891121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891121).length < 2 ^ (prefixWord ++ tailWord_1891121).sum := by decide
  have hdescent : baseEnd_1891121 < baseStart_1891121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891127 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 1, 6]
def baseStart_1891127 : Nat := 118140960795 + 1891127 * 2 ^ 59
def prefixEnd_1891127 : Nat := 4983230072969 + 3 ^ 40 * 1891127 * 2
def baseEnd_1891127 : Nat := 323685709898442563538457

theorem tailTrace_1891127 : CollatzResearch.WordTrace tailWord_1891127 prefixEnd_1891127 323685709898442563538457 := by
  unfold tailWord_1891127
  simp only [CollatzResearch.WordTrace]
  refine ⟨68975068219777332623055635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45983378813184888415370423 68975068219777332623055635)
  ·
    refine ⟨103462602329665998934583453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68975068219777332623055635 103462602329665998934583453)
    ·
      refine ⟨38798475873624749600468795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103462602329665998934583453 38798475873624749600468795)
      ·
        refine ⟨58197713810437124400703193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38798475873624749600468795 58197713810437124400703193)
        ·
          refine ⟨43648285357827843300527395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58197713810437124400703193 43648285357827843300527395)
          ·
            refine ⟨65472428036741764950791093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43648285357827843300527395 65472428036741764950791093)
            ·
              refine ⟨6138040128444540464136665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65472428036741764950791093 6138040128444540464136665)
              ·
                refine ⟨4603530096333405348102499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6138040128444540464136665 4603530096333405348102499)
                ·
                  refine ⟨6905295144500108022153749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4603530096333405348102499 6905295144500108022153749)
                  ·
                    refine ⟨323685709898442563538457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6905295144500108022153749 323685709898442563538457)
                    ·
                      rfl

theorem cell23_1891127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_1891127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891127 prefixEnd_1891127 := by exact prefixLift 1891127
  have htrace : WordTrace (prefixWord ++ tailWord_1891127) baseStart_1891127 baseEnd_1891127 := by
    simpa [prefixWord, tailWord_1891127, baseEnd_1891127] using wordTrace_append hprefix tailTrace_1891127
  have hstable : (prefixWord ++ tailWord_1891127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891127).length < 2 ^ (prefixWord ++ tailWord_1891127).sum := by decide
  have hdescent : baseEnd_1891127 < baseStart_1891127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891145 : List Nat := [1, 2, 1, 1, 2, 7, 2, 2, 1, 1, 3]
def baseStart_1891145 : Nat := 118140960795 + 1891145 * 2 ^ 59
def prefixEnd_1891145 : Nat := 4983230072969 + 3 ^ 40 * 1891145 * 2
def baseEnd_1891145 : Nat := 971066372347108620190289

theorem tailTrace_1891145 : CollatzResearch.WordTrace tailWord_1891145 prefixEnd_1891145 971066372347108620190289 := by
  unfold tailWord_1891145
  simp only [CollatzResearch.WordTrace]
  refine ⟨68975724733712121697210889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45983816489141414464807259 68975724733712121697210889)
  ·
    refine ⟨51731793550284091272908167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68975724733712121697210889 51731793550284091272908167)
    ·
      refine ⟨77597690325426136909362251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51731793550284091272908167 77597690325426136909362251)
      ·
        refine ⟨116396535488139205364043377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77597690325426136909362251 116396535488139205364043377)
        ·
          refine ⟨87297401616104404023032533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116396535488139205364043377 87297401616104404023032533)
          ·
            refine ⟨2046032850377446969289825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 87297401616104404023032533 2046032850377446969289825)
            ·
              refine ⟨1534524637783085226967369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046032850377446969289825 1534524637783085226967369)
              ·
                refine ⟨1150893478337313920225527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1534524637783085226967369 1150893478337313920225527)
                ·
                  refine ⟨1726340217505970880338291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150893478337313920225527 1726340217505970880338291)
                  ·
                    refine ⟨2589510326258956320507437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1726340217505970880338291 2589510326258956320507437)
                    ·
                      refine ⟨971066372347108620190289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2589510326258956320507437 971066372347108620190289)
                      ·
                        rfl

theorem cell23_1891145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 1, 1, 3].length) (baseStart_1891145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891145 prefixEnd_1891145 := by exact prefixLift 1891145
  have htrace : WordTrace (prefixWord ++ tailWord_1891145) baseStart_1891145 baseEnd_1891145 := by
    simpa [prefixWord, tailWord_1891145, baseEnd_1891145] using wordTrace_append hprefix tailTrace_1891145
  have hstable : (prefixWord ++ tailWord_1891145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891145).length < 2 ^ (prefixWord ++ tailWord_1891145).sum := by decide
  have hdescent : baseEnd_1891145 < baseStart_1891145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891154 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_1891154 : Nat := 118140960795 + 1891154 * 2 ^ 59
def prefixEnd_1891154 : Nat := 4983230072969 + 3 ^ 40 * 1891154 * 2
def baseEnd_1891154 : Nat := 971070993672999084977747

theorem tailTrace_1891154 : CollatzResearch.WordTrace tailWord_1891154 prefixEnd_1891154 971070993672999084977747 := by
  unfold tailWord_1891154
  simp only [CollatzResearch.WordTrace]
  refine ⟨17244013247669879058572129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45984035327119677489525677 17244013247669879058572129)
  ·
    refine ⟨12933009935752409293929097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17244013247669879058572129 12933009935752409293929097)
    ·
      refine ⟨9699757451814306970446823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12933009935752409293929097 9699757451814306970446823)
      ·
        refine ⟨14549636177721460455670235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9699757451814306970446823 14549636177721460455670235)
        ·
          refine ⟨21824454266582190683505353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14549636177721460455670235 21824454266582190683505353)
          ·
            refine ⟨16368340699936643012629015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21824454266582190683505353 16368340699936643012629015)
            ·
              refine ⟨24552511049904964518943523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16368340699936643012629015 24552511049904964518943523)
              ·
                refine ⟨36828766574857446778415285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24552511049904964518943523 36828766574857446778415285)
                ·
                  refine ⟨3452696866392885635476433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36828766574857446778415285 3452696866392885635476433)
                  ·
                    refine ⟨2589522649794664226607325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3452696866392885635476433 2589522649794664226607325)
                    ·
                      refine ⟨971070993672999084977747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2589522649794664226607325 971070993672999084977747)
                      ·
                        rfl

theorem cell23_1891154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_1891154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891154 prefixEnd_1891154 := by exact prefixLift 1891154
  have htrace : WordTrace (prefixWord ++ tailWord_1891154) baseStart_1891154 baseEnd_1891154 := by
    simpa [prefixWord, tailWord_1891154, baseEnd_1891154] using wordTrace_append hprefix tailTrace_1891154
  have hstable : (prefixWord ++ tailWord_1891154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891154).length < 2 ^ (prefixWord ++ tailWord_1891154).sum := by decide
  have hdescent : baseEnd_1891154 < baseStart_1891154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891184 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 3]
def baseStart_1891184 : Nat := 118140960795 + 1891184 * 2 ^ 59
def prefixEnd_1891184 : Nat := 4983230072969 + 3 ^ 40 * 1891184 * 2
def baseEnd_1891184 : Nat := 971086398092633967602609

theorem tailTrace_1891184 : CollatzResearch.WordTrace tailWord_1891184 prefixEnd_1891184 971086398092633967602609 := by
  unfold tailWord_1891184
  simp only [CollatzResearch.WordTrace]
  refine ⟨34488573590285415678940303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45984764787047220905253737 34488573590285415678940303)
  ·
    refine ⟨51732860385428123518410455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34488573590285415678940303 51732860385428123518410455)
    ·
      refine ⟨77599290578142185277615683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51732860385428123518410455 77599290578142185277615683)
      ·
        refine ⟨116398935867213277916423525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77599290578142185277615683 116398935867213277916423525)
        ·
          refine ⟨21824800475102489609329411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116398935867213277916423525 21824800475102489609329411)
          ·
            refine ⟨32737200712653734413994117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21824800475102489609329411 32737200712653734413994117)
            ·
              refine ⟨6138225133622575202623897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32737200712653734413994117 6138225133622575202623897)
              ·
                refine ⟨4603668850216931401967923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6138225133622575202623897 4603668850216931401967923)
                ·
                  refine ⟨6905503275325397102951885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4603668850216931401967923 6905503275325397102951885)
                  ·
                    refine ⟨2589563728247023913606957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6905503275325397102951885 2589563728247023913606957)
                    ·
                      refine ⟨971086398092633967602609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2589563728247023913606957 971086398092633967602609)
                      ·
                        rfl

theorem cell23_1891184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 3].length) (baseStart_1891184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891184 prefixEnd_1891184 := by exact prefixLift 1891184
  have htrace : WordTrace (prefixWord ++ tailWord_1891184) baseStart_1891184 baseEnd_1891184 := by
    simpa [prefixWord, tailWord_1891184, baseEnd_1891184] using wordTrace_append hprefix tailTrace_1891184
  have hstable : (prefixWord ++ tailWord_1891184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891184).length < 2 ^ (prefixWord ++ tailWord_1891184).sum := by decide
  have hdescent : baseEnd_1891184 < baseStart_1891184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891185 : List Nat := [1, 2, 2, 2, 1, 5, 2, 3, 1, 2, 2]
def baseStart_1891185 : Nat := 118140960795 + 1891185 * 2 ^ 59
def prefixEnd_1891185 : Nat := 4983230072969 + 3 ^ 40 * 1891185 * 2
def baseEnd_1891185 : Nat := 971086911573288463690105

theorem tailTrace_1891185 : CollatzResearch.WordTrace tailWord_1891185 prefixEnd_1891185 971086911573288463690105 := by
  unfold tailWord_1891185
  simp only [CollatzResearch.WordTrace]
  refine ⟨68977183653567208528667009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45984789102378139019111339 68977183653567208528667009)
  ·
    refine ⟨51732887740175406396500257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68977183653567208528667009 51732887740175406396500257)
    ·
      refine ⟨38799665805131554797375193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51732887740175406396500257 38799665805131554797375193)
      ·
        refine ⟨29099749353848666098031395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38799665805131554797375193 29099749353848666098031395)
        ·
          refine ⟨43649624030772999147047093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29099749353848666098031395 43649624030772999147047093)
          ·
            refine ⟨4092152252884968670035665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43649624030772999147047093 4092152252884968670035665)
            ·
              refine ⟨3069114189663726502526749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4092152252884968670035665 3069114189663726502526749)
              ·
                refine ⟨1150917821123897438447531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3069114189663726502526749 1150917821123897438447531)
                ·
                  refine ⟨1726376731685846157671297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150917821123897438447531 1726376731685846157671297)
                  ·
                    refine ⟨1294782548764384618253473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1726376731685846157671297 1294782548764384618253473)
                    ·
                      refine ⟨971086911573288463690105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294782548764384618253473 971086911573288463690105)
                      ·
                        rfl

theorem cell23_1891185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_1891185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891185 prefixEnd_1891185 := by exact prefixLift 1891185
  have htrace : WordTrace (prefixWord ++ tailWord_1891185) baseStart_1891185 baseEnd_1891185 := by
    simpa [prefixWord, tailWord_1891185, baseEnd_1891185] using wordTrace_append hprefix tailTrace_1891185
  have hstable : (prefixWord ++ tailWord_1891185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891185).length < 2 ^ (prefixWord ++ tailWord_1891185).sum := by decide
  have hdescent : baseEnd_1891185 < baseStart_1891185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891222 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1891222 : Nat := 118140960795 + 1891222 * 2 ^ 59
def prefixEnd_1891222 : Nat := 4983230072969 + 3 ^ 40 * 1891222 * 2
def baseEnd_1891222 : Nat := 971105910357504818927435

theorem tailTrace_1891222 : CollatzResearch.WordTrace tailWord_1891222 prefixEnd_1891222 971105910357504818927435 := by
  unfold tailWord_1891222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311158322152072740485245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45985688769622109231842613 4311158322152072740485245)
  ·
    refine ⟨1616684370807027277681967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4311158322152072740485245 1616684370807027277681967)
    ·
      refine ⟨2425026556210540916522951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1616684370807027277681967 2425026556210540916522951)
      ·
        refine ⟨3637539834315811374784427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2425026556210540916522951 3637539834315811374784427)
        ·
          refine ⟨5456309751473717062176641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3637539834315811374784427 5456309751473717062176641)
          ·
            refine ⟨4092232313605287796632481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5456309751473717062176641 4092232313605287796632481)
            ·
              refine ⟨3069174235203965847474361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4092232313605287796632481 3069174235203965847474361)
              ·
                refine ⟨2301880676402974385605771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3069174235203965847474361 2301880676402974385605771)
                ·
                  refine ⟨3452821014604461578408657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301880676402974385605771 3452821014604461578408657)
                  ·
                    refine ⟨2589615760953346183806493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3452821014604461578408657 2589615760953346183806493)
                    ·
                      refine ⟨971105910357504818927435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2589615760953346183806493 971105910357504818927435)
                      ·
                        rfl

theorem cell23_1891222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1891222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891222 prefixEnd_1891222 := by exact prefixLift 1891222
  have htrace : WordTrace (prefixWord ++ tailWord_1891222) baseStart_1891222 baseEnd_1891222 := by
    simpa [prefixWord, tailWord_1891222, baseEnd_1891222] using wordTrace_append hprefix tailTrace_1891222
  have hstable : (prefixWord ++ tailWord_1891222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891222).length < 2 ^ (prefixWord ++ tailWord_1891222).sum := by decide
  have hdescent : baseEnd_1891222 < baseStart_1891222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891241 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 6, 2, 2]
def baseStart_1891241 : Nat := 118140960795 + 1891241 * 2 ^ 59
def prefixEnd_1891241 : Nat := 4983230072969 + 3 ^ 40 * 1891241 * 2
def baseEnd_1891241 : Nat := 971115666489940244589847

theorem tailTrace_1891241 : CollatzResearch.WordTrace tailWord_1891241 prefixEnd_1891241 971115666489940244589847 := by
  unfold tailWord_1891241
  simp only [CollatzResearch.WordTrace]
  refine ⟨68979226141364330092705577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45986150760909553395137051 68979226141364330092705577)
  ·
    refine ⟨51734419606023247569529183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68979226141364330092705577 51734419606023247569529183)
    ·
      refine ⟨77601629409034871354293775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51734419606023247569529183 77601629409034871354293775)
      ·
        refine ⟨116402444113552307031440663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77601629409034871354293775 116402444113552307031440663)
        ·
          refine ⟨174603666170328460547160995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116402444113552307031440663 174603666170328460547160995)
          ·
            refine ⟨261905499255492690820741493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174603666170328460547160995 261905499255492690820741493)
            ·
              refine ⟨24553640555202439764444515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261905499255492690820741493 24553640555202439764444515)
              ·
                refine ⟨36830460832803659646666773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24553640555202439764444515 36830460832803659646666773)
                ·
                  refine ⟨1726427851537671545937505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36830460832803659646666773 1726427851537671545937505)
                  ·
                    refine ⟨1294820888653253659453129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1726427851537671545937505 1294820888653253659453129)
                    ·
                      refine ⟨971115666489940244589847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294820888653253659453129 971115666489940244589847)
                      ·
                        rfl

theorem cell23_1891241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 2, 2].length) (baseStart_1891241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891241 prefixEnd_1891241 := by exact prefixLift 1891241
  have htrace : WordTrace (prefixWord ++ tailWord_1891241) baseStart_1891241 baseEnd_1891241 := by
    simpa [prefixWord, tailWord_1891241, baseEnd_1891241] using wordTrace_append hprefix tailTrace_1891241
  have hstable : (prefixWord ++ tailWord_1891241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891241).length < 2 ^ (prefixWord ++ tailWord_1891241).sum := by decide
  have hdescent : baseEnd_1891241 < baseStart_1891241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891258 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2]
def baseStart_1891258 : Nat := 118140960795 + 1891258 * 2 ^ 59
def prefixEnd_1891258 : Nat := 4983230072969 + 3 ^ 40 * 1891258 * 2
def baseEnd_1891258 : Nat := 971124395661066678077269

theorem tailTrace_1891258 : CollatzResearch.WordTrace tailWord_1891258 prefixEnd_1891258 971124395661066678077269 := by
  unfold tailWord_1891258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17244961545575685499018607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45986564121535161330716285 17244961545575685499018607)
  ·
    refine ⟨25867442318363528248527911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17244961545575685499018607 25867442318363528248527911)
    ·
      refine ⟨38801163477545292372791867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25867442318363528248527911 38801163477545292372791867)
      ·
        refine ⟨58201745216317938559187801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38801163477545292372791867 58201745216317938559187801)
        ·
          refine ⟨43651308912238453919390851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58201745216317938559187801 43651308912238453919390851)
          ·
            refine ⟨65476963368357680879086277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43651308912238453919390851 65476963368357680879086277)
            ·
              refine ⟨12276930631567065164828677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65476963368357680879086277 12276930631567065164828677)
              ·
                refine ⟨2301924493418824718405377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12276930631567065164828677 2301924493418824718405377)
                ·
                  refine ⟨1726443370064118538804033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2301924493418824718405377 1726443370064118538804033)
                  ·
                    refine ⟨1294832527548088904103025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1726443370064118538804033 1294832527548088904103025)
                    ·
                      refine ⟨971124395661066678077269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294832527548088904103025 971124395661066678077269)
                      ·
                        rfl

theorem cell23_1891258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2].length) (baseStart_1891258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891258 prefixEnd_1891258 := by exact prefixLift 1891258
  have htrace : WordTrace (prefixWord ++ tailWord_1891258) baseStart_1891258 baseEnd_1891258 := by
    simpa [prefixWord, tailWord_1891258, baseEnd_1891258] using wordTrace_append hprefix tailTrace_1891258
  have hstable : (prefixWord ++ tailWord_1891258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891258).length < 2 ^ (prefixWord ++ tailWord_1891258).sum := by decide
  have hdescent : baseEnd_1891258 < baseStart_1891258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891264 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 7]
def baseStart_1891264 : Nat := 118140960795 + 1891264 * 2 ^ 59
def prefixEnd_1891264 : Nat := 4983230072969 + 3 ^ 40 * 1891264 * 2
def baseEnd_1891264 : Nat := 107903052949443739400249

theorem tailTrace_1891264 : CollatzResearch.WordTrace tailWord_1891264 prefixEnd_1891264 107903052949443739400249 := by
  unfold tailWord_1891264
  simp only [CollatzResearch.WordTrace]
  refine ⟨34490032510140502510396423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45986710013520670013861897 34490032510140502510396423)
  ·
    refine ⟨51735048765210753765594635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34490032510140502510396423 51735048765210753765594635)
    ·
      refine ⟨77602573147816130648391953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51735048765210753765594635 77602573147816130648391953)
      ·
        refine ⟨58201929860862097986293965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77602573147816130648391953 58201929860862097986293965)
        ·
          refine ⟨21825723697823286744860237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58201929860862097986293965 21825723697823286744860237)
          ·
            refine ⟨8184646386683732529322589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21825723697823286744860237 8184646386683732529322589)
            ·
              refine ⟨3069242395006399698495971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8184646386683732529322589 3069242395006399698495971)
              ·
                refine ⟨4603863592509599547743957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069242395006399698495971 4603863592509599547743957)
                ·
                  refine ⟨107903052949443739400249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4603863592509599547743957 107903052949443739400249)
                  ·
                    rfl

theorem cell23_1891264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 7].length) (baseStart_1891264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891264 prefixEnd_1891264 := by exact prefixLift 1891264
  have htrace : WordTrace (prefixWord ++ tailWord_1891264) baseStart_1891264 baseEnd_1891264 := by
    simpa [prefixWord, tailWord_1891264, baseEnd_1891264] using wordTrace_append hprefix tailTrace_1891264
  have hstable : (prefixWord ++ tailWord_1891264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891264).length < 2 ^ (prefixWord ++ tailWord_1891264).sum := by decide
  have hdescent : baseEnd_1891264 < baseStart_1891264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891274 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_1891274 : Nat := 118140960795 + 1891274 * 2 ^ 59
def prefixEnd_1891274 : Nat := 4983230072969 + 3 ^ 40 * 1891274 * 2
def baseEnd_1891274 : Nat := 971132611351538615477195

theorem tailTrace_1891274 : CollatzResearch.WordTrace tailWord_1891274 prefixEnd_1891274 971132611351538615477195 := by
  unfold tailWord_1891274
  simp only [CollatzResearch.WordTrace]
  refine ⟨17245107437561194182164219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45986953166829851152437917 17245107437561194182164219)
  ·
    refine ⟨25867661156341791273246329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17245107437561194182164219 25867661156341791273246329)
    ·
      refine ⟨19400745867256343454934747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25867661156341791273246329 19400745867256343454934747)
      ·
        refine ⟨29101118800884515182402121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19400745867256343454934747 29101118800884515182402121)
        ·
          refine ⟨21825839100663386386801591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29101118800884515182402121 21825839100663386386801591)
          ·
            refine ⟨32738758650995079580202387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21825839100663386386801591 32738758650995079580202387)
            ·
              refine ⟨49108137976492619370303581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32738758650995079580202387 49108137976492619370303581)
              ·
                refine ⟨18415551741184732263863843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49108137976492619370303581 18415551741184732263863843)
                ·
                  refine ⟨27623327611777098395795765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18415551741184732263863843 27623327611777098395795765)
                  ·
                    refine ⟨2589686963604102974605853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27623327611777098395795765 2589686963604102974605853)
                    ·
                      refine ⟨971132611351538615477195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2589686963604102974605853 971132611351538615477195)
                      ·
                        rfl

theorem cell23_1891274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_1891274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891274 prefixEnd_1891274 := by exact prefixLift 1891274
  have htrace : WordTrace (prefixWord ++ tailWord_1891274) baseStart_1891274 baseEnd_1891274 := by
    simpa [prefixWord, tailWord_1891274, baseEnd_1891274] using wordTrace_append hprefix tailTrace_1891274
  have hstable : (prefixWord ++ tailWord_1891274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891274).length < 2 ^ (prefixWord ++ tailWord_1891274).sum := by decide
  have hdescent : baseEnd_1891274 < baseStart_1891274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891275 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 2, 2, 2]
def baseStart_1891275 : Nat := 118140960795 + 1891275 * 2 ^ 59
def prefixEnd_1891275 : Nat := 4983230072969 + 3 ^ 40 * 1891275 * 2
def baseEnd_1891275 : Nat := 971133124832193111564691

theorem tailTrace_1891275 : CollatzResearch.WordTrace tailWord_1891275 prefixEnd_1891275 971133124832193111564691 := by
  unfold tailWord_1891275
  simp only [CollatzResearch.WordTrace]
  refine ⟨68980466223241153899443279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45986977482160769266295519 68980466223241153899443279)
  ·
    refine ⟨103470699334861730849164919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68980466223241153899443279 103470699334861730849164919)
    ·
      refine ⟨155206049002292596273747379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103470699334861730849164919 155206049002292596273747379)
      ·
        refine ⟨232809073503438894410621069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155206049002292596273747379 232809073503438894410621069)
        ·
          refine ⟨87303402563789585403982901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232809073503438894410621069 87303402563789585403982901)
          ·
            refine ⟨8184693990355273631623397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87303402563789585403982901 8184693990355273631623397)
            ·
              refine ⟨1534630123191613805929387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8184693990355273631623397 1534630123191613805929387)
              ·
                refine ⟨2301945184787420708894081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534630123191613805929387 2301945184787420708894081)
                ·
                  refine ⟨1726458888590565531670561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2301945184787420708894081 1726458888590565531670561)
                  ·
                    refine ⟨1294844166442924148752921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1726458888590565531670561 1294844166442924148752921)
                    ·
                      refine ⟨971133124832193111564691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294844166442924148752921 971133124832193111564691)
                      ·
                        rfl

theorem cell23_1891275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 2, 2, 2].length) (baseStart_1891275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891275 prefixEnd_1891275 := by exact prefixLift 1891275
  have htrace : WordTrace (prefixWord ++ tailWord_1891275) baseStart_1891275 baseEnd_1891275 := by
    simpa [prefixWord, tailWord_1891275, baseEnd_1891275] using wordTrace_append hprefix tailTrace_1891275
  have hstable : (prefixWord ++ tailWord_1891275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891275).length < 2 ^ (prefixWord ++ tailWord_1891275).sum := by decide
  have hdescent : baseEnd_1891275 < baseStart_1891275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891304 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1891304 : Nat := 118140960795 + 1891304 * 2 ^ 59
def prefixEnd_1891304 : Nat := 4983230072969 + 3 ^ 40 * 1891304 * 2
def baseEnd_1891304 : Nat := 971148015771173498102057

theorem tailTrace_1891304 : CollatzResearch.WordTrace tailWord_1891304 prefixEnd_1891304 971148015771173498102057 := by
  unfold tailWord_1891304
  simp only [CollatzResearch.WordTrace]
  refine ⟨34490761970068045926124483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45987682626757394568165977 34490761970068045926124483)
  ·
    refine ⟨51736142955102068889186725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34490761970068045926124483 51736142955102068889186725)
    ·
      refine ⟨9700526804081637916722511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51736142955102068889186725 9700526804081637916722511)
      ·
        refine ⟨14550790206122456875083767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9700526804081637916722511 14550790206122456875083767)
        ·
          refine ⟨21826185309183685312625651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14550790206122456875083767 21826185309183685312625651)
          ·
            refine ⟨32739277963775527968938477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21826185309183685312625651 32739277963775527968938477)
            ·
              refine ⟨12277229236415822988351929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32739277963775527968938477 12277229236415822988351929)
              ·
                refine ⟨9207921927311867241263947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12277229236415822988351929 9207921927311867241263947)
                ·
                  refine ⟨13811882890967800861895921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9207921927311867241263947 13811882890967800861895921)
                  ·
                    refine ⟨10358912168225850646421941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13811882890967800861895921 10358912168225850646421941)
                    ·
                      refine ⟨971148015771173498102057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10358912168225850646421941 971148015771173498102057)
                      ·
                        rfl

theorem cell23_1891304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1891304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891304 prefixEnd_1891304 := by exact prefixLift 1891304
  have htrace : WordTrace (prefixWord ++ tailWord_1891304) baseStart_1891304 baseEnd_1891304 := by
    simpa [prefixWord, tailWord_1891304, baseEnd_1891304] using wordTrace_append hprefix tailTrace_1891304
  have hstable : (prefixWord ++ tailWord_1891304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891304).length < 2 ^ (prefixWord ++ tailWord_1891304).sum := by decide
  have hdescent : baseEnd_1891304 < baseStart_1891304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891318 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_1891318 : Nat := 118140960795 + 1891318 * 2 ^ 59
def prefixEnd_1891318 : Nat := 4983230072969 + 3 ^ 40 * 1891318 * 2
def baseEnd_1891318 : Nat := 971155204500336443326993

theorem tailTrace_1891318 : CollatzResearch.WordTrace tailWord_1891318 prefixEnd_1891318 971155204500336443326993 := by
  unfold tailWord_1891318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311377160130335765203663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45988023041390248162172405 4311377160130335765203663)
  ·
    refine ⟨6467065740195503647805495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4311377160130335765203663 6467065740195503647805495)
    ·
      refine ⟨9700598610293255471708243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6467065740195503647805495 9700598610293255471708243)
      ·
        refine ⟨14550897915439883207562365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9700598610293255471708243 14550897915439883207562365)
        ·
          refine ⟨5456586718289956202835887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14550897915439883207562365 5456586718289956202835887)
          ·
            refine ⟨8184880077434934304253831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5456586718289956202835887 8184880077434934304253831)
            ·
              refine ⟨12277320116152401456380747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8184880077434934304253831 12277320116152401456380747)
              ·
                refine ⟨18415980174228602184571121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12277320116152401456380747 18415980174228602184571121)
                ·
                  refine ⟨13811985130671451638428341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18415980174228602184571121 13811985130671451638428341)
                  ·
                    refine ⟨1294873606000448591102657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13811985130671451638428341 1294873606000448591102657)
                    ·
                      refine ⟨971155204500336443326993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1294873606000448591102657 971155204500336443326993)
                      ·
                        rfl

theorem cell23_1891318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_1891318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891318 prefixEnd_1891318 := by exact prefixLift 1891318
  have htrace : WordTrace (prefixWord ++ tailWord_1891318) baseStart_1891318 baseEnd_1891318 := by
    simpa [prefixWord, tailWord_1891318, baseEnd_1891318] using wordTrace_append hprefix tailTrace_1891318
  have hstable : (prefixWord ++ tailWord_1891318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891318).length < 2 ^ (prefixWord ++ tailWord_1891318).sum := by decide
  have hdescent : baseEnd_1891318 < baseStart_1891318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891354 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 8]
def baseStart_1891354 : Nat := 118140960795 + 1891354 * 2 ^ 59
def prefixEnd_1891354 : Nat := 4983230072969 + 3 ^ 40 * 1891354 * 2
def baseEnd_1891354 : Nat := 107908187755988700275203

theorem tailTrace_1891354 : CollatzResearch.WordTrace tailWord_1891354 prefixEnd_1891354 107908187755988700275203 := by
  unfold tailWord_1891354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17245836897488737597892279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45988898393303300261046077 17245836897488737597892279)
  ·
    refine ⟨25868755346233106396838419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17245836897488737597892279 25868755346233106396838419)
    ·
      refine ⟨38803133019349659595257629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25868755346233106396838419 38803133019349659595257629)
      ·
        refine ⟨14551174882256122348221611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38803133019349659595257629 14551174882256122348221611)
        ·
          refine ⟨21826762323384183522332417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14551174882256122348221611 21826762323384183522332417)
          ·
            refine ⟨16370071742538137641749313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21826762323384183522332417 16370071742538137641749313)
            ·
              refine ⟨12277553806903603231311985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16370071742538137641749313 12277553806903603231311985)
              ·
                refine ⟨9208165355177702423483989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12277553806903603231311985 9208165355177702423483989)
                ·
                  refine ⟨107908187755988700275203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9208165355177702423483989 107908187755988700275203)
                  ·
                    rfl

theorem cell23_1891354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_1891354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891354 prefixEnd_1891354 := by exact prefixLift 1891354
  have htrace : WordTrace (prefixWord ++ tailWord_1891354) baseStart_1891354 baseEnd_1891354 := by
    simpa [prefixWord, tailWord_1891354, baseEnd_1891354] using wordTrace_append hprefix tailTrace_1891354
  have hstable : (prefixWord ++ tailWord_1891354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891354).length < 2 ^ (prefixWord ++ tailWord_1891354).sum := by decide
  have hdescent : baseEnd_1891354 < baseStart_1891354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891388 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 6]
def baseStart_1891388 : Nat := 118140960795 + 1891388 * 2 ^ 59
def prefixEnd_1891388 : Nat := 4983230072969 + 3 ^ 40 * 1891388 * 2
def baseEnd_1891388 : Nat := 107910127571794574383519

theorem tailTrace_1891388 : CollatzResearch.WordTrace tailWord_1891388 prefixEnd_1891388 107910127571794574383519 := by
  unfold tailWord_1891388
  simp only [CollatzResearch.WordTrace]
  refine ⟨34492293835915887099153409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45989725114554516132204545 34492293835915887099153409)
  ·
    refine ⟨25869220376936915324365057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34492293835915887099153409 25869220376936915324365057)
    ·
      refine ⟨19401915282702686493273793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25869220376936915324365057 19401915282702686493273793)
      ·
        refine ⟨14551436462027014869955345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19401915282702686493273793 14551436462027014869955345)
        ·
          refine ⟨10913577346520261152466509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14551436462027014869955345 10913577346520261152466509)
          ·
            refine ⟨4092591504945097932174941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10913577346520261152466509 4092591504945097932174941)
            ·
              refine ⟨1534721814354411724565603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4092591504945097932174941 1534721814354411724565603)
              ·
                refine ⟨2302082721531617586848405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534721814354411724565603 2302082721531617586848405)
                ·
                  refine ⟨107910127571794574383519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2302082721531617586848405 107910127571794574383519)
                  ·
                    rfl

theorem cell23_1891388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_1891388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891388 prefixEnd_1891388 := by exact prefixLift 1891388
  have htrace : WordTrace (prefixWord ++ tailWord_1891388) baseStart_1891388 baseEnd_1891388 := by
    simpa [prefixWord, tailWord_1891388, baseEnd_1891388] using wordTrace_append hprefix tailTrace_1891388
  have hstable : (prefixWord ++ tailWord_1891388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891388).length < 2 ^ (prefixWord ++ tailWord_1891388).sum := by decide
  have hdescent : baseEnd_1891388 < baseStart_1891388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891505 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1891505 : Nat := 118140960795 + 1891505 * 2 ^ 59
def prefixEnd_1891505 : Nat := 4983230072969 + 3 ^ 40 * 1891505 * 2
def baseEnd_1891505 : Nat := 971251225382727211688633

theorem tailTrace_1891505 : CollatzResearch.WordTrace tailWord_1891505 prefixEnd_1891505 971251225382727211688633 := by
  unfold tailWord_1891505
  simp only [CollatzResearch.WordTrace]
  refine ⟨68988855012407903180315969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45992570008271935453543979 68988855012407903180315969)
  ·
    refine ⟨51741641259305927385236977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68988855012407903180315969 51741641259305927385236977)
    ·
      refine ⟨38806230944479445538927733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51741641259305927385236977 38806230944479445538927733)
      ·
        refine ⟨3638084151044948019274475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38806230944479445538927733 3638084151044948019274475)
        ·
          refine ⟨5457126226567422028911713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3638084151044948019274475 5457126226567422028911713)
          ·
            refine ⟨4092844669925566521683785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5457126226567422028911713 4092844669925566521683785)
            ·
              refine ⟨3069633502444174891262839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4092844669925566521683785 3069633502444174891262839)
              ·
                refine ⟨4604450253666262336894259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069633502444174891262839 4604450253666262336894259)
                ·
                  refine ⟨6906675380499393505341389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604450253666262336894259 6906675380499393505341389)
                  ·
                    refine ⟨2590003267687272564503021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6906675380499393505341389 2590003267687272564503021)
                    ·
                      refine ⟨971251225382727211688633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2590003267687272564503021 971251225382727211688633)
                      ·
                        rfl

theorem cell23_1891505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1891505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891505 prefixEnd_1891505 := by exact prefixLift 1891505
  have htrace : WordTrace (prefixWord ++ tailWord_1891505) baseStart_1891505 baseEnd_1891505 := by
    simpa [prefixWord, tailWord_1891505, baseEnd_1891505] using wordTrace_append hprefix tailTrace_1891505
  have hstable : (prefixWord ++ tailWord_1891505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891505).length < 2 ^ (prefixWord ++ tailWord_1891505).sum := by decide
  have hdescent : baseEnd_1891505 < baseStart_1891505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891511 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_1891511 : Nat := 118140960795 + 1891511 * 2 ^ 59
def prefixEnd_1891511 : Nat := 4983230072969 + 3 ^ 40 * 1891511 * 2
def baseEnd_1891511 : Nat := 971254306266654188213605

theorem tailTrace_1891511 : CollatzResearch.WordTrace tailWord_1891511 prefixEnd_1891511 971254306266654188213605 := by
  unfold tailWord_1891511
  simp only [CollatzResearch.WordTrace]
  refine ⟨68989073850386166205034387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45992715900257444136689591 68989073850386166205034387)
  ·
    refine ⟨103483610775579249307551581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68989073850386166205034387 103483610775579249307551581)
    ·
      refine ⟨38806354040842218490331843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103483610775579249307551581 38806354040842218490331843)
      ·
        refine ⟨58209531061263327735497765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38806354040842218490331843 58209531061263327735497765)
        ·
          refine ⟨10914287073986873950405831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58209531061263327735497765 10914287073986873950405831)
          ·
            refine ⟨16371430610980310925608747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10914287073986873950405831 16371430610980310925608747)
            ·
              refine ⟨24557145916470466388413121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16371430610980310925608747 24557145916470466388413121)
              ·
                refine ⟨18417859437352849791309841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24557145916470466388413121 18417859437352849791309841)
                ·
                  refine ⟨13813394578014637343482381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18417859437352849791309841 13813394578014637343482381)
                  ·
                    refine ⟨5180022966755489003805893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13813394578014637343482381 5180022966755489003805893)
                    ·
                      refine ⟨971254306266654188213605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5180022966755489003805893 971254306266654188213605)
                      ·
                        rfl

theorem cell23_1891511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_1891511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891511 prefixEnd_1891511 := by exact prefixLift 1891511
  have htrace : WordTrace (prefixWord ++ tailWord_1891511) baseStart_1891511 baseEnd_1891511 := by
    simpa [prefixWord, tailWord_1891511, baseEnd_1891511] using wordTrace_append hprefix tailTrace_1891511
  have hstable : (prefixWord ++ tailWord_1891511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891511).length < 2 ^ (prefixWord ++ tailWord_1891511).sum := by decide
  have hdescent : baseEnd_1891511 < baseStart_1891511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891526 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1891526 : Nat := 118140960795 + 1891526 * 2 ^ 59
def prefixEnd_1891526 : Nat := 4983230072969 + 3 ^ 40 * 1891526 * 2
def baseEnd_1891526 : Nat := 971262008476471629526037

theorem tailTrace_1891526 : CollatzResearch.WordTrace tailWord_1891526 prefixEnd_1891526 971262008476471629526037 := by
  unfold tailWord_1891526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2155925654541619492713451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45993080630221215844553621 2155925654541619492713451)
  ·
    refine ⟨3233888481812429239070177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2155925654541619492713451 3233888481812429239070177)
    ·
      refine ⟨2425416361359321929302633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3233888481812429239070177 2425416361359321929302633)
      ·
        refine ⟨1819062271019491446976975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2425416361359321929302633 1819062271019491446976975)
        ·
          refine ⟨2728593406529237170465463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819062271019491446976975 2728593406529237170465463)
          ·
            refine ⟨4092890109793855755698195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728593406529237170465463 4092890109793855755698195)
            ·
              refine ⟨6139335164690783633547293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092890109793855755698195 6139335164690783633547293)
              ·
                refine ⟨2302250686759043862580235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6139335164690783633547293 2302250686759043862580235)
                ·
                  refine ⟨3453376030138565793870353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302250686759043862580235 3453376030138565793870353)
                  ·
                    refine ⟨2590032022603924345402765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3453376030138565793870353 2590032022603924345402765)
                    ·
                      refine ⟨971262008476471629526037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2590032022603924345402765 971262008476471629526037)
                      ·
                        rfl

theorem cell23_1891526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1891526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891526 prefixEnd_1891526 := by exact prefixLift 1891526
  have htrace : WordTrace (prefixWord ++ tailWord_1891526) baseStart_1891526 baseEnd_1891526 := by
    simpa [prefixWord, tailWord_1891526, baseEnd_1891526] using wordTrace_append hprefix tailTrace_1891526
  have hstable : (prefixWord ++ tailWord_1891526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891526).length < 2 ^ (prefixWord ++ tailWord_1891526).sum := by decide
  have hdescent : baseEnd_1891526 < baseStart_1891526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891531 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 3]
def baseStart_1891531 : Nat := 118140960795 + 1891531 * 2 ^ 59
def prefixEnd_1891531 : Nat := 4983230072969 + 3 ^ 40 * 1891531 * 2
def baseEnd_1891531 : Nat := 971264575879744109963513

theorem tailTrace_1891531 : CollatzResearch.WordTrace tailWord_1891531 prefixEnd_1891531 971264575879744109963513 := by
  unfold tailWord_1891531
  simp only [CollatzResearch.WordTrace]
  refine ⟨68989803310313709620762447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45993202206875806413841631 68989803310313709620762447)
  ·
    refine ⟨103484704965470564431143671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68989803310313709620762447 103484704965470564431143671)
    ·
      refine ⟨155227057448205846646715507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103484704965470564431143671 155227057448205846646715507)
      ·
        refine ⟨232840586172308769970073261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155227057448205846646715507 232840586172308769970073261)
        ·
          refine ⟨87315219814615788738777473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232840586172308769970073261 87315219814615788738777473)
          ·
            refine ⟨65486414860961841554083105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87315219814615788738777473 65486414860961841554083105)
            ·
              refine ⟨49114811145721381165562329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65486414860961841554083105 49114811145721381165562329)
              ·
                refine ⟨36836108359291035874171747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49114811145721381165562329 36836108359291035874171747)
                ·
                  refine ⟨55254162538936553811257621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36836108359291035874171747 55254162538936553811257621)
                  ·
                    refine ⟨2590038869012650959902701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55254162538936553811257621 2590038869012650959902701)
                    ·
                      refine ⟨971264575879744109963513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2590038869012650959902701 971264575879744109963513)
                      ·
                        rfl

theorem cell23_1891531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 3].length) (baseStart_1891531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891531 prefixEnd_1891531 := by exact prefixLift 1891531
  have htrace : WordTrace (prefixWord ++ tailWord_1891531) baseStart_1891531 baseEnd_1891531 := by
    simpa [prefixWord, tailWord_1891531, baseEnd_1891531] using wordTrace_append hprefix tailTrace_1891531
  have hstable : (prefixWord ++ tailWord_1891531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891531).length < 2 ^ (prefixWord ++ tailWord_1891531).sum := by decide
  have hdescent : baseEnd_1891531 < baseStart_1891531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891551 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 7]
def baseStart_1891551 : Nat := 118140960795 + 1891551 * 2 ^ 59
def prefixEnd_1891551 : Nat := 4983230072969 + 3 ^ 40 * 1891551 * 2
def baseEnd_1891551 : Nat := 107919427276981559079269

theorem tailTrace_1891551 : CollatzResearch.WordTrace tailWord_1891551 prefixEnd_1891551 107919427276981559079269 := by
  unfold tailWord_1891551
  simp only [CollatzResearch.WordTrace]
  refine ⟨68990532770241253036490507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45993688513494168690993671 68990532770241253036490507)
  ·
    refine ⟨103485799155361879554735761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68990532770241253036490507 103485799155361879554735761)
    ·
      refine ⟨77614349366521409666051821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103485799155361879554735761 77614349366521409666051821)
      ·
        refine ⟨29105381012445528624769433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77614349366521409666051821 29105381012445528624769433)
        ·
          refine ⟨21829035759334146468577075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29105381012445528624769433 21829035759334146468577075)
          ·
            refine ⟨32743553639001219702865613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21829035759334146468577075 32743553639001219702865613)
            ·
              refine ⟨12278832614625457388574605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32743553639001219702865613 12278832614625457388574605)
              ·
                refine ⟨4604562230484546520715477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12278832614625457388574605 4604562230484546520715477)
                ·
                  refine ⟨107919427276981559079269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4604562230484546520715477 107919427276981559079269)
                  ·
                    rfl

theorem cell23_1891551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 7].length) (baseStart_1891551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891551 prefixEnd_1891551 := by exact prefixLift 1891551
  have htrace : WordTrace (prefixWord ++ tailWord_1891551) baseStart_1891551 baseEnd_1891551 := by
    simpa [prefixWord, tailWord_1891551, baseEnd_1891551] using wordTrace_append hprefix tailTrace_1891551
  have hstable : (prefixWord ++ tailWord_1891551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891551).length < 2 ^ (prefixWord ++ tailWord_1891551).sum := by decide
  have hdescent : baseEnd_1891551 < baseStart_1891551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891562 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_1891562 : Nat := 118140960795 + 1891562 * 2 ^ 59
def prefixEnd_1891562 : Nat := 4983230072969 + 3 ^ 40 * 1891562 * 2
def baseEnd_1891562 : Nat := 971280493780033488675871

theorem tailTrace_1891562 : CollatzResearch.WordTrace tailWord_1891562 prefixEnd_1891562 971280493780033488675871 := by
  unfold tailWord_1891562
  simp only [CollatzResearch.WordTrace]
  refine ⟨17247733493300350478785235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45993955982134267943427293 17247733493300350478785235)
  ·
    refine ⟨25871600239950525718177853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17247733493300350478785235 25871600239950525718177853)
    ·
      refine ⟨9701850089981447144316695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25871600239950525718177853 9701850089981447144316695)
      ·
        refine ⟨14552775134972170716475043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9701850089981447144316695 14552775134972170716475043)
        ·
          refine ⟨21829162702458256074712565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14552775134972170716475043 21829162702458256074712565)
          ·
            refine ⟨2046484003355461507004303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21829162702458256074712565 2046484003355461507004303)
            ·
              refine ⟨3069726005033192260506455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046484003355461507004303 3069726005033192260506455)
              ·
                refine ⟨4604589007549788390759683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069726005033192260506455 4604589007549788390759683)
                ·
                  refine ⟨6906883511324682586139525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604589007549788390759683 6906883511324682586139525)
                  ·
                    refine ⟨1295040658373377984901161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6906883511324682586139525 1295040658373377984901161)
                    ·
                      refine ⟨971280493780033488675871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295040658373377984901161 971280493780033488675871)
                      ·
                        rfl

theorem cell23_1891562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_1891562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891562 prefixEnd_1891562 := by exact prefixLift 1891562
  have htrace : WordTrace (prefixWord ++ tailWord_1891562) baseStart_1891562 baseEnd_1891562 := by
    simpa [prefixWord, tailWord_1891562, baseEnd_1891562] using wordTrace_append hprefix tailTrace_1891562
  have hstable : (prefixWord ++ tailWord_1891562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891562).length < 2 ^ (prefixWord ++ tailWord_1891562).sum := by decide
  have hdescent : baseEnd_1891562 < baseStart_1891562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891585 : List Nat := [1, 2, 4, 1, 1, 3, 3, 3, 5]
def baseStart_1891585 : Nat := 118140960795 + 1891585 * 2 ^ 59
def prefixEnd_1891585 : Nat := 4983230072969 + 3 ^ 40 * 1891585 * 2
def baseEnd_1891585 : Nat := 107921367092787433187585

theorem tailTrace_1891585 : CollatzResearch.WordTrace tailWord_1891585 prefixEnd_1891585 107921367092787433187585 := by
  unfold tailWord_1891585
  simp only [CollatzResearch.WordTrace]
  refine ⟨68991772852118076843228209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45994515234745384562152139 68991772852118076843228209)
  ·
    refine ⟨51743829639088557632421157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68991772852118076843228209 51743829639088557632421157)
    ·
      refine ⟨9701968057329104556078967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51743829639088557632421157 9701968057329104556078967)
      ·
        refine ⟨14552952085993656834118451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9701968057329104556078967 14552952085993656834118451)
        ·
          refine ⟨21829428128990485251177677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14552952085993656834118451 21829428128990485251177677)
          ·
            refine ⟨8186035548371431969191629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21829428128990485251177677 8186035548371431969191629)
            ·
              refine ⟨3069763330639286988446861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8186035548371431969191629 3069763330639286988446861)
              ·
                refine ⟨1151161248989732620667573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3069763330639286988446861 1151161248989732620667573)
                ·
                  refine ⟨107921367092787433187585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1151161248989732620667573 107921367092787433187585)
                  ·
                    rfl

theorem cell23_1891585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 5].length) (baseStart_1891585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891585 prefixEnd_1891585 := by exact prefixLift 1891585
  have htrace : WordTrace (prefixWord ++ tailWord_1891585) baseStart_1891585 baseEnd_1891585 := by
    simpa [prefixWord, tailWord_1891585, baseEnd_1891585] using wordTrace_append hprefix tailTrace_1891585
  have hstable : (prefixWord ++ tailWord_1891585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891585).length < 2 ^ (prefixWord ++ tailWord_1891585).sum := by decide
  have hdescent : baseEnd_1891585 < baseStart_1891585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891598 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_1891598 : Nat := 118140960795 + 1891598 * 2 ^ 59
def prefixEnd_1891598 : Nat := 4983230072969 + 3 ^ 40 * 1891598 * 2
def baseEnd_1891598 : Nat := 323766326361198449275235

theorem tailTrace_1891598 : CollatzResearch.WordTrace tailWord_1891598 prefixEnd_1891598 323766326361198449275235 := by
  unfold tailWord_1891598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8624030875133872507931431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45994831334047320042300965 8624030875133872507931431)
  ·
    refine ⟨12936046312700808761897147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8624030875133872507931431 12936046312700808761897147)
    ·
      refine ⟨19404069469051213142845721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12936046312700808761897147 19404069469051213142845721)
      ·
        refine ⟨14553052101788409857134291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19404069469051213142845721 14553052101788409857134291)
        ·
          refine ⟨21829578152682614785701437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14553052101788409857134291 21829578152682614785701437)
          ·
            refine ⟨8186091807255980544638039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21829578152682614785701437 8186091807255980544638039)
            ·
              refine ⟨12279137710883970816957059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8186091807255980544638039 12279137710883970816957059)
              ·
                refine ⟨18418706566325956225435589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12279137710883970816957059 18418706566325956225435589)
                ·
                  refine ⟨3453507481186116792269173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18418706566325956225435589 3453507481186116792269173)
                  ·
                    refine ⟨323766326361198449275235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3453507481186116792269173 323766326361198449275235)
                    ·
                      rfl

theorem cell23_1891598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_1891598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891598 prefixEnd_1891598 := by exact prefixLift 1891598
  have htrace : WordTrace (prefixWord ++ tailWord_1891598) baseStart_1891598 baseEnd_1891598 := by
    simpa [prefixWord, tailWord_1891598, baseEnd_1891598] using wordTrace_append hprefix tailTrace_1891598
  have hstable : (prefixWord ++ tailWord_1891598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891598).length < 2 ^ (prefixWord ++ tailWord_1891598).sum := by decide
  have hdescent : baseEnd_1891598 < baseStart_1891598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891608 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1891608 : Nat := 118140960795 + 1891608 * 2 ^ 59
def prefixEnd_1891608 : Nat := 4983230072969 + 3 ^ 40 * 1891608 * 2
def baseEnd_1891608 : Nat := 971304113890140308700659

theorem tailTrace_1891608 : CollatzResearch.WordTrace tailWord_1891608 prefixEnd_1891608 971304113890140308700659 := by
  unfold tailWord_1891608
  simp only [CollatzResearch.WordTrace]
  refine ⟨34496305865517375885657739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45995074487356501180876985 34496305865517375885657739)
  ·
    refine ⟨51744458798276063828486609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34496305865517375885657739 51744458798276063828486609)
    ·
      refine ⟨38808344098707047871364957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51744458798276063828486609 38808344098707047871364957)
      ·
        refine ⟨14553129037015142951761859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38808344098707047871364957 14553129037015142951761859)
        ·
          refine ⟨21829693555522714427642789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14553129037015142951761859 21829693555522714427642789)
          ·
            refine ⟨4093067541660508955183023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21829693555522714427642789 4093067541660508955183023)
            ·
              refine ⟨6139601312490763432774535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093067541660508955183023 6139601312490763432774535)
              ·
                refine ⟨9209401968736145149161803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139601312490763432774535 9209401968736145149161803)
                ·
                  refine ⟨13814102953104217723742705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9209401968736145149161803 13814102953104217723742705)
                  ·
                    refine ⟨10360577214828163292807029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13814102953104217723742705 10360577214828163292807029)
                    ·
                      refine ⟨971304113890140308700659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10360577214828163292807029 971304113890140308700659)
                      ·
                        rfl

theorem cell23_1891608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1891608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891608 prefixEnd_1891608 := by exact prefixLift 1891608
  have htrace : WordTrace (prefixWord ++ tailWord_1891608) baseStart_1891608 baseEnd_1891608 := by
    simpa [prefixWord, tailWord_1891608, baseEnd_1891608] using wordTrace_append hprefix tailTrace_1891608
  have hstable : (prefixWord ++ tailWord_1891608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891608).length < 2 ^ (prefixWord ++ tailWord_1891608).sum := by decide
  have hdescent : baseEnd_1891608 < baseStart_1891608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891628 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 5, 4]
def baseStart_1891628 : Nat := 118140960795 + 1891628 * 2 ^ 59
def prefixEnd_1891628 : Nat := 4983230072969 + 3 ^ 40 * 1891628 * 2
def baseEnd_1891628 : Nat := 323771461167743410150189

theorem tailTrace_1891628 : CollatzResearch.WordTrace tailWord_1891628 prefixEnd_1891628 323771461167743410150189 := by
  unfold tailWord_1891628
  simp only [CollatzResearch.WordTrace]
  refine ⟨34496670595481147593521769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45995560793974863458029025 34496670595481147593521769)
  ·
    refine ⟨25872502946610860695141327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34496670595481147593521769 25872502946610860695141327)
    ·
      refine ⟨38808754419916291042711991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25872502946610860695141327 38808754419916291042711991)
      ·
        refine ⟨58213131629874436564067987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38808754419916291042711991 58213131629874436564067987)
        ·
          refine ⟨87319697444811654846101981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58213131629874436564067987 87319697444811654846101981)
          ·
            refine ⟨32744886541804370567288243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87319697444811654846101981 32744886541804370567288243)
            ·
              refine ⟨49117329812706555850932365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32744886541804370567288243 49117329812706555850932365)
              ·
                refine ⟨18418998679764958444099637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49117329812706555850932365 18418998679764958444099637)
                ·
                  refine ⟨1726781126227964854134341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18418998679764958444099637 1726781126227964854134341)
                  ·
                    refine ⟨323771461167743410150189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1726781126227964854134341 323771461167743410150189)
                    ·
                      rfl

theorem cell23_1891628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_1891628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891628 prefixEnd_1891628 := by exact prefixLift 1891628
  have htrace : WordTrace (prefixWord ++ tailWord_1891628) baseStart_1891628 baseEnd_1891628 := by
    simpa [prefixWord, tailWord_1891628, baseEnd_1891628] using wordTrace_append hprefix tailTrace_1891628
  have hstable : (prefixWord ++ tailWord_1891628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891628).length < 2 ^ (prefixWord ++ tailWord_1891628).sum := by decide
  have hdescent : baseEnd_1891628 < baseStart_1891628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891631 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_1891631 : Nat := 118140960795 + 1891631 * 2 ^ 59
def prefixEnd_1891631 : Nat := 4983230072969 + 3 ^ 40 * 1891631 * 2
def baseEnd_1891631 : Nat := 971315923945193718713053

theorem tailTrace_1891631 : CollatzResearch.WordTrace tailWord_1891631 prefixEnd_1891631 971315923945193718713053 := by
  unfold tailWord_1891631
  simp only [CollatzResearch.WordTrace]
  refine ⟨68993450609951426699402747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45995633739967617799601831 68993450609951426699402747)
  ·
    refine ⟨103490175914927140049104121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68993450609951426699402747 103490175914927140049104121)
    ·
      refine ⟨77617631936195355036828091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103490175914927140049104121 77617631936195355036828091)
      ·
        refine ⟨116426447904293032555242137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77617631936195355036828091 116426447904293032555242137)
        ·
          refine ⟨87319835928219774416431603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116426447904293032555242137 87319835928219774416431603)
          ·
            refine ⟨130979753892329661624647405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87319835928219774416431603 130979753892329661624647405)
            ·
              refine ⟨49117407709623623109242777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130979753892329661624647405 49117407709623623109242777)
              ·
                refine ⟨36838055782217717331932083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49117407709623623109242777 36838055782217717331932083)
                ·
                  refine ⟨55257083673326575997898125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36838055782217717331932083 55257083673326575997898125)
                  ·
                    refine ⟨20721406377497465999211797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55257083673326575997898125 20721406377497465999211797)
                    ·
                      refine ⟨971315923945193718713053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20721406377497465999211797 971315923945193718713053)
                      ·
                        rfl

theorem cell23_1891631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_1891631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891631 prefixEnd_1891631 := by exact prefixLift 1891631
  have htrace : WordTrace (prefixWord ++ tailWord_1891631) baseStart_1891631 baseEnd_1891631 := by
    simpa [prefixWord, tailWord_1891631, baseEnd_1891631] using wordTrace_append hprefix tailTrace_1891631
  have hstable : (prefixWord ++ tailWord_1891631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891631).length < 2 ^ (prefixWord ++ tailWord_1891631).sum := by decide
  have hdescent : baseEnd_1891631 < baseStart_1891631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891635 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 4]
def baseStart_1891635 : Nat := 118140960795 + 1891635 * 2 ^ 59
def prefixEnd_1891635 : Nat := 4983230072969 + 3 ^ 40 * 1891635 * 2
def baseEnd_1891635 : Nat := 971317977867811703063035

theorem tailTrace_1891635 : CollatzResearch.WordTrace tailWord_1891635 prefixEnd_1891635 971317977867811703063035 := by
  unfold tailWord_1891635
  simp only [CollatzResearch.WordTrace]
  refine ⟨68993596501936935382548359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45995731001291290255032239 68993596501936935382548359)
  ·
    refine ⟨103490394752905403073822539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68993596501936935382548359 103490394752905403073822539)
    ·
      refine ⟨155235592129358104610733809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103490394752905403073822539 155235592129358104610733809)
      ·
        refine ⟨116426694097018578458050357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155235592129358104610733809 116426694097018578458050357)
        ·
          refine ⟨10915002571595491730442221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116426694097018578458050357 10915002571595491730442221)
          ·
            refine ⟨4093125964348309398915833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10915002571595491730442221 4093125964348309398915833)
            ·
              refine ⟨3069844473261232049186875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4093125964348309398915833 3069844473261232049186875)
              ·
                refine ⟨4604766709891848073780313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069844473261232049186875 4604766709891848073780313)
                ·
                  refine ⟨3453575032418886055335235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4604766709891848073780313 3453575032418886055335235)
                  ·
                    refine ⟨5180362548628329083002853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3453575032418886055335235 5180362548628329083002853)
                    ·
                      refine ⟨971317977867811703063035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5180362548628329083002853 971317977867811703063035)
                      ·
                        rfl

theorem cell23_1891635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 4].length) (baseStart_1891635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891635 prefixEnd_1891635 := by exact prefixLift 1891635
  have htrace : WordTrace (prefixWord ++ tailWord_1891635) baseStart_1891635 baseEnd_1891635 := by
    simpa [prefixWord, tailWord_1891635, baseEnd_1891635] using wordTrace_append hprefix tailTrace_1891635
  have hstable : (prefixWord ++ tailWord_1891635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891635).length < 2 ^ (prefixWord ++ tailWord_1891635).sum := by decide
  have hdescent : baseEnd_1891635 < baseStart_1891635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891652 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1891652 : Nat := 118140960795 + 1891652 * 2 ^ 59
def prefixEnd_1891652 : Nat := 4983230072969 + 3 ^ 40 * 1891652 * 2
def baseEnd_1891652 : Nat := 971326707038938136550457

theorem tailTrace_1891652 : CollatzResearch.WordTrace tailWord_1891652 prefixEnd_1891652 971326707038938136550457 := by
  unfold tailWord_1891652
  simp only [CollatzResearch.WordTrace]
  refine ⟨34497108271437673642958605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45996144361916898190611473 34497108271437673642958605)
  ·
    refine ⟨12936415601789127616109477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34497108271437673642958605 12936415601789127616109477)
    ·
      refine ⟨2425577925335461428020527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12936415601789127616109477 2425577925335461428020527)
      ·
        refine ⟨3638366888003192142030791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2425577925335461428020527 3638366888003192142030791)
        ·
          refine ⟨5457550332004788213046187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3638366888003192142030791 5457550332004788213046187)
          ·
            refine ⟨8186325498007182319569281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5457550332004788213046187 8186325498007182319569281)
            ·
              refine ⟨6139744123505386739676961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8186325498007182319569281 6139744123505386739676961)
              ·
                refine ⟨4604808092629040054757721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6139744123505386739676961 4604808092629040054757721)
                ·
                  refine ⟨3453606069471780041068291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4604808092629040054757721 3453606069471780041068291)
                  ·
                    refine ⟨5180409104207670061602437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3453606069471780041068291 5180409104207670061602437)
                    ·
                      refine ⟨971326707038938136550457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5180409104207670061602437 971326707038938136550457)
                      ·
                        rfl

theorem cell23_1891652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1891652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891652 prefixEnd_1891652 := by exact prefixLift 1891652
  have htrace : WordTrace (prefixWord ++ tailWord_1891652) baseStart_1891652 baseEnd_1891652 := by
    simpa [prefixWord, tailWord_1891652, baseEnd_1891652] using wordTrace_append hprefix tailTrace_1891652
  have hstable : (prefixWord ++ tailWord_1891652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891652).length < 2 ^ (prefixWord ++ tailWord_1891652).sum := by decide
  have hdescent : baseEnd_1891652 < baseStart_1891652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891655 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_1891655 : Nat := 118140960795 + 1891655 * 2 ^ 59
def prefixEnd_1891655 : Nat := 4983230072969 + 3 ^ 40 * 1891655 * 2
def baseEnd_1891655 : Nat := 971328247480901624812943

theorem tailTrace_1891655 : CollatzResearch.WordTrace tailWord_1891655 prefixEnd_1891655 971328247480901624812943 := by
  unfold tailWord_1891655
  simp only [CollatzResearch.WordTrace]
  refine ⟨68994325961864478798276419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45996217307909652532184279 68994325961864478798276419)
  ·
    refine ⟨103491488942796718197414629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68994325961864478798276419 103491488942796718197414629)
    ·
      refine ⟨19404654176774384662015243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103491488942796718197414629 19404654176774384662015243)
      ·
        refine ⟨29106981265161576993022865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19404654176774384662015243 29106981265161576993022865)
        ·
          refine ⟨21830235948871182744767149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29106981265161576993022865 21830235948871182744767149)
          ·
            refine ⟨8186338480826693529287681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21830235948871182744767149 8186338480826693529287681)
            ·
              refine ⟨6139753860620020146965761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8186338480826693529287681 6139753860620020146965761)
              ·
                refine ⟨4604815395465015110224321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6139753860620020146965761 4604815395465015110224321)
                ·
                  refine ⟨3453611546598761332668241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4604815395465015110224321 3453611546598761332668241)
                  ·
                    refine ⟨2590208659949070999501181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3453611546598761332668241 2590208659949070999501181)
                    ·
                      refine ⟨971328247480901624812943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2590208659949070999501181 971328247480901624812943)
                      ·
                        rfl

theorem cell23_1891655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_1891655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891655 prefixEnd_1891655 := by exact prefixLift 1891655
  have htrace : WordTrace (prefixWord ++ tailWord_1891655) baseStart_1891655 baseEnd_1891655 := by
    simpa [prefixWord, tailWord_1891655, baseEnd_1891655] using wordTrace_append hprefix tailTrace_1891655
  have hstable : (prefixWord ++ tailWord_1891655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891655).length < 2 ^ (prefixWord ++ tailWord_1891655).sum := by decide
  have hdescent : baseEnd_1891655 < baseStart_1891655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891662 : List Nat := [4, 1, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_1891662 : Nat := 118140960795 + 1891662 * 2 ^ 59
def prefixEnd_1891662 : Nat := 4983230072969 + 3 ^ 40 * 1891662 * 2
def baseEnd_1891662 : Nat := 323777280615161032475137

theorem tailTrace_1891662 : CollatzResearch.WordTrace tailWord_1891662 prefixEnd_1891662 323777280615161032475137 := by
  unfold tailWord_1891662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8624322659104889874222655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45996387515226079329187493 8624322659104889874222655)
  ·
    refine ⟨12936483988657334811333983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8624322659104889874222655 12936483988657334811333983)
    ·
      refine ⟨19404725982986002217000975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12936483988657334811333983 19404725982986002217000975)
      ·
        refine ⟨29107088974479003325501463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19404725982986002217000975 29107088974479003325501463)
        ·
          refine ⟨43660633461718504988252195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29107088974479003325501463 43660633461718504988252195)
          ·
            refine ⟨65490950192577757482378293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43660633461718504988252195 65490950192577757482378293)
            ·
              refine ⟨6139776580554164763972965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65490950192577757482378293 6139776580554164763972965)
              ·
                refine ⟨1151208108853905893244931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6139776580554164763972965 1151208108853905893244931)
                ·
                  refine ⟨1726812163280858839867397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151208108853905893244931 1726812163280858839867397)
                  ·
                    refine ⟨323777280615161032475137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1726812163280858839867397 323777280615161032475137)
                    ·
                      rfl

theorem cell23_1891662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_1891662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891662 prefixEnd_1891662 := by exact prefixLift 1891662
  have htrace : WordTrace (prefixWord ++ tailWord_1891662) baseStart_1891662 baseEnd_1891662 := by
    simpa [prefixWord, tailWord_1891662, baseEnd_1891662] using wordTrace_append hprefix tailTrace_1891662
  have hstable : (prefixWord ++ tailWord_1891662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891662).length < 2 ^ (prefixWord ++ tailWord_1891662).sum := by decide
  have hdescent : baseEnd_1891662 < baseStart_1891662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891695 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 1, 5, 2]
def baseStart_1891695 : Nat := 118140960795 + 1891695 * 2 ^ 59
def prefixEnd_1891695 : Nat := 4983230072969 + 3 ^ 40 * 1891695 * 2
def baseEnd_1891695 : Nat := 971348786707081468312759

theorem tailTrace_1891695 : CollatzResearch.WordTrace tailWord_1891695 prefixEnd_1891695 971348786707081468312759 := by
  unfold tailWord_1891695
  simp only [CollatzResearch.WordTrace]
  refine ⟨68995784881719565629732539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45997189921146377086488359 68995784881719565629732539)
  ·
    refine ⟨103493677322579348444598809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68995784881719565629732539 103493677322579348444598809)
    ·
      refine ⟨77620257991934511333449107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103493677322579348444598809 77620257991934511333449107)
      ·
        refine ⟨116430386987901767000173661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77620257991934511333449107 116430386987901767000173661)
        ·
          refine ⟨43661395120463162625065123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116430386987901767000173661 43661395120463162625065123)
          ·
            refine ⟨65492092680694743937597685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43661395120463162625065123 65492092680694743937597685)
            ·
              refine ⟨6139883688815132244149783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65492092680694743937597685 6139883688815132244149783)
              ·
                refine ⟨9209825533222698366224675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139883688815132244149783 9209825533222698366224675)
                ·
                  refine ⟨13814738299834047549337013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9209825533222698366224675 13814738299834047549337013)
                  ·
                    refine ⟨1295131715609441957750345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13814738299834047549337013 1295131715609441957750345)
                    ·
                      refine ⟨971348786707081468312759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295131715609441957750345 971348786707081468312759)
                      ·
                        rfl

theorem cell23_1891695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 5, 2].length) (baseStart_1891695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891695 prefixEnd_1891695 := by exact prefixLift 1891695
  have htrace : WordTrace (prefixWord ++ tailWord_1891695) baseStart_1891695 baseEnd_1891695 := by
    simpa [prefixWord, tailWord_1891695, baseEnd_1891695] using wordTrace_append hprefix tailTrace_1891695
  have hstable : (prefixWord ++ tailWord_1891695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891695).length < 2 ^ (prefixWord ++ tailWord_1891695).sum := by decide
  have hdescent : baseEnd_1891695 < baseStart_1891695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891719 : List Nat := [1, 1, 4, 2, 2, 2, 2, 4, 1, 1, 3]
def baseStart_1891719 : Nat := 118140960795 + 1891719 * 2 ^ 59
def prefixEnd_1891719 : Nat := 4983230072969 + 3 ^ 40 * 1891719 * 2
def baseEnd_1891719 : Nat := 971361110242789374412649

theorem tailTrace_1891719 : CollatzResearch.WordTrace tailWord_1891719 prefixEnd_1891719 971361110242789374412649 := by
  unfold tailWord_1891719
  simp only [CollatzResearch.WordTrace]
  refine ⟨68996660233632617728606211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45997773489088411819070807 68996660233632617728606211)
  ·
    refine ⟨103494990350448926592909317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68996660233632617728606211 103494990350448926592909317)
    ·
      refine ⟨19405310690709173736170497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103494990350448926592909317 19405310690709173736170497)
      ·
        refine ⟨14553983018031880302127873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19405310690709173736170497 14553983018031880302127873)
        ·
          refine ⟨10915487263523910226595905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14553983018031880302127873 10915487263523910226595905)
          ·
            refine ⟨8186615447642932669946929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10915487263523910226595905 8186615447642932669946929)
            ·
              refine ⟨6139961585732199502460197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8186615447642932669946929 6139961585732199502460197)
              ·
                refine ⟨1151242797324787406711287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6139961585732199502460197 1151242797324787406711287)
                ·
                  refine ⟨1726864195987181110066931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151242797324787406711287 1726864195987181110066931)
                  ·
                    refine ⟨2590296293980771665100397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1726864195987181110066931 2590296293980771665100397)
                    ·
                      refine ⟨971361110242789374412649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2590296293980771665100397 971361110242789374412649)
                      ·
                        rfl

theorem cell23_1891719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_1891719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891719 prefixEnd_1891719 := by exact prefixLift 1891719
  have htrace : WordTrace (prefixWord ++ tailWord_1891719) baseStart_1891719 baseEnd_1891719 := by
    simpa [prefixWord, tailWord_1891719, baseEnd_1891719] using wordTrace_append hprefix tailTrace_1891719
  have hstable : (prefixWord ++ tailWord_1891719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891719).length < 2 ^ (prefixWord ++ tailWord_1891719).sum := by decide
  have hdescent : baseEnd_1891719 < baseStart_1891719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891765 : List Nat := [1, 3, 3, 2, 2, 3, 9]
def baseStart_1891765 : Nat := 118140960795 + 1891765 * 2 ^ 59
def prefixEnd_1891765 : Nat := 4983230072969 + 3 ^ 40 * 1891765 * 2
def baseEnd_1891765 : Nat := 11992404078430817215277

theorem tailTrace_1891765 : CollatzResearch.WordTrace tailWord_1891765 prefixEnd_1891765 11992404078430817215277 := by
  unfold tailWord_1891765
  simp only [CollatzResearch.WordTrace]
  refine ⟨68998337991465967584780749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45998891994310645056520499 68998337991465967584780749)
  ·
    refine ⟨25874376746799737844292781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68998337991465967584780749 25874376746799737844292781)
    ·
      refine ⟨9702891280049901691609793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25874376746799737844292781 9702891280049901691609793)
      ·
        refine ⟨7277168460037426268707345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9702891280049901691609793 7277168460037426268707345)
        ·
          refine ⟨5457876345028069701530509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7277168460037426268707345 5457876345028069701530509)
          ·
            refine ⟨2046703629385526138073941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5457876345028069701530509 2046703629385526138073941)
            ·
              refine ⟨11992404078430817215277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2046703629385526138073941 11992404078430817215277)
              ·
                rfl

theorem cell23_1891765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 9].length) (baseStart_1891765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891765 prefixEnd_1891765 := by exact prefixLift 1891765
  have htrace : WordTrace (prefixWord ++ tailWord_1891765) baseStart_1891765 baseEnd_1891765 := by
    simpa [prefixWord, tailWord_1891765, baseEnd_1891765] using wordTrace_append hprefix tailTrace_1891765
  have hstable : (prefixWord ++ tailWord_1891765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891765).length < 2 ^ (prefixWord ++ tailWord_1891765).sum := by decide
  have hdescent : baseEnd_1891765 < baseStart_1891765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891785 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 2, 7, 2]
def baseStart_1891785 : Nat := 118140960795 + 1891785 * 2 ^ 59
def prefixEnd_1891785 : Nat := 4983230072969 + 3 ^ 40 * 1891785 * 2
def baseEnd_1891785 : Nat := 971394999965986116187345

theorem tailTrace_1891785 : CollatzResearch.WordTrace tailWord_1891785 prefixEnd_1891785 971394999965986116187345 := by
  unfold tailWord_1891785
  simp only [CollatzResearch.WordTrace]
  refine ⟨68999067451393511000508809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45999378300929007333672539 68999067451393511000508809)
  ·
    refine ⟨51749300588545133250381607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68999067451393511000508809 51749300588545133250381607)
    ·
      refine ⟨77623950882817699875572411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51749300588545133250381607 77623950882817699875572411)
      ·
        refine ⟨116435926324226549813358617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77623950882817699875572411 116435926324226549813358617)
        ·
          refine ⟨87326944743169912360018963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116435926324226549813358617 87326944743169912360018963)
          ·
            refine ⟨130990417114754868540028445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87326944743169912360018963 130990417114754868540028445)
            ·
              refine ⟨49121406418033075702510667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130990417114754868540028445 49121406418033075702510667)
              ·
                refine ⟨73682109627049613553766001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49121406418033075702510667 73682109627049613553766001)
                ·
                  refine ⟨55261582220287210165324501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73682109627049613553766001 55261582220287210165324501)
                  ·
                    refine ⟨1295193333287981488249793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55261582220287210165324501 1295193333287981488249793)
                    ·
                      refine ⟨971394999965986116187345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295193333287981488249793 971394999965986116187345)
                      ·
                        rfl

theorem cell23_1891785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 7, 2].length) (baseStart_1891785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891785 prefixEnd_1891785 := by exact prefixLift 1891785
  have htrace : WordTrace (prefixWord ++ tailWord_1891785) baseStart_1891785 baseEnd_1891785 := by
    simpa [prefixWord, tailWord_1891785, baseEnd_1891785] using wordTrace_append hprefix tailTrace_1891785
  have hstable : (prefixWord ++ tailWord_1891785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891785).length < 2 ^ (prefixWord ++ tailWord_1891785).sum := by decide
  have hdescent : baseEnd_1891785 < baseStart_1891785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891792 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 2, 1, 3]
def baseStart_1891792 : Nat := 118140960795 + 1891792 * 2 ^ 59
def prefixEnd_1891792 : Nat := 4983230072969 + 3 ^ 40 * 1891792 * 2
def baseEnd_1891792 : Nat := 971398594330567588799813

theorem tailTrace_1891792 : CollatzResearch.WordTrace tailWord_1891792 prefixEnd_1891792 971398594330567588799813 := by
  unfold tailWord_1891792
  simp only [CollatzResearch.WordTrace]
  refine ⟨34499661381184075598006815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45999548508245434130675753 34499661381184075598006815)
  ·
    refine ⟨51749492071776113397010223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34499661381184075598006815 51749492071776113397010223)
    ·
      refine ⟨77624238107664170095515335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51749492071776113397010223 77624238107664170095515335)
      ·
        refine ⟨116436357161496255143273003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77624238107664170095515335 116436357161496255143273003)
        ·
          refine ⟨174654535742244382714909505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116436357161496255143273003 174654535742244382714909505)
          ·
            refine ⟨130990901806683287036182129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174654535742244382714909505 130990901806683287036182129)
            ·
              refine ⟨98243176355012465277136597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130990901806683287036182129 98243176355012465277136597)
              ·
                refine ⟨2302574445820604654932889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98243176355012465277136597 2302574445820604654932889)
                ·
                  refine ⟨1726930834365453491199667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2302574445820604654932889 1726930834365453491199667)
                  ·
                    refine ⟨2590396251548180236799501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1726930834365453491199667 2590396251548180236799501)
                    ·
                      refine ⟨971398594330567588799813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2590396251548180236799501 971398594330567588799813)
                      ·
                        rfl

theorem cell23_1891792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2, 1, 3].length) (baseStart_1891792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891792 prefixEnd_1891792 := by exact prefixLift 1891792
  have htrace : WordTrace (prefixWord ++ tailWord_1891792) baseStart_1891792 baseEnd_1891792 := by
    simpa [prefixWord, tailWord_1891792, baseEnd_1891792] using wordTrace_append hprefix tailTrace_1891792
  have hstable : (prefixWord ++ tailWord_1891792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891792).length < 2 ^ (prefixWord ++ tailWord_1891792).sum := by decide
  have hdescent : baseEnd_1891792 < baseStart_1891792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
