import V185TrunkScan23Chunk0966

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5724474 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 8]
def baseStart_5724474 : Nat := 118140960795 + 5724474 * 2 ^ 59
def prefixEnd_5724474 : Nat := 4983230072969 + 3 ^ 40 * 5724474 * 2
def baseEnd_5724474 : Nat := 326600739573993466983181

theorem tailTrace_5724474 : CollatzResearch.WordTrace tailWord_5724474 prefixEnd_5724474 326600739573993466983181 := by
  unfold tailWord_5724474
  simp only [CollatzResearch.WordTrace]
  refine ⟨52197179865803958792159119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139192479642143890112424317 52197179865803958792159119)
  ·
    refine ⟨78295769798705938188238679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52197179865803958792159119 78295769798705938188238679)
    ·
      refine ⟨117443654698058907282358019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78295769798705938188238679 117443654698058907282358019)
      ·
        refine ⟨176165482047088360923537029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117443654698058907282358019 176165482047088360923537029)
        ·
          refine ⟨33031027883829067673163193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176165482047088360923537029 33031027883829067673163193)
          ·
            refine ⟨24773270912871800754872395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33031027883829067673163193 24773270912871800754872395)
            ·
              refine ⟨37159906369307701132308593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24773270912871800754872395 37159906369307701132308593)
              ·
                refine ⟨27869929776980775849231445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37159906369307701132308593 27869929776980775849231445)
                ·
                  refine ⟨326600739573993466983181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27869929776980775849231445 326600739573993466983181)
                  ·
                    rfl

theorem cell23_5724474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_5724474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724474 prefixEnd_5724474 := by exact prefixLift 5724474
  have htrace : WordTrace (prefixWord ++ tailWord_5724474) baseStart_5724474 baseEnd_5724474 := by
    simpa [prefixWord, tailWord_5724474, baseEnd_5724474] using wordTrace_append hprefix tailTrace_5724474
  have hstable : (prefixWord ++ tailWord_5724474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724474).length < 2 ^ (prefixWord ++ tailWord_5724474).sum := by decide
  have hdescent : baseEnd_5724474 < baseStart_5724474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724494 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_5724494 : Nat := 118140960795 + 5724494 * 2 ^ 59
def prefixEnd_5724494 : Nat := 4983230072969 + 3 ^ 40 * 5724494 * 2
def baseEnd_5724494 : Nat := 2939416925779031124598537

theorem tailTrace_5724494 : CollatzResearch.WordTrace tailWord_5724494 prefixEnd_5724494 2939416925779031124598537 := by
  unfold tailWord_5724494
  simp only [CollatzResearch.WordTrace]
  refine ⟨26098681115392922323045567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139192965948762252389576357 26098681115392922323045567)
  ·
    refine ⟨39148021673089383484568351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26098681115392922323045567 39148021673089383484568351)
    ·
      refine ⟨58722032509634075226852527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39148021673089383484568351 58722032509634075226852527)
      ·
        refine ⟨88083048764451112840278791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58722032509634075226852527 88083048764451112840278791)
        ·
          refine ⟨132124573146676669260418187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88083048764451112840278791 132124573146676669260418187)
          ·
            refine ⟨198186859720015003890627281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132124573146676669260418187 198186859720015003890627281)
            ·
              refine ⟨148640144790011252917970461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198186859720015003890627281 148640144790011252917970461)
              ·
                refine ⟨55740054296254219844238923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148640144790011252917970461 55740054296254219844238923)
                ·
                  refine ⟨83610081444381329766358385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55740054296254219844238923 83610081444381329766358385)
                  ·
                    refine ⟨62707561083285997324768789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83610081444381329766358385 62707561083285997324768789)
                    ·
                      refine ⟨2939416925779031124598537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62707561083285997324768789 2939416925779031124598537)
                      ·
                        rfl

theorem cell23_5724494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_5724494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724494 prefixEnd_5724494 := by exact prefixLift 5724494
  have htrace : WordTrace (prefixWord ++ tailWord_5724494) baseStart_5724494 baseEnd_5724494 := by
    simpa [prefixWord, tailWord_5724494, baseEnd_5724494] using wordTrace_append hprefix tailTrace_5724494
  have hstable : (prefixWord ++ tailWord_5724494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724494).length < 2 ^ (prefixWord ++ tailWord_5724494).sum := by decide
  have hdescent : baseEnd_5724494 < baseStart_5724494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724511 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 3, 5, 2]
def baseStart_5724511 : Nat := 118140960795 + 5724511 * 2 ^ 59
def prefixEnd_5724511 : Nat := 4983230072969 + 3 ^ 40 * 5724511 * 2
def baseEnd_5724511 : Nat := 2939425654950157558085959

theorem tailTrace_5724511 : CollatzResearch.WordTrace tailWord_5724511 prefixEnd_5724511 2939425654950157558085959 := by
  unfold tailWord_5724511
  simp only [CollatzResearch.WordTrace]
  refine ⟨208790068964081790487733387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139193379309387860325155591 208790068964081790487733387)
  ·
    refine ⟨313185103446122685731600081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208790068964081790487733387 313185103446122685731600081)
    ·
      refine ⟨234888827584592014298700061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313185103446122685731600081 234888827584592014298700061)
      ·
        refine ⟨88083310344222005362012523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234888827584592014298700061 88083310344222005362012523)
        ·
          refine ⟨132124965516333008043018785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88083310344222005362012523 132124965516333008043018785)
          ·
            refine ⟨99093724137249756032264089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132124965516333008043018785 99093724137249756032264089)
            ·
              refine ⟨74320293102937317024198067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99093724137249756032264089 74320293102937317024198067)
              ·
                refine ⟨111480439654405975536297101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74320293102937317024198067 111480439654405975536297101)
                ·
                  refine ⟨41805164870402240826111413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111480439654405975536297101 41805164870402240826111413)
                  ·
                    refine ⟨3919234206600210077447945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41805164870402240826111413 3919234206600210077447945)
                    ·
                      refine ⟨2939425654950157558085959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919234206600210077447945 2939425654950157558085959)
                      ·
                        rfl

theorem cell23_5724511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_5724511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724511 prefixEnd_5724511 := by exact prefixLift 5724511
  have htrace : WordTrace (prefixWord ++ tailWord_5724511) baseStart_5724511 baseEnd_5724511 := by
    simpa [prefixWord, tailWord_5724511, baseEnd_5724511] using wordTrace_append hprefix tailTrace_5724511
  have hstable : (prefixWord ++ tailWord_5724511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724511).length < 2 ^ (prefixWord ++ tailWord_5724511).sum := by decide
  have hdescent : baseEnd_5724511 < baseStart_5724511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724528 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 2, 3, 2]
def baseStart_5724528 : Nat := 118140960795 + 5724528 * 2 ^ 59
def prefixEnd_5724528 : Nat := 4983230072969 + 3 ^ 40 * 5724528 * 2
def baseEnd_5724528 : Nat := 2939434384121283991573381

theorem tailTrace_5724528 : CollatzResearch.WordTrace tailWord_5724528 prefixEnd_5724528 2939434384121283991573381 := by
  unfold tailWord_5724528
  simp only [CollatzResearch.WordTrace]
  refine ⟨104395344502510101195551119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139193792670013468260734825 104395344502510101195551119)
  ·
    refine ⟨156593016753765151793326679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104395344502510101195551119 156593016753765151793326679)
    ·
      refine ⟨234889525130647727689990019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156593016753765151793326679 234889525130647727689990019)
      ·
        refine ⟨352334287695971591534985029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234889525130647727689990019 352334287695971591534985029)
        ·
          refine ⟨66062678942994673412809693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 352334287695971591534985029 66062678942994673412809693)
          ·
            refine ⟨24773504603623002529803635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66062678942994673412809693 24773504603623002529803635)
            ·
              refine ⟨37160256905434503794705453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24773504603623002529803635 37160256905434503794705453)
              ·
                refine ⟨13935096339537938923014545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37160256905434503794705453 13935096339537938923014545)
                ·
                  refine ⟨10451322254653454192260909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13935096339537938923014545 10451322254653454192260909)
                  ·
                    refine ⟨3919245845495045322097841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10451322254653454192260909 3919245845495045322097841)
                    ·
                      refine ⟨2939434384121283991573381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919245845495045322097841 2939434384121283991573381)
                      ·
                        rfl

theorem cell23_5724528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2, 3, 2].length) (baseStart_5724528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724528 prefixEnd_5724528 := by exact prefixLift 5724528
  have htrace : WordTrace (prefixWord ++ tailWord_5724528) baseStart_5724528 baseEnd_5724528 := by
    simpa [prefixWord, tailWord_5724528, baseEnd_5724528] using wordTrace_append hprefix tailTrace_5724528
  have hstable : (prefixWord ++ tailWord_5724528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724528).length < 2 ^ (prefixWord ++ tailWord_5724528).sum := by decide
  have hdescent : baseEnd_5724528 < baseStart_5724528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724545 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_5724545 : Nat := 118140960795 + 5724545 * 2 ^ 59
def prefixEnd_5724545 : Nat := 4983230072969 + 3 ^ 40 * 5724545 * 2
def baseEnd_5724545 : Nat := 2939443113292410425060803

theorem tailTrace_5724545 : CollatzResearch.WordTrace tailWord_5724545 prefixEnd_5724545 2939443113292410425060803 := by
  unfold tailWord_5724545
  simp only [CollatzResearch.WordTrace]
  refine ⟨208791309045958614294471089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139194206030639076196314059 208791309045958614294471089)
  ·
    refine ⟨156593481784468960720853317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208791309045958614294471089 156593481784468960720853317)
    ·
      refine ⟨29361277834587930135159997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156593481784468960720853317 29361277834587930135159997)
      ·
        refine ⟨11010479187970473800684999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29361277834587930135159997 11010479187970473800684999)
        ·
          refine ⟨16515718781955710701027499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11010479187970473800684999 16515718781955710701027499)
          ·
            refine ⟨24773578172933566051541249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16515718781955710701027499 24773578172933566051541249)
            ·
              refine ⟨18580183629700174538655937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24773578172933566051541249 18580183629700174538655937)
              ·
                refine ⟨13935137722275130903991953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18580183629700174538655937 13935137722275130903991953)
                ·
                  refine ⟨10451353291706348177993965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13935137722275130903991953 10451353291706348177993965)
                  ·
                    refine ⟨3919257484389880566747737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10451353291706348177993965 3919257484389880566747737)
                    ·
                      refine ⟨2939443113292410425060803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919257484389880566747737 2939443113292410425060803)
                      ·
                        rfl

theorem cell23_5724545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_5724545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724545 prefixEnd_5724545 := by exact prefixLift 5724545
  have htrace : WordTrace (prefixWord ++ tailWord_5724545) baseStart_5724545 baseEnd_5724545 := by
    simpa [prefixWord, tailWord_5724545, baseEnd_5724545] using wordTrace_append hprefix tailTrace_5724545
  have hstable : (prefixWord ++ tailWord_5724545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724545).length < 2 ^ (prefixWord ++ tailWord_5724545).sum := by decide
  have hdescent : baseEnd_5724545 < baseStart_5724545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724546 : List Nat := [3, 4, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_5724546 : Nat := 118140960795 + 5724546 * 2 ^ 59
def prefixEnd_5724546 : Nat := 4983230072969 + 3 ^ 40 * 5724546 * 2
def baseEnd_5724546 : Nat := 979814542257688307049433

theorem tailTrace_5724546 : CollatzResearch.WordTrace tailWord_5724546 prefixEnd_5724546 979814542257688307049433 := by
  unfold tailWord_5724546
  simp only [CollatzResearch.WordTrace]
  refine ⟨52197836379738747866314373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139194230345969994310171661 52197836379738747866314373)
  ·
    refine ⟨9787094321201015224933945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52197836379738747866314373 9787094321201015224933945)
    ·
      refine ⟨7340320740900761418700459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9787094321201015224933945 7340320740900761418700459)
      ·
        refine ⟨11010481111351142128050689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7340320740900761418700459 11010481111351142128050689)
        ·
          refine ⟨8257860833513356596038017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11010481111351142128050689 8257860833513356596038017)
          ·
            refine ⟨6193395625135017447028513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8257860833513356596038017 6193395625135017447028513)
            ·
              refine ⟨4645046718851263085271385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6193395625135017447028513 4645046718851263085271385)
              ·
                refine ⟨3483785039138447313953539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4645046718851263085271385 3483785039138447313953539)
                ·
                  refine ⟨5225677558707670970930309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3483785039138447313953539 5225677558707670970930309)
                  ·
                    refine ⟨979814542257688307049433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5225677558707670970930309 979814542257688307049433)
                    ·
                      rfl

theorem cell23_5724546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_5724546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724546 prefixEnd_5724546 := by exact prefixLift 5724546
  have htrace : WordTrace (prefixWord ++ tailWord_5724546) baseStart_5724546 baseEnd_5724546 := by
    simpa [prefixWord, tailWord_5724546, baseEnd_5724546] using wordTrace_append hprefix tailTrace_5724546
  have hstable : (prefixWord ++ tailWord_5724546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724546).length < 2 ^ (prefixWord ++ tailWord_5724546).sum := by decide
  have hdescent : baseEnd_5724546 < baseStart_5724546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724558 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5724558 : Nat := 118140960795 + 5724558 * 2 ^ 59
def prefixEnd_5724558 : Nat := 4983230072969 + 3 ^ 40 * 5724558 * 2
def baseEnd_5724558 : Nat := 2939449788540918874198243

theorem tailTrace_5724558 : CollatzResearch.WordTrace tailWord_5724558 prefixEnd_5724558 2939449788540918874198243 := by
  unfold tailWord_5724558
  simp only [CollatzResearch.WordTrace]
  refine ⟨26098972899363939689336791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139194522129941011676462885 26098972899363939689336791)
  ·
    refine ⟨39148459349045909534005187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26098972899363939689336791 39148459349045909534005187)
    ·
      refine ⟨58722689023568864301007781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39148459349045909534005187 58722689023568864301007781)
      ·
        refine ⟨11010504191919162056438959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58722689023568864301007781 11010504191919162056438959)
        ·
          refine ⟨16515756287878743084658439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11010504191919162056438959 16515756287878743084658439)
          ·
            refine ⟨24773634431818114626987659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16515756287878743084658439 24773634431818114626987659)
            ·
              refine ⟨37160451647727171940481489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24773634431818114626987659 37160451647727171940481489)
              ·
                refine ⟨27870338735795378955361117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37160451647727171940481489 27870338735795378955361117)
                ·
                  refine ⟨10451377025923267108260419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27870338735795378955361117 10451377025923267108260419)
                  ·
                    refine ⟨15677065538884900662390629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10451377025923267108260419 15677065538884900662390629)
                    ·
                      refine ⟨2939449788540918874198243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15677065538884900662390629 2939449788540918874198243)
                      ·
                        rfl

theorem cell23_5724558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5724558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724558 prefixEnd_5724558 := by exact prefixLift 5724558
  have htrace : WordTrace (prefixWord ++ tailWord_5724558) baseStart_5724558 baseEnd_5724558 := by
    simpa [prefixWord, tailWord_5724558, baseEnd_5724558] using wordTrace_append hprefix tailTrace_5724558
  have hstable : (prefixWord ++ tailWord_5724558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724558).length < 2 ^ (prefixWord ++ tailWord_5724558).sum := by decide
  have hdescent : baseEnd_5724558 < baseStart_5724558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724568 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 1, 6]
def baseStart_5724568 : Nat := 118140960795 + 5724568 * 2 ^ 59
def prefixEnd_5724568 : Nat := 4983230072969 + 3 ^ 40 * 5724568 * 2
def baseEnd_5724568 : Nat := 979818307782487945024399

theorem tailTrace_5724568 : CollatzResearch.WordTrace tailWord_5724568 prefixEnd_5724568 979818307782487945024399 := by
  unfold tailWord_5724568
  simp only [CollatzResearch.WordTrace]
  refine ⟨104396073962437644611279179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139194765283250192815038905 104396073962437644611279179)
  ·
    refine ⟨156594110943656466916918769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104396073962437644611279179 156594110943656466916918769)
    ·
      refine ⟨117445583207742350187689077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156594110943656466916918769 117445583207742350187689077)
      ·
        refine ⟨11010523425725845330095851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117445583207742350187689077 11010523425725845330095851)
        ·
          refine ⟨16515785138588767995143777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11010523425725845330095851 16515785138588767995143777)
          ·
            refine ⟨12386838853941575996357833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16515785138588767995143777 12386838853941575996357833)
            ·
              refine ⟨9290129140456181997268375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12386838853941575996357833 9290129140456181997268375)
              ·
                refine ⟨13935193710684272995902563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9290129140456181997268375 13935193710684272995902563)
                ·
                  refine ⟨20902790566026409493853845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13935193710684272995902563 20902790566026409493853845)
                  ·
                    refine ⟨979818307782487945024399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20902790566026409493853845 979818307782487945024399)
                    ·
                      rfl

theorem cell23_5724568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_5724568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724568 prefixEnd_5724568 := by exact prefixLift 5724568
  have htrace : WordTrace (prefixWord ++ tailWord_5724568) baseStart_5724568 baseEnd_5724568 := by
    simpa [prefixWord, tailWord_5724568, baseEnd_5724568] using wordTrace_append hprefix tailTrace_5724568
  have hstable : (prefixWord ++ tailWord_5724568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724568).length < 2 ^ (prefixWord ++ tailWord_5724568).sum := by decide
  have hdescent : baseEnd_5724568 < baseStart_5724568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724575 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 3, 2, 2]
def baseStart_5724575 : Nat := 118140960795 + 5724575 * 2 ^ 59
def prefixEnd_5724575 : Nat := 4983230072969 + 3 ^ 40 * 5724575 * 2
def baseEnd_5724575 : Nat := 2939458517712045307685665

theorem tailTrace_5724575 : CollatzResearch.WordTrace tailWord_5724575 prefixEnd_5724575 2939458517712045307685665 := by
  unfold tailWord_5724575
  simp only [CollatzResearch.WordTrace]
  refine ⟨208792403235849929418063179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139194935490566619612042119 208792403235849929418063179)
  ·
    refine ⟨313188604853774894127094769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208792403235849929418063179 313188604853774894127094769)
    ·
      refine ⟨234891453640331170595321077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313188604853774894127094769 234891453640331170595321077)
      ·
        refine ⟨22021073778781047243311351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234891453640331170595321077 22021073778781047243311351)
        ·
          refine ⟨33031610668171570864967027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22021073778781047243311351 33031610668171570864967027)
          ·
            refine ⟨49547416002257356297450541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33031610668171570864967027 49547416002257356297450541)
            ·
              refine ⟨18580281000846508611543953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49547416002257356297450541 18580281000846508611543953)
              ·
                refine ⟨13935210750634881458657965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18580281000846508611543953 13935210750634881458657965)
                ·
                  refine ⟨5225704031488080546996737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13935210750634881458657965 5225704031488080546996737)
                  ·
                    refine ⟨3919278023616060410247553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5225704031488080546996737 3919278023616060410247553)
                    ·
                      refine ⟨2939458517712045307685665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919278023616060410247553 2939458517712045307685665)
                      ·
                        rfl

theorem cell23_5724575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_5724575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724575 prefixEnd_5724575 := by exact prefixLift 5724575
  have htrace : WordTrace (prefixWord ++ tailWord_5724575) baseStart_5724575 baseEnd_5724575 := by
    simpa [prefixWord, tailWord_5724575, baseEnd_5724575] using wordTrace_append hprefix tailTrace_5724575
  have hstable : (prefixWord ++ tailWord_5724575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724575).length < 2 ^ (prefixWord ++ tailWord_5724575).sum := by decide
  have hdescent : baseEnd_5724575 < baseStart_5724575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724578 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_5724578 : Nat := 118140960795 + 5724578 * 2 ^ 59
def prefixEnd_5724578 : Nat := 4983230072969 + 3 ^ 40 * 5724578 * 2
def baseEnd_5724578 : Nat := 2939460058154008795948151

theorem tailTrace_5724578 : CollatzResearch.WordTrace tailWord_5724578 prefixEnd_5724578 2939460058154008795948151 := by
  unfold tailWord_5724578
  simp only [CollatzResearch.WordTrace]
  refine ⟨52198128163709765232605597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139195008436559373953614925 52198128163709765232605597)
  ·
    refine ⟨19574298061391161962227099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52198128163709765232605597 19574298061391161962227099)
    ·
      refine ⟨29361447092086742943340649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19574298061391161962227099 29361447092086742943340649)
      ·
        refine ⟨22021085319065057207505487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29361447092086742943340649 22021085319065057207505487)
        ·
          refine ⟨33031627978597585811258231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22021085319065057207505487 33031627978597585811258231)
          ·
            refine ⟨49547441967896378716887347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33031627978597585811258231 49547441967896378716887347)
            ·
              refine ⟨74321162951844568075331021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49547441967896378716887347 74321162951844568075331021)
              ·
                refine ⟨27870436106941713028249133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74321162951844568075331021 27870436106941713028249133)
                ·
                  refine ⟨10451413540103142385593425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27870436106941713028249133 10451413540103142385593425)
                  ·
                    refine ⟨7838560155077356789195069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10451413540103142385593425 7838560155077356789195069)
                    ·
                      refine ⟨2939460058154008795948151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7838560155077356789195069 2939460058154008795948151)
                      ·
                        rfl

theorem cell23_5724578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_5724578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724578 prefixEnd_5724578 := by exact prefixLift 5724578
  have htrace : WordTrace (prefixWord ++ tailWord_5724578) baseStart_5724578 baseEnd_5724578 := by
    simpa [prefixWord, tailWord_5724578, baseEnd_5724578] using wordTrace_append hprefix tailTrace_5724578
  have hstable : (prefixWord ++ tailWord_5724578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724578).length < 2 ^ (prefixWord ++ tailWord_5724578).sum := by decide
  have hdescent : baseEnd_5724578 < baseStart_5724578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724581 : List Nat := [1, 3, 1, 2, 1, 1, 7, 7]
def baseStart_5724581 : Nat := 118140960795 + 5724581 * 2 ^ 59
def prefixEnd_5724581 : Nat := 4983230072969 + 3 ^ 40 * 5724581 * 2
def baseEnd_5724581 : Nat := 108868948096147121637431

theorem tailTrace_5724581 : CollatzResearch.WordTrace tailWord_5724581 prefixEnd_5724581 108868948096147121637431 := by
  unfold tailWord_5724581
  simp only [CollatzResearch.WordTrace]
  refine ⟨208792622073828192442781597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139195081382552128295187731 208792622073828192442781597)
  ·
    refine ⟨78297233277685572166043099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208792622073828192442781597 78297233277685572166043099)
    ·
      refine ⟨117445849916528358249064649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78297233277685572166043099 117445849916528358249064649)
      ·
        refine ⟨88084387437396268686798487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117445849916528358249064649 88084387437396268686798487)
        ·
          refine ⟨132126581156094403030197731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88084387437396268686798487 132126581156094403030197731)
          ·
            refine ⟨198189871734141604545296597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132126581156094403030197731 198189871734141604545296597)
            ·
              refine ⟨4645075118768943856530389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 198189871734141604545296597 4645075118768943856530389)
              ·
                refine ⟨108868948096147121637431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4645075118768943856530389 108868948096147121637431)
                ·
                  rfl

theorem cell23_5724581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 7].length) (baseStart_5724581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724581 prefixEnd_5724581 := by exact prefixLift 5724581
  have htrace : WordTrace (prefixWord ++ tailWord_5724581) baseStart_5724581 baseEnd_5724581 := by
    simpa [prefixWord, tailWord_5724581, baseEnd_5724581] using wordTrace_append hprefix tailTrace_5724581
  have hstable : (prefixWord ++ tailWord_5724581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724581).length < 2 ^ (prefixWord ++ tailWord_5724581).sum := by decide
  have hdescent : baseEnd_5724581 < baseStart_5724581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724589 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_5724589 : Nat := 118140960795 + 5724589 * 2 ^ 59
def prefixEnd_5724589 : Nat := 4983230072969 + 3 ^ 40 * 5724589 * 2
def baseEnd_5724589 : Nat := 979821902147069417636867

theorem tailTrace_5724589 : CollatzResearch.WordTrace tailWord_5724589 prefixEnd_5724589 979821902147069417636867 := by
  unfold tailWord_5724589
  simp only [CollatzResearch.WordTrace]
  refine ⟨208792913857799209809072821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139195275905199473206048547 208792913857799209809072821)
  ·
    refine ⟨19574335674168675919600577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208792913857799209809072821 19574335674168675919600577)
    ·
      refine ⟨14680751755626506939700433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19574335674168675919600577 14680751755626506939700433)
      ·
        refine ⟨11010563816719880204775325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14680751755626506939700433 11010563816719880204775325)
        ·
          refine ⟨4128961431269955076790747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11010563816719880204775325 4128961431269955076790747)
          ·
            refine ⟨6193442146904932615186121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4128961431269955076790747 6193442146904932615186121)
            ·
              refine ⟨4645081610178699461389591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6193442146904932615186121 4645081610178699461389591)
              ·
                refine ⟨6967622415268049192084387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4645081610178699461389591 6967622415268049192084387)
                ·
                  refine ⟨10451433622902073788126581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6967622415268049192084387 10451433622902073788126581)
                  ·
                    refine ⟨979821902147069417636867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10451433622902073788126581 979821902147069417636867)
                    ·
                      rfl

theorem cell23_5724589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_5724589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724589 prefixEnd_5724589 := by exact prefixLift 5724589
  have htrace : WordTrace (prefixWord ++ tailWord_5724589) baseStart_5724589 baseEnd_5724589 := by
    simpa [prefixWord, tailWord_5724589, baseEnd_5724589] using wordTrace_append hprefix tailTrace_5724589
  have hstable : (prefixWord ++ tailWord_5724589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724589).length < 2 ^ (prefixWord ++ tailWord_5724589).sum := by decide
  have hdescent : baseEnd_5724589 < baseStart_5724589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724651 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 5]
def baseStart_5724651 : Nat := 118140960795 + 5724651 * 2 ^ 59
def prefixEnd_5724651 : Nat := 4983230072969 + 3 ^ 40 * 5724651 * 2
def baseEnd_5724651 : Nat := 2939497542241787010335315

theorem tailTrace_5724651 : CollatzResearch.WordTrace tailWord_5724651 prefixEnd_5724651 2939497542241787010335315 := by
  unfold tailWord_5724651
  simp only [CollatzResearch.WordTrace]
  refine ⟨208795175183574594397829807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139196783455716396265219871 208795175183574594397829807)
  ·
    refine ⟨313192762775361891596744711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208795175183574594397829807 313192762775361891596744711)
    ·
      refine ⟨469789144163042837395117067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313192762775361891596744711 469789144163042837395117067)
      ·
        refine ⟨704683716244564256092675601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469789144163042837395117067 704683716244564256092675601)
        ·
          refine ⟨528512787183423192069506701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704683716244564256092675601 528512787183423192069506701)
          ·
            refine ⟨198192295193783697026065013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 528512787183423192069506701 198192295193783697026065013)
            ·
              refine ⟨18580527674417221596193595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 198192295193783697026065013 18580527674417221596193595)
              ·
                refine ⟨27870791511625832394290393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18580527674417221596193595 27870791511625832394290393)
                ·
                  refine ⟨20903093633719374295717795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27870791511625832394290393 20903093633719374295717795)
                  ·
                    refine ⟨31354640450579061443576693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20903093633719374295717795 31354640450579061443576693)
                    ·
                      refine ⟨2939497542241787010335315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31354640450579061443576693 2939497542241787010335315)
                      ·
                        rfl

theorem cell23_5724651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 5].length) (baseStart_5724651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724651 prefixEnd_5724651 := by exact prefixLift 5724651
  have htrace : WordTrace (prefixWord ++ tailWord_5724651) baseStart_5724651 baseEnd_5724651 := by
    simpa [prefixWord, tailWord_5724651, baseEnd_5724651] using wordTrace_append hprefix tailTrace_5724651
  have hstable : (prefixWord ++ tailWord_5724651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724651).length < 2 ^ (prefixWord ++ tailWord_5724651).sum := by decide
  have hdescent : baseEnd_5724651 < baseStart_5724651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724665 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 4, 2, 2]
def baseStart_5724665 : Nat := 118140960795 + 5724665 * 2 ^ 59
def prefixEnd_5724665 : Nat := 4983230072969 + 3 ^ 40 * 5724665 * 2
def baseEnd_5724665 : Nat := 2939504730970949955560251

theorem tailTrace_5724665 : CollatzResearch.WordTrace tailWord_5724665 prefixEnd_5724665 2939504730970949955560251 := by
  unfold tailWord_5724665
  simp only [CollatzResearch.WordTrace]
  refine ⟨208795685805523874788839449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139197123870349249859226299 208795685805523874788839449)
  ·
    refine ⟨156596764354142906091629587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208795685805523874788839449 156596764354142906091629587)
    ·
      refine ⟨234895146531214359137444381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156596764354142906091629587 234895146531214359137444381)
      ·
        refine ⟨88085679949205384676541643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234895146531214359137444381 88085679949205384676541643)
        ·
          refine ⟨132128519923808077014812465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88085679949205384676541643 132128519923808077014812465)
          ·
            refine ⟨99096389942856057761109349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132128519923808077014812465 99096389942856057761109349)
            ·
              refine ⟨18580573114285510830208003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99096389942856057761109349 18580573114285510830208003)
              ·
                refine ⟨27870859671428266245312005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18580573114285510830208003 27870859671428266245312005)
                ·
                  refine ⟨5225786188392799920996001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27870859671428266245312005 5225786188392799920996001)
                  ·
                    refine ⟨3919339641294599940747001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5225786188392799920996001 3919339641294599940747001)
                    ·
                      refine ⟨2939504730970949955560251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919339641294599940747001 2939504730970949955560251)
                      ·
                        rfl

theorem cell23_5724665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_5724665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724665 prefixEnd_5724665 := by exact prefixLift 5724665
  have htrace : WordTrace (prefixWord ++ tailWord_5724665) baseStart_5724665 baseEnd_5724665 := by
    simpa [prefixWord, tailWord_5724665, baseEnd_5724665] using wordTrace_append hprefix tailTrace_5724665
  have hstable : (prefixWord ++ tailWord_5724665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724665).length < 2 ^ (prefixWord ++ tailWord_5724665).sum := by decide
  have hdescent : baseEnd_5724665 < baseStart_5724665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724682 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2]
def baseStart_5724682 : Nat := 118140960795 + 5724682 * 2 ^ 59
def prefixEnd_5724682 : Nat := 4983230072969 + 3 ^ 40 * 5724682 * 2
def baseEnd_5724682 : Nat := 2939513460142076389047673

theorem tailTrace_5724682 : CollatzResearch.WordTrace tailWord_5724682 prefixEnd_5724682 2939513460142076389047673 := by
  unfold tailWord_5724682
  simp only [CollatzResearch.WordTrace]
  refine ⟨52199076461615571673052075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139197537230974857794805533 52199076461615571673052075)
  ·
    refine ⟨78298614692423357509578113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52199076461615571673052075 78298614692423357509578113)
    ·
      refine ⟨58723961019317518132183585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78298614692423357509578113 58723961019317518132183585)
      ·
        refine ⟨44042970764488138599137689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58723961019317518132183585 44042970764488138599137689)
        ·
          refine ⟨33032228073366103949353267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44042970764488138599137689 33032228073366103949353267)
          ·
            refine ⟨49548342110049155924029901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33032228073366103949353267 49548342110049155924029901)
            ·
              refine ⟨18580628291268433471511213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49548342110049155924029901 18580628291268433471511213)
              ·
                refine ⟨6967735609225662551816705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18580628291268433471511213 6967735609225662551816705)
                ·
                  refine ⟨5225801706919246913862529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6967735609225662551816705 5225801706919246913862529)
                  ·
                    refine ⟨3919351280189435185396897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5225801706919246913862529 3919351280189435185396897)
                    ·
                      refine ⟨2939513460142076389047673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919351280189435185396897 2939513460142076389047673)
                      ·
                        rfl

theorem cell23_5724682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_5724682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724682 prefixEnd_5724682 := by exact prefixLift 5724682
  have htrace : WordTrace (prefixWord ++ tailWord_5724682) baseStart_5724682 baseEnd_5724682 := by
    simpa [prefixWord, tailWord_5724682, baseEnd_5724682] using wordTrace_append hprefix tailTrace_5724682
  have hstable : (prefixWord ++ tailWord_5724682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724682).length < 2 ^ (prefixWord ++ tailWord_5724682).sum := by decide
  have hdescent : baseEnd_5724682 < baseStart_5724682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724778 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 8]
def baseStart_5724778 : Nat := 118140960795 + 5724778 * 2 ^ 59
def prefixEnd_5724778 : Nat := 4983230072969 + 3 ^ 40 * 5724778 * 2
def baseEnd_5724778 : Nat := 326618083809434223716359

theorem tailTrace_5724778 : CollatzResearch.WordTrace tailWord_5724778 prefixEnd_5724778 326618083809434223716359 := by
  unfold tailWord_5724778
  simp only [CollatzResearch.WordTrace]
  refine ⟨52199951813528623771925747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139199871502742996725135325 52199951813528623771925747)
  ·
    refine ⟨78299927720292935657888621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52199951813528623771925747 78299927720292935657888621)
    ·
      refine ⟨29362472895109850871708233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78299927720292935657888621 29362472895109850871708233)
      ·
        refine ⟨22021854671332388153781175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29362472895109850871708233 22021854671332388153781175)
        ·
          refine ⟨33032782006998582230671763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22021854671332388153781175 33032782006998582230671763)
          ·
            refine ⟨49549173010497873346007645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33032782006998582230671763 49549173010497873346007645)
            ·
              refine ⟨18580939878936702504752867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49549173010497873346007645 18580939878936702504752867)
              ·
                refine ⟨27871409818405053757129301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18580939878936702504752867 27871409818405053757129301)
                ·
                  refine ⟨326618083809434223716359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27871409818405053757129301 326618083809434223716359)
                  ·
                    rfl

theorem cell23_5724778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_5724778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724778 prefixEnd_5724778 := by exact prefixLift 5724778
  have htrace : WordTrace (prefixWord ++ tailWord_5724778) baseStart_5724778 baseEnd_5724778 := by
    simpa [prefixWord, tailWord_5724778, baseEnd_5724778] using wordTrace_append hprefix tailTrace_5724778
  have hstable : (prefixWord ++ tailWord_5724778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724778).length < 2 ^ (prefixWord ++ tailWord_5724778).sum := by decide
  have hdescent : baseEnd_5724778 < baseStart_5724778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724782 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_5724782 : Nat := 118140960795 + 5724782 * 2 ^ 59
def prefixEnd_5724782 : Nat := 4983230072969 + 3 ^ 40 * 5724782 * 2
def baseEnd_5724782 : Nat := 979854936069175332599071

theorem tailTrace_5724782 : CollatzResearch.WordTrace tailWord_5724782 prefixEnd_5724782 979854936069175332599071 := by
  unfold tailWord_5724782
  simp only [CollatzResearch.WordTrace]
  refine ⟨26099994143262500471356075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139199968764066669180565733 26099994143262500471356075)
  ·
    refine ⟨39149991214893750707034113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26099994143262500471356075 39149991214893750707034113)
    ·
      refine ⟨29362493411170313030275585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39149991214893750707034113 29362493411170313030275585)
      ·
        refine ⟨22021870058377734772706689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29362493411170313030275585 22021870058377734772706689)
        ·
          refine ⟨16516402543783301079530017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22021870058377734772706689 16516402543783301079530017)
          ·
            refine ⟨12387301907837475809647513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16516402543783301079530017 12387301907837475809647513)
            ·
              refine ⟨9290476430878106857235635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12387301907837475809647513 9290476430878106857235635)
              ·
                refine ⟨13935714646317160285853453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9290476430878106857235635 13935714646317160285853453)
                ·
                  refine ⟨5225892992368935107195045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13935714646317160285853453 5225892992368935107195045)
                  ·
                    refine ⟨979854936069175332599071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5225892992368935107195045 979854936069175332599071)
                    ·
                      rfl

theorem cell23_5724782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_5724782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724782 prefixEnd_5724782 := by exact prefixLift 5724782
  have htrace : WordTrace (prefixWord ++ tailWord_5724782) baseStart_5724782 baseEnd_5724782 := by
    simpa [prefixWord, tailWord_5724782, baseEnd_5724782] using wordTrace_append hprefix tailTrace_5724782
  have hstable : (prefixWord ++ tailWord_5724782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724782).length < 2 ^ (prefixWord ++ tailWord_5724782).sum := by decide
  have hdescent : baseEnd_5724782 < baseStart_5724782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724848 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 3]
def baseStart_5724848 : Nat := 118140960795 + 5724848 * 2 ^ 59
def prefixEnd_5724848 : Nat := 4983230072969 + 3 ^ 40 * 5724848 * 2
def baseEnd_5724848 : Nat := 2939598697930722739571909

theorem tailTrace_5724848 : CollatzResearch.WordTrace tailWord_5724848 prefixEnd_5724848 2939598697930722739571909 := by
  unfold tailWord_5724848
  simp only [CollatzResearch.WordTrace]
  refine ⟨104401180181930448521375599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139201573575907264695167465 104401180181930448521375599)
  ·
    refine ⟨156601770272895672782063399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104401180181930448521375599 156601770272895672782063399)
    ·
      refine ⟨234902655409343509173095099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156601770272895672782063399 234902655409343509173095099)
      ·
        refine ⟨352353983114015263759642649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234902655409343509173095099 352353983114015263759642649)
        ·
          refine ⟨264265487335511447819731987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352353983114015263759642649 264265487335511447819731987)
          ·
            refine ⟨396398231003267171729597981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264265487335511447819731987 396398231003267171729597981)
            ·
              refine ⟨148649336626225189398599243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396398231003267171729597981 148649336626225189398599243)
              ·
                refine ⟨222974004939337784097898865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148649336626225189398599243 222974004939337784097898865)
                ·
                  refine ⟨167230503704503338073424149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222974004939337784097898865 167230503704503338073424149)
                  ·
                    refine ⟨7838929861148593972191757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 167230503704503338073424149 7838929861148593972191757)
                    ·
                      refine ⟨2939598697930722739571909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7838929861148593972191757 2939598697930722739571909)
                      ·
                        rfl

theorem cell23_5724848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 3].length) (baseStart_5724848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724848 prefixEnd_5724848 := by exact prefixLift 5724848
  have htrace : WordTrace (prefixWord ++ tailWord_5724848) baseStart_5724848 baseEnd_5724848 := by
    simpa [prefixWord, tailWord_5724848, baseEnd_5724848] using wordTrace_append hprefix tailTrace_5724848
  have hstable : (prefixWord ++ tailWord_5724848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724848).length < 2 ^ (prefixWord ++ tailWord_5724848).sum := by decide
  have hdescent : baseEnd_5724848 < baseStart_5724848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724858 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_5724858 : Nat := 118140960795 + 5724858 * 2 ^ 59
def prefixEnd_5724858 : Nat := 4983230072969 + 3 ^ 40 * 5724858 * 2
def baseEnd_5724858 : Nat := 2939603832737267700446863

theorem tailTrace_5724858 : CollatzResearch.WordTrace tailWord_5724858 prefixEnd_5724858 2939603832737267700446863 := by
  unfold tailWord_5724858
  simp only [CollatzResearch.WordTrace]
  refine ⟨52200681273456167187653807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139201816729216445833743485 52200681273456167187653807)
  ·
    refine ⟨78301021910184250781480711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52200681273456167187653807 78301021910184250781480711)
    ·
      refine ⟨117451532865276376172221067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78301021910184250781480711 117451532865276376172221067)
      ·
        refine ⟨176177299297914564258331601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117451532865276376172221067 176177299297914564258331601)
        ·
          refine ⟨132132974473435923193748701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176177299297914564258331601 132132974473435923193748701)
          ·
            refine ⟨49549865427538471197655763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132132974473435923193748701 49549865427538471197655763)
            ·
              refine ⟨74324798141307706796483645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49549865427538471197655763 74324798141307706796483645)
              ·
                refine ⟨27871799302990390048681367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74324798141307706796483645 27871799302990390048681367)
                ·
                  refine ⟨41807698954485585073022051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27871799302990390048681367 41807698954485585073022051)
                  ·
                    refine ⟨62711548431728377609533077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41807698954485585073022051 62711548431728377609533077)
                    ·
                      refine ⟨2939603832737267700446863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62711548431728377609533077 2939603832737267700446863)
                      ·
                        rfl

theorem cell23_5724858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_5724858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724858 prefixEnd_5724858 := by exact prefixLift 5724858
  have htrace : WordTrace (prefixWord ++ tailWord_5724858) baseStart_5724858 baseEnd_5724858 := by
    simpa [prefixWord, tailWord_5724858, baseEnd_5724858] using wordTrace_append hprefix tailTrace_5724858
  have hstable : (prefixWord ++ tailWord_5724858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724858).length < 2 ^ (prefixWord ++ tailWord_5724858).sum := by decide
  have hdescent : baseEnd_5724858 < baseStart_5724858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724885 : List Nat := [1, 3, 2, 5, 1, 11]
def baseStart_5724885 : Nat := 118140960795 + 5724885 * 2 ^ 59
def prefixEnd_5724885 : Nat := 4983230072969 + 3 ^ 40 * 5724885 * 2
def baseEnd_5724885 : Nat := 12097192167551189690573

theorem tailTrace_5724885 : CollatzResearch.WordTrace tailWord_5724885 prefixEnd_5724885 12097192167551189690573 := by
  unfold tailWord_5724885
  simp only [CollatzResearch.WordTrace]
  refine ⟨208803709864726852361848109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139202473243151234907898739 208803709864726852361848109)
  ·
    refine ⟨78301391199272569635693041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208803709864726852361848109 78301391199272569635693041)
    ·
      refine ⟨58726043399454427226769781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78301391199272569635693041 58726043399454427226769781)
      ·
        refine ⟨5505566568698852552509667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58726043399454427226769781 5505566568698852552509667)
        ·
          refine ⟨8258349853048278828764501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5505566568698852552509667 8258349853048278828764501)
          ·
            refine ⟨12097192167551189690573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8258349853048278828764501 12097192167551189690573)
            ·
              rfl

theorem cell23_5724885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 11].length) (baseStart_5724885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724885 prefixEnd_5724885 := by exact prefixLift 5724885
  have htrace : WordTrace (prefixWord ++ tailWord_5724885) baseStart_5724885 baseEnd_5724885 := by
    simpa [prefixWord, tailWord_5724885, baseEnd_5724885] using wordTrace_append hprefix tailTrace_5724885
  have hstable : (prefixWord ++ tailWord_5724885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724885).length < 2 ^ (prefixWord ++ tailWord_5724885).sum := by decide
  have hdescent : baseEnd_5724885 < baseStart_5724885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724908 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_5724908 : Nat := 118140960795 + 5724908 * 2 ^ 59
def prefixEnd_5724908 : Nat := 4983230072969 + 3 ^ 40 * 5724908 * 2
def baseEnd_5724908 : Nat := 2939629506769992504821633

theorem tailTrace_5724908 : CollatzResearch.WordTrace tailWord_5724908 prefixEnd_5724908 2939629506769992504821633 := by
  unfold tailWord_5724908
  simp only [CollatzResearch.WordTrace]
  refine ⟨104402274371821763644967689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139203032495762351526623585 104402274371821763644967689)
  ·
    refine ⟨78301705778866322733725767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104402274371821763644967689 78301705778866322733725767)
    ·
      refine ⟨117452558668299484100588651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78301705778866322733725767 117452558668299484100588651)
      ·
        refine ⟨176178838002449226150882977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117452558668299484100588651 176178838002449226150882977)
        ·
          refine ⟨132134128501836919613162233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176178838002449226150882977 132134128501836919613162233)
          ·
            refine ⟨99100596376377689709871675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132134128501836919613162233 99100596376377689709871675)
            ·
              refine ⟨148650894564566534564807513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99100596376377689709871675 148650894564566534564807513)
              ·
                refine ⟨111488170923424900923605635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148650894564566534564807513 111488170923424900923605635)
                ·
                  refine ⟨167232256385137351385408453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111488170923424900923605635 167232256385137351385408453)
                  ·
                    refine ⟨31356048072213253384764085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167232256385137351385408453 31356048072213253384764085)
                    ·
                      refine ⟨2939629506769992504821633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31356048072213253384764085 2939629506769992504821633)
                      ·
                        rfl

theorem cell23_5724908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_5724908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724908 prefixEnd_5724908 := by exact prefixLift 5724908
  have htrace : WordTrace (prefixWord ++ tailWord_5724908) baseStart_5724908 baseEnd_5724908 := by
    simpa [prefixWord, tailWord_5724908, baseEnd_5724908] using wordTrace_append hprefix tailTrace_5724908
  have hstable : (prefixWord ++ tailWord_5724908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724908).length < 2 ^ (prefixWord ++ tailWord_5724908).sum := by decide
  have hdescent : baseEnd_5724908 < baseStart_5724908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724912 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 2, 1, 3]
def baseStart_5724912 : Nat := 118140960795 + 5724912 * 2 ^ 59
def prefixEnd_5724912 : Nat := 4983230072969 + 3 ^ 40 * 5724912 * 2
def baseEnd_5724912 : Nat := 2939631560692610489171615

theorem tailTrace_5724912 : CollatzResearch.WordTrace tailWord_5724912 prefixEnd_5724912 2939631560692610489171615 := by
  unfold tailWord_5724912
  simp only [CollatzResearch.WordTrace]
  refine ⟨104402347317814517986540495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139203129757086023982053993 104402347317814517986540495)
  ·
    refine ⟨156603520976721776979810743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104402347317814517986540495 156603520976721776979810743)
    ·
      refine ⟨234905281465082665469716115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156603520976721776979810743 234905281465082665469716115)
      ·
        refine ⟨352357922197623998204574173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234905281465082665469716115 352357922197623998204574173)
        ·
          refine ⟨132134220824108999326715315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352357922197623998204574173 132134220824108999326715315)
          ·
            refine ⟨198201331236163498990072973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132134220824108999326715315 198201331236163498990072973)
            ·
              refine ⟨74325499213561312121277365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198201331236163498990072973 74325499213561312121277365)
              ·
                refine ⟨6968015551271373011369753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74325499213561312121277365 6968015551271373011369753)
                ·
                  refine ⟨5226011663453529758527315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6968015551271373011369753 5226011663453529758527315)
                  ·
                    refine ⟨7839017495180294637790973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5226011663453529758527315 7839017495180294637790973)
                    ·
                      refine ⟨2939631560692610489171615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7839017495180294637790973 2939631560692610489171615)
                      ·
                        rfl

theorem cell23_5724912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2, 1, 3].length) (baseStart_5724912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724912 prefixEnd_5724912 := by exact prefixLift 5724912
  have htrace : WordTrace (prefixWord ++ tailWord_5724912) baseStart_5724912 baseEnd_5724912 := by
    simpa [prefixWord, tailWord_5724912, baseEnd_5724912] using wordTrace_append hprefix tailTrace_5724912
  have hstable : (prefixWord ++ tailWord_5724912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724912).length < 2 ^ (prefixWord ++ tailWord_5724912).sum := by decide
  have hdescent : baseEnd_5724912 < baseStart_5724912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724922 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2]
def baseStart_5724922 : Nat := 118140960795 + 5724922 * 2 ^ 59
def prefixEnd_5724922 : Nat := 4983230072969 + 3 ^ 40 * 5724922 * 2
def baseEnd_5724922 : Nat := 2939636695499155450046569

theorem tailTrace_5724922 : CollatzResearch.WordTrace tailWord_5724922 prefixEnd_5724922 2939636695499155450046569 := by
  unfold tailWord_5724922
  simp only [CollatzResearch.WordTrace]
  refine ⟨52201264841398201920236255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139203372910395205120630013 52201264841398201920236255)
  ·
    refine ⟨78301897262097302880354383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52201264841398201920236255 78301897262097302880354383)
    ·
      refine ⟨117452845893145954320531575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78301897262097302880354383 117452845893145954320531575)
      ·
        refine ⟨176179268839718931480797363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117452845893145954320531575 176179268839718931480797363)
        ·
          refine ⟨264268903259578397221196045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176179268839718931480797363 264268903259578397221196045)
          ·
            refine ⟨99100838722341898957948517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264268903259578397221196045 99100838722341898957948517)
            ·
              refine ⟨18581407260439106054615347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99100838722341898957948517 18581407260439106054615347)
              ·
                refine ⟨27872110890658659081923021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18581407260439106054615347 27872110890658659081923021)
                ·
                  refine ⟨10452041583996997155721133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27872110890658659081923021 10452041583996997155721133)
                  ·
                    refine ⟨3919515593998873933395425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10452041583996997155721133 3919515593998873933395425)
                    ·
                      refine ⟨2939636695499155450046569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919515593998873933395425 2939636695499155450046569)
                      ·
                        rfl

theorem cell23_5724922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2].length) (baseStart_5724922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724922 prefixEnd_5724922 := by exact prefixLift 5724922
  have htrace : WordTrace (prefixWord ++ tailWord_5724922) baseStart_5724922 baseEnd_5724922 := by
    simpa [prefixWord, tailWord_5724922, baseEnd_5724922] using wordTrace_append hprefix tailTrace_5724922
  have hstable : (prefixWord ++ tailWord_5724922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724922).length < 2 ^ (prefixWord ++ tailWord_5724922).sum := by decide
  have hdescent : baseEnd_5724922 < baseStart_5724922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724928 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 6, 6]
def baseStart_5724928 : Nat := 118140960795 + 5724928 * 2 ^ 59
def prefixEnd_5724928 : Nat := 4983230072969 + 3 ^ 40 * 5724928 * 2
def baseEnd_5724928 : Nat := 979879925461027475523847

theorem tailTrace_5724928 : CollatzResearch.WordTrace tailWord_5724928 prefixEnd_5724928 979879925461027475523847 := by
  unfold tailWord_5724928
  simp only [CollatzResearch.WordTrace]
  refine ⟨104402639101785535352831719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139203518802380713803775625 104402639101785535352831719)
  ·
    refine ⟨156603958652678303029247579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104402639101785535352831719 156603958652678303029247579)
    ·
      refine ⟨234905937979017454543871369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156603958652678303029247579 234905937979017454543871369)
      ·
        refine ⟨176179453484263090907903527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234905937979017454543871369 176179453484263090907903527)
        ·
          refine ⟨264269180226394636361855291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176179453484263090907903527 264269180226394636361855291)
          ·
            refine ⟨396403770339591954542782937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264269180226394636361855291 396403770339591954542782937)
            ·
              refine ⟨297302827754693965907087203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396403770339591954542782937 297302827754693965907087203)
              ·
                refine ⟨445954241632040948860630805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297302827754693965907087203 445954241632040948860630805)
                ·
                  refine ⟨20904105076501919477842069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 445954241632040948860630805 20904105076501919477842069)
                  ·
                    refine ⟨979879925461027475523847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20904105076501919477842069 979879925461027475523847)
                    ·
                      rfl

theorem cell23_5724928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_5724928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724928 prefixEnd_5724928 := by exact prefixLift 5724928
  have htrace : WordTrace (prefixWord ++ tailWord_5724928) baseStart_5724928 baseEnd_5724928 := by
    simpa [prefixWord, tailWord_5724928, baseEnd_5724928] using wordTrace_append hprefix tailTrace_5724928
  have hstable : (prefixWord ++ tailWord_5724928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724928).length < 2 ^ (prefixWord ++ tailWord_5724928).sum := by decide
  have hdescent : baseEnd_5724928 < baseStart_5724928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724946 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_5724946 : Nat := 118140960795 + 5724946 * 2 ^ 59
def prefixEnd_5724946 : Nat := 4983230072969 + 3 ^ 40 * 5724946 * 2
def baseEnd_5724946 : Nat := 2939649019034863356146459

theorem tailTrace_5724946 : CollatzResearch.WordTrace tailWord_5724946 prefixEnd_5724946 2939649019034863356146459 := by
  unfold tailWord_5724946
  simp only [CollatzResearch.WordTrace]
  refine ⟨52201483679376464944954673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139203956478337239853212461 52201483679376464944954673)
  ·
    refine ⟨39151112759532348708716005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52201483679376464944954673 39151112759532348708716005)
    ·
      refine ⟨7340833642412315382884251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39151112759532348708716005 7340833642412315382884251)
      ·
        refine ⟨11011250463618473074326377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7340833642412315382884251 11011250463618473074326377)
        ·
          refine ⟨8258437847713854805744783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11011250463618473074326377 8258437847713854805744783)
          ·
            refine ⟨12387656771570782208617175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8258437847713854805744783 12387656771570782208617175)
            ·
              refine ⟨18581485157356173312925763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12387656771570782208617175 18581485157356173312925763)
              ·
                refine ⟨27872227736034259969388645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18581485157356173312925763 27872227736034259969388645)
                ·
                  refine ⟨5226042700506423744260371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27872227736034259969388645 5226042700506423744260371)
                  ·
                    refine ⟨7839064050759635616390557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5226042700506423744260371 7839064050759635616390557)
                    ·
                      refine ⟨2939649019034863356146459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7839064050759635616390557 2939649019034863356146459)
                      ·
                        rfl

theorem cell23_5724946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_5724946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724946 prefixEnd_5724946 := by exact prefixLift 5724946
  have htrace : WordTrace (prefixWord ++ tailWord_5724946) baseStart_5724946 baseEnd_5724946 := by
    simpa [prefixWord, tailWord_5724946, baseEnd_5724946] using wordTrace_append hprefix tailTrace_5724946
  have hstable : (prefixWord ++ tailWord_5724946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724946).length < 2 ^ (prefixWord ++ tailWord_5724946).sum := by decide
  have hdescent : baseEnd_5724946 < baseStart_5724946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5724965 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_5724965 : Nat := 118140960795 + 5724965 * 2 ^ 59
def prefixEnd_5724965 : Nat := 4983230072969 + 3 ^ 40 * 5724965 * 2
def baseEnd_5724965 : Nat := 2939658775167298781808871

theorem tailTrace_5724965 : CollatzResearch.WordTrace tailWord_5724965 prefixEnd_5724965 2939658775167298781808871 := by
  unfold tailWord_5724965
  simp only [CollatzResearch.WordTrace]
  refine ⟨208806627704437026024760349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139204418469624684016506899 208806627704437026024760349)
  ·
    refine ⟨78302485389163884759285131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208806627704437026024760349 78302485389163884759285131)
    ·
      refine ⟨117453728083745827138927697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78302485389163884759285131 117453728083745827138927697)
      ·
        refine ⟨88090296062809370354195773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117453728083745827138927697 88090296062809370354195773)
        ·
          refine ⟨33033861023553513882823415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88090296062809370354195773 33033861023553513882823415)
          ·
            refine ⟨49550791535330270824235123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33033861023553513882823415 49550791535330270824235123)
            ·
              refine ⟨74326187302995406236352685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49550791535330270824235123 74326187302995406236352685)
              ·
                refine ⟨27872320238623277338632257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74326187302995406236352685 27872320238623277338632257)
                ·
                  refine ⟨20904240178967458003974193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27872320238623277338632257 20904240178967458003974193)
                  ·
                    refine ⟨15678180134225593502980645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20904240178967458003974193 15678180134225593502980645)
                    ·
                      refine ⟨2939658775167298781808871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15678180134225593502980645 2939658775167298781808871)
                      ·
                        rfl

theorem cell23_5724965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_5724965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5724965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5724965 prefixEnd_5724965 := by exact prefixLift 5724965
  have htrace : WordTrace (prefixWord ++ tailWord_5724965) baseStart_5724965 baseEnd_5724965 := by
    simpa [prefixWord, tailWord_5724965, baseEnd_5724965] using wordTrace_append hprefix tailTrace_5724965
  have hstable : (prefixWord ++ tailWord_5724965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5724965).length < 2 ^ (prefixWord ++ tailWord_5724965).sum := by decide
  have hdescent : baseEnd_5724965 < baseStart_5724965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5724965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725009 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 7]
def baseStart_5725009 : Nat := 118140960795 + 5725009 * 2 ^ 59
def prefixEnd_5725009 : Nat := 4983230072969 + 3 ^ 40 * 5725009 * 2
def baseEnd_5725009 : Nat := 326631263146232956628741

theorem tailTrace_5725009 : CollatzResearch.WordTrace tailWord_5725009 prefixEnd_5725009 326631263146232956628741 := by
  unfold tailWord_5725009
  simp only [CollatzResearch.WordTrace]
  refine ⟨208808232516277621539362081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139205488344185081026241387 208808232516277621539362081)
  ·
    refine ⟨156606174387208216154521561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208808232516277621539362081 156606174387208216154521561)
    ·
      refine ⟨117454630790406162115891171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156606174387208216154521561 117454630790406162115891171)
      ·
        refine ⟨176181946185609243173836757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117454630790406162115891171 176181946185609243173836757)
        ·
          refine ⟨4129264363725216636886799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 176181946185609243173836757 4129264363725216636886799)
          ·
            refine ⟨6193896545587824955330199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129264363725216636886799 6193896545587824955330199)
            ·
              refine ⟨9290844818381737432995299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6193896545587824955330199 9290844818381737432995299)
              ·
                refine ⟨13936267227572606149492949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9290844818381737432995299 13936267227572606149492949)
                ·
                  refine ⟨326631263146232956628741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13936267227572606149492949 326631263146232956628741)
                  ·
                    rfl

theorem cell23_5725009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 7].length) (baseStart_5725009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725009 prefixEnd_5725009 := by exact prefixLift 5725009
  have htrace : WordTrace (prefixWord ++ tailWord_5725009) baseStart_5725009 baseEnd_5725009 := by
    simpa [prefixWord, tailWord_5725009, baseEnd_5725009] using wordTrace_append hprefix tailTrace_5725009
  have hstable : (prefixWord ++ tailWord_5725009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725009).length < 2 ^ (prefixWord ++ tailWord_5725009).sum := by decide
  have hdescent : baseEnd_5725009 < baseStart_5725009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725015 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_5725015 : Nat := 118140960795 + 5725015 * 2 ^ 59
def prefixEnd_5725015 : Nat := 4983230072969 + 3 ^ 40 * 5725015 * 2
def baseEnd_5725015 : Nat := 2939684449200023586183641

theorem tailTrace_5725015 : CollatzResearch.WordTrace tailWord_5725015 prefixEnd_5725015 2939684449200023586183641 := by
  unfold tailWord_5725015
  simp only [CollatzResearch.WordTrace]
  refine ⟨208808451354255884564080499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139205634236170589709386999 208808451354255884564080499)
  ·
    refine ⟨313212677031383826846120749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208808451354255884564080499 313212677031383826846120749)
    ·
      refine ⟨117454753886768935067295281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313212677031383826846120749 117454753886768935067295281)
      ·
        refine ⟨88091065415076701300471461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117454753886768935067295281 88091065415076701300471461)
        ·
          refine ⟨16517074765326881493838399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88091065415076701300471461 16517074765326881493838399)
          ·
            refine ⟨24775612147990322240757599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16517074765326881493838399 24775612147990322240757599)
            ·
              refine ⟨37163418221985483361136399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24775612147990322240757599 37163418221985483361136399)
              ·
                refine ⟨55745127332978225041704599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37163418221985483361136399 55745127332978225041704599)
                ·
                  refine ⟨83617690999467337562556899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55745127332978225041704599 83617690999467337562556899)
                  ·
                    refine ⟨125426536499201006343835349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83617690999467337562556899 125426536499201006343835349)
                    ·
                      refine ⟨2939684449200023586183641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125426536499201006343835349 2939684449200023586183641)
                      ·
                        rfl

theorem cell23_5725015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_5725015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725015 prefixEnd_5725015 := by exact prefixLift 5725015
  have htrace : WordTrace (prefixWord ++ tailWord_5725015) baseStart_5725015 baseEnd_5725015 := by
    simpa [prefixWord, tailWord_5725015, baseEnd_5725015] using wordTrace_append hprefix tailTrace_5725015
  have hstable : (prefixWord ++ tailWord_5725015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725015).length < 2 ^ (prefixWord ++ tailWord_5725015).sum := by decide
  have hdescent : baseEnd_5725015 < baseStart_5725015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725020 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_5725020 : Nat := 118140960795 + 5725020 * 2 ^ 59
def prefixEnd_5725020 : Nat := 4983230072969 + 3 ^ 40 * 5725020 * 2
def baseEnd_5725020 : Nat := 2939687016603296066621119

theorem tailTrace_5725020 : CollatzResearch.WordTrace tailWord_5725020 prefixEnd_5725020 2939687016603296066621119 := by
  unfold tailWord_5725020
  simp only [CollatzResearch.WordTrace]
  refine ⟨104404316859618885209006257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139205755812825180278675009 104404316859618885209006257)
  ·
    refine ⟨78303237644714163906754693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104404316859618885209006257 78303237644714163906754693)
    ·
      refine ⟨14681857058383905732516505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78303237644714163906754693 14681857058383905732516505)
      ·
        refine ⟨11011392793787929299387379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14681857058383905732516505 11011392793787929299387379)
        ·
          refine ⟨16517089190681893949081069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11011392793787929299387379 16517089190681893949081069)
          ·
            refine ⟨6193908446505710230905401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16517089190681893949081069 6193908446505710230905401)
            ·
              refine ⟨4645431334879282673179051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6193908446505710230905401 4645431334879282673179051)
              ·
                refine ⟨6968147002318924009768577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4645431334879282673179051 6968147002318924009768577)
                ·
                  refine ⟨5226110251739193007326433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6968147002318924009768577 5226110251739193007326433)
                  ·
                    refine ⟨3919582688804394755494825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5226110251739193007326433 3919582688804394755494825)
                    ·
                      refine ⟨2939687016603296066621119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919582688804394755494825 2939687016603296066621119)
                      ·
                        rfl

theorem cell23_5725020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_5725020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725020 prefixEnd_5725020 := by exact prefixLift 5725020
  have htrace : WordTrace (prefixWord ++ tailWord_5725020) baseStart_5725020 baseEnd_5725020 := by
    simpa [prefixWord, tailWord_5725020, baseEnd_5725020] using wordTrace_append hprefix tailTrace_5725020
  have hstable : (prefixWord ++ tailWord_5725020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725020).length < 2 ^ (prefixWord ++ tailWord_5725020).sum := by decide
  have hdescent : baseEnd_5725020 < baseStart_5725020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725025 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_5725025 : Nat := 118140960795 + 5725025 * 2 ^ 59
def prefixEnd_5725025 : Nat := 4983230072969 + 3 ^ 40 * 5725025 * 2
def baseEnd_5725025 : Nat := 2939689584006568547058595

theorem tailTrace_5725025 : CollatzResearch.WordTrace tailWord_5725025 prefixEnd_5725025 2939689584006568547058595 := by
  unfold tailWord_5725025
  simp only [CollatzResearch.WordTrace]
  refine ⟨208808816084219656271944529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139205877389479770847963019 208808816084219656271944529)
  ·
    refine ⟨156606612063164742203958397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208808816084219656271944529 156606612063164742203958397)
    ·
      refine ⟨58727479523686778326484399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156606612063164742203958397 58727479523686778326484399)
      ·
        refine ⟨88091219285530167489726599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58727479523686778326484399 88091219285530167489726599)
        ·
          refine ⟨132136828928295251234589899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88091219285530167489726599 132136828928295251234589899)
          ·
            refine ⟨198205243392442876851884849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132136828928295251234589899 198205243392442876851884849)
            ·
              refine ⟨148653932544332157638913637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198205243392442876851884849 148653932544332157638913637)
              ·
                refine ⟨27872612352062279557296307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148653932544332157638913637 27872612352062279557296307)
                ·
                  refine ⟨41808918528093419335944461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27872612352062279557296307 41808918528093419335944461)
                  ·
                    refine ⟨15678344448035032250979173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41808918528093419335944461 15678344448035032250979173)
                    ·
                      refine ⟨2939689584006568547058595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15678344448035032250979173 2939689584006568547058595)
                      ·
                        rfl

theorem cell23_5725025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_5725025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725025 prefixEnd_5725025 := by exact prefixLift 5725025
  have htrace : WordTrace (prefixWord ++ tailWord_5725025) baseStart_5725025 baseEnd_5725025 := by
    simpa [prefixWord, tailWord_5725025, baseEnd_5725025] using wordTrace_append hprefix tailTrace_5725025
  have hstable : (prefixWord ++ tailWord_5725025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725025).length < 2 ^ (prefixWord ++ tailWord_5725025).sum := by decide
  have hdescent : baseEnd_5725025 < baseStart_5725025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725042 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_5725042 : Nat := 118140960795 + 5725042 * 2 ^ 59
def prefixEnd_5725042 : Nat := 4983230072969 + 3 ^ 40 * 5725042 * 2
def baseEnd_5725042 : Nat := 2939698313177694980546017

theorem tailTrace_5725042 : CollatzResearch.WordTrace tailWord_5725042 prefixEnd_5725042 2939698313177694980546017 := by
  unfold tailWord_5725042
  simp only [CollatzResearch.WordTrace]
  refine ⟨52202359031289517043828345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139206290750105378783542253 52202359031289517043828345)
  ·
    refine ⟨39151769273467137782871259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52202359031289517043828345 39151769273467137782871259)
    ·
      refine ⟨58727653910200706674306889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39151769273467137782871259 58727653910200706674306889)
      ·
        refine ⟨44045740432650530005730167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58727653910200706674306889 44045740432650530005730167)
        ·
          refine ⟨66068610648975795008595251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44045740432650530005730167 66068610648975795008595251)
          ·
            refine ⟨99102915973463692512892877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66068610648975795008595251 99102915973463692512892877)
            ·
              refine ⟨37163593490048884692334829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99102915973463692512892877 37163593490048884692334829)
              ·
                refine ⟨13936347558768331759625561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37163593490048884692334829 13936347558768331759625561)
                ·
                  refine ⟨10452260669076248819719171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13936347558768331759625561 10452260669076248819719171)
                  ·
                    refine ⟨15678391003614373229578757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10452260669076248819719171 15678391003614373229578757)
                    ·
                      refine ⟨2939698313177694980546017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15678391003614373229578757 2939698313177694980546017)
                      ·
                        rfl

theorem cell23_5725042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_5725042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725042 prefixEnd_5725042 := by exact prefixLift 5725042
  have htrace : WordTrace (prefixWord ++ tailWord_5725042) baseStart_5725042 baseEnd_5725042 := by
    simpa [prefixWord, tailWord_5725042, baseEnd_5725042] using wordTrace_append hprefix tailTrace_5725042
  have hstable : (prefixWord ++ tailWord_5725042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725042).length < 2 ^ (prefixWord ++ tailWord_5725042).sum := by decide
  have hdescent : baseEnd_5725042 < baseStart_5725042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725109 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_5725109 : Nat := 118140960795 + 5725109 * 2 ^ 59
def prefixEnd_5725109 : Nat := 4983230072969 + 3 ^ 40 * 5725109 * 2
def baseEnd_5725109 : Nat := 2939732716381546218408209

theorem tailTrace_5725109 : CollatzResearch.WordTrace tailWord_5725109 prefixEnd_5725109 2939732716381546218408209 := by
  unfold tailWord_5725109
  simp only [CollatzResearch.WordTrace]
  refine ⟨208811879815915338618002381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139207919877276892412001587 208811879815915338618002381)
  ·
    refine ⟨78304454930968251981750893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208811879815915338618002381 78304454930968251981750893)
    ·
      refine ⟨29364170599113094493156585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78304454930968251981750893 29364170599113094493156585)
      ·
        refine ⟨22023127949334820869867439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29364170599113094493156585 22023127949334820869867439)
        ·
          refine ⟨33034691924002231304801159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22023127949334820869867439 33034691924002231304801159)
          ·
            refine ⟨49552037886003346957201739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33034691924002231304801159 49552037886003346957201739)
            ·
              refine ⟨74328056829005020435802609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49552037886003346957201739 74328056829005020435802609)
              ·
                refine ⟨55746042621753765326851957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74328056829005020435802609 55746042621753765326851957)
                ·
                  refine ⟨5226191495789415499392371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55746042621753765326851957 5226191495789415499392371)
                  ·
                    refine ⟨7839287243684123249088557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5226191495789415499392371 7839287243684123249088557)
                    ·
                      refine ⟨2939732716381546218408209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7839287243684123249088557 2939732716381546218408209)
                      ·
                        rfl

theorem cell23_5725109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_5725109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725109 prefixEnd_5725109 := by exact prefixLift 5725109
  have htrace : WordTrace (prefixWord ++ tailWord_5725109) baseStart_5725109 baseEnd_5725109 := by
    simpa [prefixWord, tailWord_5725109, baseEnd_5725109] using wordTrace_append hprefix tailTrace_5725109
  have hstable : (prefixWord ++ tailWord_5725109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725109).length < 2 ^ (prefixWord ++ tailWord_5725109).sum := by decide
  have hdescent : baseEnd_5725109 < baseStart_5725109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725115 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 4]
def baseStart_5725115 : Nat := 118140960795 + 5725115 * 2 ^ 59
def prefixEnd_5725115 : Nat := 4983230072969 + 3 ^ 40 * 5725115 * 2
def baseEnd_5725115 : Nat := 2939735797265473194933181

theorem tailTrace_5725115 : CollatzResearch.WordTrace tailWord_5725115 prefixEnd_5725115 2939735797265473194933181 := by
  unfold tailWord_5725115
  simp only [CollatzResearch.WordTrace]
  refine ⟨208812098653893601642720799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139208065769262401095147199 208812098653893601642720799)
  ·
    refine ⟨313218147980840402464081199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208812098653893601642720799 313218147980840402464081199)
    ·
      refine ⟨469827221971260603696121799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313218147980840402464081199 469827221971260603696121799)
      ·
        refine ⟨704740832956890905544182699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469827221971260603696121799 704740832956890905544182699)
        ·
          refine ⟨1057111249435336358316274049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704740832956890905544182699 1057111249435336358316274049)
          ·
            refine ⟨792833437076502268737205537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057111249435336358316274049 792833437076502268737205537)
            ·
              refine ⟨594625077807376701552904153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792833437076502268737205537 594625077807376701552904153)
              ·
                refine ⟨445968808355532526164678115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594625077807376701552904153 445968808355532526164678115)
                ·
                  refine ⟨668953212533298789247017173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445968808355532526164678115 668953212533298789247017173)
                  ·
                    refine ⟨15678590918749190372976965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 668953212533298789247017173 15678590918749190372976965)
                    ·
                      refine ⟨2939735797265473194933181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15678590918749190372976965 2939735797265473194933181)
                      ·
                        rfl

theorem cell23_5725115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 4].length) (baseStart_5725115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725115 prefixEnd_5725115 := by exact prefixLift 5725115
  have htrace : WordTrace (prefixWord ++ tailWord_5725115) baseStart_5725115 baseEnd_5725115 := by
    simpa [prefixWord, tailWord_5725115, baseEnd_5725115] using wordTrace_append hprefix tailTrace_5725115
  have hstable : (prefixWord ++ tailWord_5725115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725115).length < 2 ^ (prefixWord ++ tailWord_5725115).sum := by decide
  have hdescent : baseEnd_5725115 < baseStart_5725115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725159 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 4, 4]
def baseStart_5725159 : Nat := 118140960795 + 5725159 * 2 ^ 59
def prefixEnd_5725159 : Nat := 4983230072969 + 3 ^ 40 * 5725159 * 2
def baseEnd_5725159 : Nat := 979919463471423674260993

theorem tailTrace_5725159 : CollatzResearch.WordTrace tailWord_5725159 prefixEnd_5725159 979919463471423674260993 := by
  unfold tailWord_5725159
  simp only [CollatzResearch.WordTrace]
  refine ⟨208813703465734197157322531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139209135643822798104881687 208813703465734197157322531)
  ·
    refine ⟨313220555198601295735983797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208813703465734197157322531 313220555198601295735983797)
    ·
      refine ⟨29364427049868871475248481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 313220555198601295735983797 29364427049868871475248481)
      ·
        refine ⟨22023320287401653606436361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29364427049868871475248481 22023320287401653606436361)
        ·
          refine ⟨16517490215551240204827271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22023320287401653606436361 16517490215551240204827271)
          ·
            refine ⟨24776235323326860307240907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16517490215551240204827271 24776235323326860307240907)
            ·
              refine ⟨37164352984990290460861361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24776235323326860307240907 37164352984990290460861361)
              ·
                refine ⟨27873264738742717845646021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37164352984990290460861361 27873264738742717845646021)
                ·
                  refine ⟨5226237138514259596058629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27873264738742717845646021 5226237138514259596058629)
                  ·
                    refine ⟨979919463471423674260993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5226237138514259596058629 979919463471423674260993)
                    ·
                      rfl

theorem cell23_5725159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_5725159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725159 prefixEnd_5725159 := by exact prefixLift 5725159
  have htrace : WordTrace (prefixWord ++ tailWord_5725159) baseStart_5725159 baseEnd_5725159 := by
    simpa [prefixWord, tailWord_5725159, baseEnd_5725159] using wordTrace_append hprefix tailTrace_5725159
  have hstable : (prefixWord ++ tailWord_5725159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725159).length < 2 ^ (prefixWord ++ tailWord_5725159).sum := by decide
  have hdescent : baseEnd_5725159 < baseStart_5725159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725169 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 5]
def baseStart_5725169 : Nat := 118140960795 + 5725169 * 2 ^ 59
def prefixEnd_5725169 : Nat := 4983230072969 + 3 ^ 40 * 5725169 * 2
def baseEnd_5725169 : Nat := 2939763525220815983657933

theorem tailTrace_5725169 : CollatzResearch.WordTrace tailWord_5725169 prefixEnd_5725169 2939763525220815983657933 := by
  unfold tailWord_5725169
  simp only [CollatzResearch.WordTrace]
  refine ⟨208814068195697968865186561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139209378797131979243457707 208814068195697968865186561)
  ·
    refine ⟨156610551146773476648889921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208814068195697968865186561 156610551146773476648889921)
    ·
      refine ⟨117457913360080107486667441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156610551146773476648889921 117457913360080107486667441)
      ·
        refine ⟨88093435020060080615000581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117457913360080107486667441 88093435020060080615000581)
        ·
          refine ⟨16517519066261265115312609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88093435020060080615000581 16517519066261265115312609)
          ·
            refine ⟨12388139299695948836484457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16517519066261265115312609 12388139299695948836484457)
            ·
              refine ⟨9291104474771961627363343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12388139299695948836484457 9291104474771961627363343)
              ·
                refine ⟨13936656712157942441045015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9291104474771961627363343 13936656712157942441045015)
                ·
                  refine ⟨20904985068236913661567523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13936656712157942441045015 20904985068236913661567523)
                  ·
                    refine ⟨31357477602355370492351285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20904985068236913661567523 31357477602355370492351285)
                    ·
                      refine ⟨2939763525220815983657933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31357477602355370492351285 2939763525220815983657933)
                      ·
                        rfl

theorem cell23_5725169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_5725169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725169 prefixEnd_5725169 := by exact prefixLift 5725169
  have htrace : WordTrace (prefixWord ++ tailWord_5725169) baseStart_5725169 baseEnd_5725169 := by
    simpa [prefixWord, tailWord_5725169, baseEnd_5725169] using wordTrace_append hprefix tailTrace_5725169
  have hstable : (prefixWord ++ tailWord_5725169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725169).length < 2 ^ (prefixWord ++ tailWord_5725169).sum := by decide
  have hdescent : baseEnd_5725169 < baseStart_5725169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725232 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 2, 6]
def baseStart_5725232 : Nat := 118140960795 + 5725232 * 2 ^ 59
def prefixEnd_5725232 : Nat := 4983230072969 + 3 ^ 40 * 5725232 * 2
def baseEnd_5725232 : Nat := 979931958167349745723381

theorem tailTrace_5725232 : CollatzResearch.WordTrace tailWord_5725232 prefixEnd_5725232 979931958167349745723381 := by
  unfold tailWord_5725232
  simp only [CollatzResearch.WordTrace]
  refine ⟨104408182997234865312364975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139210910662979820416486633 104408182997234865312364975)
  ·
    refine ⟨156612274495852297968547463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104408182997234865312364975 156612274495852297968547463)
    ·
      refine ⟨234918411743778446952821195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156612274495852297968547463 234918411743778446952821195)
      ·
        refine ⟨352377617615667670429231793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234918411743778446952821195 352377617615667670429231793)
        ·
          refine ⟨264283213211750752821923845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352377617615667670429231793 264283213211750752821923845)
          ·
            refine ⟨49553102477203266154110721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264283213211750752821923845 49553102477203266154110721)
            ·
              refine ⟨37164826857902449615583041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49553102477203266154110721 37164826857902449615583041)
              ·
                refine ⟨27873620143426837211687281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37164826857902449615583041 27873620143426837211687281)
                ·
                  refine ⟨20905215107570127908765461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27873620143426837211687281 20905215107570127908765461)
                  ·
                    refine ⟨979931958167349745723381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20905215107570127908765461 979931958167349745723381)
                    ·
                      rfl

theorem cell23_5725232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_5725232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725232 prefixEnd_5725232 := by exact prefixLift 5725232
  have htrace : WordTrace (prefixWord ++ tailWord_5725232) baseStart_5725232 baseEnd_5725232 := by
    simpa [prefixWord, tailWord_5725232, baseEnd_5725232] using wordTrace_append hprefix tailTrace_5725232
  have hstable : (prefixWord ++ tailWord_5725232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725232).length < 2 ^ (prefixWord ++ tailWord_5725232).sum := by decide
  have hdescent : baseEnd_5725232 < baseStart_5725232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725239 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 5, 4, 2]
def baseStart_5725239 : Nat := 118140960795 + 5725239 * 2 ^ 59
def prefixEnd_5725239 : Nat := 4983230072969 + 3 ^ 40 * 5725239 * 2
def baseEnd_5725239 : Nat := 2939799468866630709782611

theorem tailTrace_5725239 : CollatzResearch.WordTrace tailWord_5725239 prefixEnd_5725239 2939799468866630709782611 := by
  unfold tailWord_5725239
  simp only [CollatzResearch.WordTrace]
  refine ⟨208816621305444370820234771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139211080870296247213489847 208816621305444370820234771)
  ·
    refine ⟨313224931958166556230352157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208816621305444370820234771 313224931958166556230352157)
    ·
      refine ⟨117459349484312458586382059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313224931958166556230352157 117459349484312458586382059)
      ·
        refine ⟨176189024226468687879573089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117459349484312458586382059 176189024226468687879573089)
        ·
          refine ⟨132141768169851515909679817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176189024226468687879573089 132141768169851515909679817)
          ·
            refine ⟨99106326127388636932259863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132141768169851515909679817 99106326127388636932259863)
            ·
              refine ⟨148659489191082955398389795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99106326127388636932259863 148659489191082955398389795)
              ·
                refine ⟨222989233786624433097584693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148659489191082955398389795 222989233786624433097584693)
                ·
                  refine ⟨20905240667496040602898565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222989233786624433097584693 20905240667496040602898565)
                  ·
                    refine ⟨3919732625155507613043481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20905240667496040602898565 3919732625155507613043481)
                    ·
                      refine ⟨2939799468866630709782611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919732625155507613043481 2939799468866630709782611)
                      ·
                        rfl

theorem cell23_5725239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 4, 2].length) (baseStart_5725239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725239 prefixEnd_5725239 := by exact prefixLift 5725239
  have htrace : WordTrace (prefixWord ++ tailWord_5725239) baseStart_5725239 baseEnd_5725239 := by
    simpa [prefixWord, tailWord_5725239, baseEnd_5725239] using wordTrace_append hprefix tailTrace_5725239
  have hstable : (prefixWord ++ tailWord_5725239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725239).length < 2 ^ (prefixWord ++ tailWord_5725239).sum := by decide
  have hdescent : baseEnd_5725239 < baseStart_5725239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725242 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_5725242 : Nat := 118140960795 + 5725242 * 2 ^ 59
def prefixEnd_5725242 : Nat := 4983230072969 + 3 ^ 40 * 5725242 * 2
def baseEnd_5725242 : Nat := 2939801009308594198045097

theorem tailTrace_5725242 : CollatzResearch.WordTrace tailWord_5725242 prefixEnd_5725242 2939801009308594198045097 := by
  unfold tailWord_5725242
  simp only [CollatzResearch.WordTrace]
  refine ⟨52204182681108375583148495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139211153816289001555062653 52204182681108375583148495)
  ·
    refine ⟨78306274021662563374722743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52204182681108375583148495 78306274021662563374722743)
    ·
      refine ⟨117459411032493845062084115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78306274021662563374722743 117459411032493845062084115)
      ·
        refine ⟨176189116548740767593126173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117459411032493845062084115 176189116548740767593126173)
        ·
          refine ⟨66070918705777787847422315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176189116548740767593126173 66070918705777787847422315)
          ·
            refine ⟨99106378058666681771133473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66070918705777787847422315 99106378058666681771133473)
            ·
              refine ⟨74329783544000011328350105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99106378058666681771133473 74329783544000011328350105)
              ·
                refine ⟨55747337658000008496262579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74329783544000011328350105 55747337658000008496262579)
                ·
                  refine ⟨83621006487000012744393869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55747337658000008496262579 83621006487000012744393869)
                  ·
                    refine ⟨31357877432625004779147701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83621006487000012744393869 31357877432625004779147701)
                    ·
                      refine ⟨2939801009308594198045097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31357877432625004779147701 2939801009308594198045097)
                      ·
                        rfl

theorem cell23_5725242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_5725242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725242 prefixEnd_5725242 := by exact prefixLift 5725242
  have htrace : WordTrace (prefixWord ++ tailWord_5725242) baseStart_5725242 baseEnd_5725242 := by
    simpa [prefixWord, tailWord_5725242, baseEnd_5725242] using wordTrace_append hprefix tailTrace_5725242
  have hstable : (prefixWord ++ tailWord_5725242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725242).length < 2 ^ (prefixWord ++ tailWord_5725242).sum := by decide
  have hdescent : baseEnd_5725242 < baseStart_5725242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725256 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 1, 4, 2]
def baseStart_5725256 : Nat := 118140960795 + 5725256 * 2 ^ 59
def prefixEnd_5725256 : Nat := 4983230072969 + 3 ^ 40 * 5725256 * 2
def baseEnd_5725256 : Nat := 2939808198037757143270033

theorem tailTrace_5725256 : CollatzResearch.WordTrace tailWord_5725256 prefixEnd_5725256 2939808198037757143270033 := by
  unfold tailWord_5725256
  simp only [CollatzResearch.WordTrace]
  refine ⟨104408620673191391361801811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139211494230921855149069081 104408620673191391361801811)
  ·
    refine ⟨156612931009787087042702717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104408620673191391361801811 156612931009787087042702717)
    ·
      refine ⟨58729849128670157641013519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156612931009787087042702717 58729849128670157641013519)
      ·
        refine ⟨88094773693005236461520279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58729849128670157641013519 88094773693005236461520279)
        ·
          refine ⟨132142160539507854692280419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88094773693005236461520279 132142160539507854692280419)
          ·
            refine ⟨198213240809261782038420629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132142160539507854692280419 198213240809261782038420629)
            ·
              refine ⟨9291245662934146033050967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198213240809261782038420629 9291245662934146033050967)
              ·
                refine ⟨13936868494401219049576451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9291245662934146033050967 13936868494401219049576451)
                ·
                  refine ⟨20905302741601828574364677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13936868494401219049576451 20905302741601828574364677)
                  ·
                    refine ⟨3919744264050342857693377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20905302741601828574364677 3919744264050342857693377)
                    ·
                      refine ⟨2939808198037757143270033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919744264050342857693377 2939808198037757143270033)
                      ·
                        rfl

theorem cell23_5725256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_5725256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725256 prefixEnd_5725256 := by exact prefixLift 5725256
  have htrace : WordTrace (prefixWord ++ tailWord_5725256) baseStart_5725256 baseEnd_5725256 := by
    simpa [prefixWord, tailWord_5725256, baseEnd_5725256] using wordTrace_append hprefix tailTrace_5725256
  have hstable : (prefixWord ++ tailWord_5725256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725256).length < 2 ^ (prefixWord ++ tailWord_5725256).sum := by decide
  have hdescent : baseEnd_5725256 < baseStart_5725256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725289 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 2, 3, 3]
def baseStart_5725289 : Nat := 118140960795 + 5725289 * 2 ^ 59
def prefixEnd_5725289 : Nat := 4983230072969 + 3 ^ 40 * 5725289 * 2
def baseEnd_5725289 : Nat := 2939825142899355514157381

theorem tailTrace_5725289 : CollatzResearch.WordTrace tailWord_5725289 prefixEnd_5725289 2939825142899355514157381 := by
  unfold tailWord_5725289
  simp only [CollatzResearch.WordTrace]
  refine ⟨208818444955263229359554921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139212296636842152906369947 208818444955263229359554921)
  ·
    refine ⟨156613833716447422019666191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208818444955263229359554921 156613833716447422019666191)
    ·
      refine ⟨234920750574671133029499287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156613833716447422019666191 234920750574671133029499287)
      ·
        refine ⟨352381125862006699544248931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234920750574671133029499287 352381125862006699544248931)
        ·
          refine ⟨528571688793010049316373397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352381125862006699544248931 528571688793010049316373397)
          ·
            refine ⟨24776797912172346061705003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 528571688793010049316373397 24776797912172346061705003)
            ·
              refine ⟨37165196868258519092557505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24776797912172346061705003 37165196868258519092557505)
              ·
                refine ⟨27873897651193889319418129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37165196868258519092557505 27873897651193889319418129)
                ·
                  refine ⟨20905423238395416989563597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27873897651193889319418129 20905423238395416989563597)
                  ·
                    refine ⟨7839533714398281371086349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20905423238395416989563597 7839533714398281371086349)
                    ·
                      refine ⟨2939825142899355514157381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7839533714398281371086349 2939825142899355514157381)
                      ·
                        rfl

theorem cell23_5725289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3, 3].length) (baseStart_5725289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725289 prefixEnd_5725289 := by exact prefixLift 5725289
  have htrace : WordTrace (prefixWord ++ tailWord_5725289) baseStart_5725289 baseEnd_5725289 := by
    simpa [prefixWord, tailWord_5725289, baseEnd_5725289] using wordTrace_append hprefix tailTrace_5725289
  have hstable : (prefixWord ++ tailWord_5725289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725289).length < 2 ^ (prefixWord ++ tailWord_5725289).sum := by decide
  have hdescent : baseEnd_5725289 < baseStart_5725289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725290 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_5725290 : Nat := 118140960795 + 5725290 * 2 ^ 59
def prefixEnd_5725290 : Nat := 4983230072969 + 3 ^ 40 * 5725290 * 2
def baseEnd_5725290 : Nat := 2939825656380010010244877

theorem tailTrace_5725290 : CollatzResearch.WordTrace tailWord_5725290 prefixEnd_5725290 2939825656380010010244877 := by
  unfold tailWord_5725290
  simp only [CollatzResearch.WordTrace]
  refine ⟨52204620357064901632585331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139212320952173071020227549 52204620357064901632585331)
  ·
    refine ⟨78306930535597352448877997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52204620357064901632585331 78306930535597352448877997)
    ·
      refine ⟨29365098950849007168329249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78306930535597352448877997 29365098950849007168329249)
      ·
        refine ⟨22023824213136755376246937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29365098950849007168329249 22023824213136755376246937)
        ·
          refine ⟨16517868159852566532185203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22023824213136755376246937 16517868159852566532185203)
          ·
            refine ⟨24776802239778849798277805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16517868159852566532185203 24776802239778849798277805)
            ·
              refine ⟨9291300839917068674354177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24776802239778849798277805 9291300839917068674354177)
              ·
                refine ⟨6968475629937801505765633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9291300839917068674354177 6968475629937801505765633)
                ·
                  refine ⟨5226356722453351129324225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6968475629937801505765633 5226356722453351129324225)
                  ·
                    refine ⟨3919767541840013346993169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5226356722453351129324225 3919767541840013346993169)
                    ·
                      refine ⟨2939825656380010010244877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919767541840013346993169 2939825656380010010244877)
                      ·
                        rfl

theorem cell23_5725290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_5725290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725290 prefixEnd_5725290 := by exact prefixLift 5725290
  have htrace : WordTrace (prefixWord ++ tailWord_5725290) baseStart_5725290 baseEnd_5725290 := by
    simpa [prefixWord, tailWord_5725290, baseEnd_5725290] using wordTrace_append hprefix tailTrace_5725290
  have hstable : (prefixWord ++ tailWord_5725290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725290).length < 2 ^ (prefixWord ++ tailWord_5725290).sum := by decide
  have hdescent : baseEnd_5725290 < baseStart_5725290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725490 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_5725490 : Nat := 118140960795 + 5725490 * 2 ^ 59
def prefixEnd_5725490 : Nat := 4983230072969 + 3 ^ 40 * 5725490 * 2
def baseEnd_5725490 : Nat := 2939928352510909227743957

theorem tailTrace_5725490 : CollatzResearch.WordTrace tailWord_5725490 prefixEnd_5725490 2939928352510909227743957 := by
  unfold tailWord_5725490
  simp only [CollatzResearch.WordTrace]
  refine ⟨52206444006883760171905481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139217184018356693791747949 52206444006883760171905481)
  ·
    refine ⟨39154833005162820128929111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52206444006883760171905481 39154833005162820128929111)
    ·
      refine ⟨58732249507744230193393667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39154833005162820128929111 58732249507744230193393667)
      ·
        refine ⟨88098374261616345290090501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58732249507744230193393667 88098374261616345290090501)
        ·
          refine ⟨16518445174053064741891969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88098374261616345290090501 16518445174053064741891969)
          ·
            refine ⟨12388833880539798556418977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16518445174053064741891969 12388833880539798556418977)
            ·
              refine ⟨9291625410404848917314233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12388833880539798556418977 9291625410404848917314233)
              ·
                refine ⟨6968719057803636687985675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9291625410404848917314233 6968719057803636687985675)
                ·
                  refine ⟨10453078586705455031978513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6968719057803636687985675 10453078586705455031978513)
                  ·
                    refine ⟨7839808940029091273983885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10453078586705455031978513 7839808940029091273983885)
                    ·
                      refine ⟨2939928352510909227743957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7839808940029091273983885 2939928352510909227743957)
                      ·
                        rfl

theorem cell23_5725490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_5725490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725490 prefixEnd_5725490 := by exact prefixLift 5725490
  have htrace : WordTrace (prefixWord ++ tailWord_5725490) baseStart_5725490 baseEnd_5725490 := by
    simpa [prefixWord, tailWord_5725490, baseEnd_5725490] using wordTrace_append hprefix tailTrace_5725490
  have hstable : (prefixWord ++ tailWord_5725490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725490).length < 2 ^ (prefixWord ++ tailWord_5725490).sum := by decide
  have hdescent : baseEnd_5725490 < baseStart_5725490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725493 : List Nat := [1, 3, 3, 1, 2, 4, 2, 7]
def baseStart_5725493 : Nat := 118140960795 + 5725493 * 2 ^ 59
def prefixEnd_5725493 : Nat := 4983230072969 + 3 ^ 40 * 5725493 * 2
def baseEnd_5725493 : Nat := 108886292331587878370609

theorem tailTrace_5725493 : CollatzResearch.WordTrace tailWord_5725493 prefixEnd_5725493 108886292331587878370609 := by
  unfold tailWord_5725493
  simp only [CollatzResearch.WordTrace]
  refine ⟨208825885446524172199981133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139217256964349448133320755 208825885446524172199981133)
  ·
    refine ⟨78309707042446564574992925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208825885446524172199981133 78309707042446564574992925)
    ·
      refine ⟨29366140140917461715622347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78309707042446564574992925 29366140140917461715622347)
      ·
        refine ⟨44049210211376192573433521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29366140140917461715622347 44049210211376192573433521)
        ·
          refine ⟨33036907658532144430075141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44049210211376192573433521 33036907658532144430075141)
          ·
            refine ⟨6194420185974777080639089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33036907658532144430075141 6194420185974777080639089)
            ·
              refine ⟨4645815139481082810479317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6194420185974777080639089 4645815139481082810479317)
              ·
                refine ⟨108886292331587878370609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4645815139481082810479317 108886292331587878370609)
                ·
                  rfl

theorem cell23_5725493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 7].length) (baseStart_5725493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725493 prefixEnd_5725493 := by exact prefixLift 5725493
  have htrace : WordTrace (prefixWord ++ tailWord_5725493) baseStart_5725493 baseEnd_5725493 := by
    simpa [prefixWord, tailWord_5725493, baseEnd_5725493] using wordTrace_append hprefix tailTrace_5725493
  have hstable : (prefixWord ++ tailWord_5725493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725493).length < 2 ^ (prefixWord ++ tailWord_5725493).sum := by decide
  have hdescent : baseEnd_5725493 < baseStart_5725493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725503 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 4, 1, 3]
def baseStart_5725503 : Nat := 118140960795 + 5725503 * 2 ^ 59
def prefixEnd_5725503 : Nat := 4983230072969 + 3 ^ 40 * 5725503 * 2
def baseEnd_5725503 : Nat := 2939935027759417676881397

theorem tailTrace_5725503 : CollatzResearch.WordTrace tailWord_5725503 prefixEnd_5725503 2939935027759417676881397 := by
  unfold tailWord_5725503
  simp only [CollatzResearch.WordTrace]
  refine ⟨208826250176487943907845163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139217500117658629271896775 208826250176487943907845163)
  ·
    refine ⟨313239375264731915861767745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208826250176487943907845163 313239375264731915861767745)
    ·
      refine ⟨234929531448548936896325809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313239375264731915861767745 234929531448548936896325809)
      ·
        refine ⟨176197148586411702672244357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234929531448548936896325809 176197148586411702672244357)
        ·
          refine ⟨33036965359952194251045817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176197148586411702672244357 33036965359952194251045817)
          ·
            refine ⟨24777724019964145688284363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33036965359952194251045817 24777724019964145688284363)
            ·
              refine ⟨37166586029946218532426545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24777724019964145688284363 37166586029946218532426545)
              ·
                refine ⟨27874939522459663899319909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37166586029946218532426545 27874939522459663899319909)
                ·
                  refine ⟨5226551160461186981122483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27874939522459663899319909 5226551160461186981122483)
                  ·
                    refine ⟨7839826740691780471683725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5226551160461186981122483 7839826740691780471683725)
                    ·
                      refine ⟨2939935027759417676881397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7839826740691780471683725 2939935027759417676881397)
                      ·
                        rfl

theorem cell23_5725503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_5725503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725503 prefixEnd_5725503 := by exact prefixLift 5725503
  have htrace : WordTrace (prefixWord ++ tailWord_5725503) baseStart_5725503 baseEnd_5725503 := by
    simpa [prefixWord, tailWord_5725503, baseEnd_5725503] using wordTrace_append hprefix tailTrace_5725503
  have hstable : (prefixWord ++ tailWord_5725503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725503).length < 2 ^ (prefixWord ++ tailWord_5725503).sum := by decide
  have hdescent : baseEnd_5725503 < baseStart_5725503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725509 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_5725509 : Nat := 118140960795 + 5725509 * 2 ^ 59
def prefixEnd_5725509 : Nat := 4983230072969 + 3 ^ 40 * 5725509 * 2
def baseEnd_5725509 : Nat := 2939938108643344653406369

theorem tailTrace_5725509 : CollatzResearch.WordTrace tailWord_5725509 prefixEnd_5725509 2939938108643344653406369 := by
  unfold tailWord_5725509
  simp only [CollatzResearch.WordTrace]
  refine ⟨208826469014466206932563581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139217646009644137955042387 208826469014466206932563581)
  ·
    refine ⟨78309925880424827599711343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208826469014466206932563581 78309925880424827599711343)
    ·
      refine ⟨117464888820637241399567015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78309925880424827599711343 117464888820637241399567015)
      ·
        refine ⟨176197333230955862099350523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117464888820637241399567015 176197333230955862099350523)
        ·
          refine ⟨264295999846433793149025785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176197333230955862099350523 264295999846433793149025785)
          ·
            refine ⟨198221999884825344861769339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264295999846433793149025785 198221999884825344861769339)
            ·
              refine ⟨297332999827238017292654009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198221999884825344861769339 297332999827238017292654009)
              ·
                refine ⟨222999749870428512969490507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297332999827238017292654009 222999749870428512969490507)
                ·
                  refine ⟨334499624805642769454235761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222999749870428512969490507 334499624805642769454235761)
                  ·
                    refine ⟨250874718604232077090676821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 334499624805642769454235761 250874718604232077090676821)
                    ·
                      refine ⟨2939938108643344653406369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 250874718604232077090676821 2939938108643344653406369)
                      ·
                        rfl

theorem cell23_5725509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_5725509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725509 prefixEnd_5725509 := by exact prefixLift 5725509
  have htrace : WordTrace (prefixWord ++ tailWord_5725509) baseStart_5725509 baseEnd_5725509 := by
    simpa [prefixWord, tailWord_5725509, baseEnd_5725509] using wordTrace_append hprefix tailTrace_5725509
  have hstable : (prefixWord ++ tailWord_5725509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725509).length < 2 ^ (prefixWord ++ tailWord_5725509).sum := by decide
  have hdescent : baseEnd_5725509 < baseStart_5725509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725593 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 2, 3, 3]
def baseStart_5725593 : Nat := 118140960795 + 5725593 * 2 ^ 59
def prefixEnd_5725593 : Nat := 4983230072969 + 3 ^ 40 * 5725593 * 2
def baseEnd_5725593 : Nat := 2939981241018322324755983

theorem tailTrace_5725593 : CollatzResearch.WordTrace tailWord_5725593 prefixEnd_5725593 2939981241018322324755983 := by
  unfold tailWord_5725593
  simp only [CollatzResearch.WordTrace]
  refine ⟨208829532746161889278621433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139219688497441259519080955 208829532746161889278621433)
  ·
    refine ⟨156622149559621416958966075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208829532746161889278621433 156622149559621416958966075)
    ·
      refine ⟨234933224339432125438449113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156622149559621416958966075 234933224339432125438449113)
      ·
        refine ⟨176199918254574094078836835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234933224339432125438449113 176199918254574094078836835)
        ·
          refine ⟨264299877381861141118255253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176199918254574094078836835 264299877381861141118255253)
          ·
            refine ⟨12389056752274740989918215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 264299877381861141118255253 12389056752274740989918215)
            ·
              refine ⟨18583585128412111484877323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12389056752274740989918215 18583585128412111484877323)
              ·
                refine ⟨27875377692618167227315985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18583585128412111484877323 27875377692618167227315985)
                ·
                  refine ⟨20906533269463625420486989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27875377692618167227315985 20906533269463625420486989)
                  ·
                    refine ⟨7839949976048859532682621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20906533269463625420486989 7839949976048859532682621)
                    ·
                      refine ⟨2939981241018322324755983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7839949976048859532682621 2939981241018322324755983)
                      ·
                        rfl

theorem cell23_5725593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_5725593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725593 prefixEnd_5725593 := by exact prefixLift 5725593
  have htrace : WordTrace (prefixWord ++ tailWord_5725593) baseStart_5725593 baseEnd_5725593 := by
    simpa [prefixWord, tailWord_5725593, baseEnd_5725593] using wordTrace_append hprefix tailTrace_5725593
  have hstable : (prefixWord ++ tailWord_5725593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725593).length < 2 ^ (prefixWord ++ tailWord_5725593).sum := by decide
  have hdescent : baseEnd_5725593 < baseStart_5725593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725603 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 2, 5, 2]
def baseStart_5725603 : Nat := 118140960795 + 5725603 * 2 ^ 59
def prefixEnd_5725603 : Nat := 4983230072969 + 3 ^ 40 * 5725603 * 2
def baseEnd_5725603 : Nat := 2939986375824867285630937

theorem tailTrace_5725603 : CollatzResearch.WordTrace tailWord_5725603 prefixEnd_5725603 2939986375824867285630937 := by
  unfold tailWord_5725603
  simp only [CollatzResearch.WordTrace]
  refine ⟨208829897476125660986485463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139219931650750440657656975 208829897476125660986485463)
  ·
    refine ⟨313244846214188491479728195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208829897476125660986485463 313244846214188491479728195)
    ·
      refine ⟨469867269321282737219592293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313244846214188491479728195 469867269321282737219592293)
      ·
        refine ⟨88100112997740513228673555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 469867269321282737219592293 88100112997740513228673555)
        ·
          refine ⟨132150169496610769843010333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88100112997740513228673555 132150169496610769843010333)
          ·
            refine ⟨49556313561229038691128875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132150169496610769843010333 49556313561229038691128875)
            ·
              refine ⟨74334470341843558036693313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49556313561229038691128875 74334470341843558036693313)
              ·
                refine ⟨55750852756382668527519985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74334470341843558036693313 55750852756382668527519985)
                ·
                  refine ⟨41813139567287001395639989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55750852756382668527519985 41813139567287001395639989)
                  ·
                    refine ⟨3919981834433156380841249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41813139567287001395639989 3919981834433156380841249)
                    ·
                      refine ⟨2939986375824867285630937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3919981834433156380841249 2939986375824867285630937)
                      ·
                        rfl

theorem cell23_5725603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_5725603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725603 prefixEnd_5725603 := by exact prefixLift 5725603
  have htrace : WordTrace (prefixWord ++ tailWord_5725603) baseStart_5725603 baseEnd_5725603 := by
    simpa [prefixWord, tailWord_5725603, baseEnd_5725603] using wordTrace_append hprefix tailTrace_5725603
  have hstable : (prefixWord ++ tailWord_5725603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725603).length < 2 ^ (prefixWord ++ tailWord_5725603).sum := by decide
  have hdescent : baseEnd_5725603 < baseStart_5725603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725643 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 3, 4]
def baseStart_5725643 : Nat := 118140960795 + 5725643 * 2 ^ 59
def prefixEnd_5725643 : Nat := 4983230072969 + 3 ^ 40 * 5725643 * 2
def baseEnd_5725643 : Nat := 980002305017015709710251

theorem tailTrace_5725643 : CollatzResearch.WordTrace tailWord_5725643 prefixEnd_5725643 980002305017015709710251 := by
  unfold tailWord_5725643
  simp only [CollatzResearch.WordTrace]
  refine ⟨208831356395980747817941583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139220904263987165211961055 208831356395980747817941583)
  ·
    refine ⟨313247034593971121726912375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208831356395980747817941583 313247034593971121726912375)
    ·
      refine ⟨469870551890956682590368563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313247034593971121726912375 469870551890956682590368563)
      ·
        refine ⟨704805827836435023885552845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469870551890956682590368563 704805827836435023885552845)
        ·
          refine ⟨264302185438663133957082317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 704805827836435023885552845 264302185438663133957082317)
          ·
            refine ⟨99113319539498675233905869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264302185438663133957082317 99113319539498675233905869)
            ·
              refine ⟨37167494827312003212714701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99113319539498675233905869 37167494827312003212714701)
              ·
                refine ⟨13937810560242001204768013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37167494827312003212714701 13937810560242001204768013)
                ·
                  refine ⟨5226678960090750451788005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13937810560242001204768013 5226678960090750451788005)
                  ·
                    refine ⟨980002305017015709710251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5226678960090750451788005 980002305017015709710251)
                    ·
                      rfl

theorem cell23_5725643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 4].length) (baseStart_5725643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725643 prefixEnd_5725643 := by exact prefixLift 5725643
  have htrace : WordTrace (prefixWord ++ tailWord_5725643) baseStart_5725643 baseEnd_5725643 := by
    simpa [prefixWord, tailWord_5725643, baseEnd_5725643] using wordTrace_append hprefix tailTrace_5725643
  have hstable : (prefixWord ++ tailWord_5725643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725643).length < 2 ^ (prefixWord ++ tailWord_5725643).sum := by decide
  have hdescent : baseEnd_5725643 < baseStart_5725643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725653 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_5725653 : Nat := 118140960795 + 5725653 * 2 ^ 59
def prefixEnd_5725653 : Nat := 4983230072969 + 3 ^ 40 * 5725653 * 2
def baseEnd_5725653 : Nat := 2940012049857592090005707

theorem tailTrace_5725653 : CollatzResearch.WordTrace tailWord_5725653 prefixEnd_5725653 2940012049857592090005707 := by
  unfold tailWord_5725653
  simp only [CollatzResearch.WordTrace]
  refine ⟨208831721125944519525805613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139221147417296346350537075 208831721125944519525805613)
  ·
    refine ⟨78311895422229194822177105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208831721125944519525805613 78311895422229194822177105)
    ·
      refine ⟨58733921566671896116632829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78311895422229194822177105 58733921566671896116632829)
      ·
        refine ⟨22025220587501961043737311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58733921566671896116632829 22025220587501961043737311)
        ·
          refine ⟨33037830881252941565605967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22025220587501961043737311 33037830881252941565605967)
          ·
            refine ⟨49556746321879412348408951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33037830881252941565605967 49556746321879412348408951)
            ·
              refine ⟨74335119482819118522613427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49556746321879412348408951 74335119482819118522613427)
              ·
                refine ⟨111502679224228677783920141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74335119482819118522613427 111502679224228677783920141)
                ·
                  refine ⟨41813504709085754168970053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111502679224228677783920141 41813504709085754168970053)
                  ·
                    refine ⟨7840032132953578906681885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41813504709085754168970053 7840032132953578906681885)
                    ·
                      refine ⟨2940012049857592090005707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7840032132953578906681885 2940012049857592090005707)
                      ·
                        rfl

theorem cell23_5725653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_5725653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725653 prefixEnd_5725653 := by exact prefixLift 5725653
  have htrace : WordTrace (prefixWord ++ tailWord_5725653) baseStart_5725653 baseEnd_5725653 := by
    simpa [prefixWord, tailWord_5725653, baseEnd_5725653] using wordTrace_append hprefix tailTrace_5725653
  have hstable : (prefixWord ++ tailWord_5725653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725653).length < 2 ^ (prefixWord ++ tailWord_5725653).sum := by decide
  have hdescent : baseEnd_5725653 < baseStart_5725653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725676 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_5725676 : Nat := 118140960795 + 5725676 * 2 ^ 59
def prefixEnd_5725676 : Nat := 4983230072969 + 3 ^ 40 * 5725676 * 2
def baseEnd_5725676 : Nat := 2940023859912645500018101

theorem tailTrace_5725676 : CollatzResearch.WordTrace tailWord_5725676 prefixEnd_5725676 2940023859912645500018101 := by
  unfold tailWord_5725676
  simp only [CollatzResearch.WordTrace]
  refine ⟨104416280002430597226946441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139221706669907462969261921 104416280002430597226946441)
  ·
    refine ⟨78312210001822947920209831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104416280002430597226946441 78312210001822947920209831)
    ·
      refine ⟨117468315002734421880314747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78312210001822947920209831 117468315002734421880314747)
      ·
        refine ⟨176202472504101632820472121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117468315002734421880314747 176202472504101632820472121)
        ·
          refine ⟨132151854378076224615354091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176202472504101632820472121 132151854378076224615354091)
          ·
            refine ⟨198227781567114336923031137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132151854378076224615354091 198227781567114336923031137)
            ·
              refine ⟨148670836175335752692273353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198227781567114336923031137 148670836175335752692273353)
              ·
                refine ⟨111503127131501814519205015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148670836175335752692273353 111503127131501814519205015)
                ·
                  refine ⟨167254690697252721778807523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111503127131501814519205015 167254690697252721778807523)
                  ·
                    refine ⟨250882036045879082668211285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167254690697252721778807523 250882036045879082668211285)
                    ·
                      refine ⟨2940023859912645500018101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 250882036045879082668211285 2940023859912645500018101)
                      ·
                        rfl

theorem cell23_5725676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_5725676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725676 prefixEnd_5725676 := by exact prefixLift 5725676
  have htrace : WordTrace (prefixWord ++ tailWord_5725676) baseStart_5725676 baseEnd_5725676 := by
    simpa [prefixWord, tailWord_5725676, baseEnd_5725676] using wordTrace_append hprefix tailTrace_5725676
  have hstable : (prefixWord ++ tailWord_5725676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725676).length < 2 ^ (prefixWord ++ tailWord_5725676).sum := by decide
  have hdescent : baseEnd_5725676 < baseStart_5725676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725707 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 6]
def baseStart_5725707 : Nat := 118140960795 + 5725707 * 2 ^ 59
def prefixEnd_5725707 : Nat := 4983230072969 + 3 ^ 40 * 5725707 * 2
def baseEnd_5725707 : Nat := 326671086423659430970051

theorem tailTrace_5725707 : CollatzResearch.WordTrace tailWord_5725707 prefixEnd_5725707 326671086423659430970051 := by
  unfold tailWord_5725707
  simp only [CollatzResearch.WordTrace]
  refine ⟨208833690667748886748271375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139222460445165924498847583 208833690667748886748271375)
  ·
    refine ⟨313250536001623330122407063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208833690667748886748271375 313250536001623330122407063)
    ·
      refine ⟨469875804002434995183610595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313250536001623330122407063 469875804002434995183610595)
      ·
        refine ⟨704813706003652492775415893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469875804002434995183610595 704813706003652492775415893)
        ·
          refine ⟨8259535617230302649711905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 704813706003652492775415893 8259535617230302649711905)
          ·
            refine ⟨6194651712922726987283929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8259535617230302649711905 6194651712922726987283929)
            ·
              refine ⟨4645988784692045240462947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6194651712922726987283929 4645988784692045240462947)
              ·
                refine ⟨6968983177038067860694421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4645988784692045240462947 6968983177038067860694421)
                ·
                  refine ⟨326671086423659430970051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6968983177038067860694421 326671086423659430970051)
                  ·
                    rfl

theorem cell23_5725707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 6].length) (baseStart_5725707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725707 prefixEnd_5725707 := by exact prefixLift 5725707
  have htrace : WordTrace (prefixWord ++ tailWord_5725707) baseStart_5725707 baseEnd_5725707 := by
    simpa [prefixWord, tailWord_5725707, baseEnd_5725707] using wordTrace_append hprefix tailTrace_5725707
  have hstable : (prefixWord ++ tailWord_5725707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725707).length < 2 ^ (prefixWord ++ tailWord_5725707).sum := by decide
  have hdescent : baseEnd_5725707 < baseStart_5725707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725720 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 3, 5]
def baseStart_5725720 : Nat := 118140960795 + 5725720 * 2 ^ 59
def prefixEnd_5725720 : Nat := 4983230072969 + 3 ^ 40 * 5725720 * 2
def baseEnd_5725720 : Nat := 980015484353814442622633

theorem tailTrace_5725720 : CollatzResearch.WordTrace tailWord_5725720 prefixEnd_5725720 980015484353814442622633 := by
  unfold tailWord_5725720
  simp only [CollatzResearch.WordTrace]
  refine ⟨104417082408350894984247307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139222776544467859978996409 104417082408350894984247307)
  ·
    refine ⟨156625623612526342476370961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104417082408350894984247307 156625623612526342476370961)
    ·
      refine ⟨117469217709394756857278221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156625623612526342476370961 117469217709394756857278221)
      ·
        refine ⟨44050956641023033821479333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117469217709394756857278221 44050956641023033821479333)
        ·
          refine ⟨8259554370191818841527375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44050956641023033821479333 8259554370191818841527375)
          ·
            refine ⟨12389331555287728262291063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8259554370191818841527375 12389331555287728262291063)
            ·
              refine ⟨18583997332931592393436595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12389331555287728262291063 18583997332931592393436595)
              ·
                refine ⟨27875995999397388590154893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18583997332931592393436595 27875995999397388590154893)
                ·
                  refine ⟨10453498499774020721308085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27875995999397388590154893 10453498499774020721308085)
                  ·
                    refine ⟨980015484353814442622633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10453498499774020721308085 980015484353814442622633)
                    ·
                      rfl

theorem cell23_5725720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_5725720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725720 prefixEnd_5725720 := by exact prefixLift 5725720
  have htrace : WordTrace (prefixWord ++ tailWord_5725720) baseStart_5725720 baseEnd_5725720 := by
    simpa [prefixWord, tailWord_5725720, baseEnd_5725720] using wordTrace_append hprefix tailTrace_5725720
  have hstable : (prefixWord ++ tailWord_5725720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725720).length < 2 ^ (prefixWord ++ tailWord_5725720).sum := by decide
  have hdescent : baseEnd_5725720 < baseStart_5725720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725751 : List Nat := [1, 1, 3, 1, 2, 6, 2, 2, 1, 1, 3]
def baseStart_5725751 : Nat := 118140960795 + 5725751 * 2 ^ 59
def prefixEnd_5725751 : Nat := 4983230072969 + 3 ^ 40 * 5725751 * 2
def baseEnd_5725751 : Nat := 2940062370961732706580257

theorem tailTrace_5725751 : CollatzResearch.WordTrace tailWord_5725751 prefixEnd_5725751 2940062370961732706580257 := by
  unfold tailWord_5725751
  simp only [CollatzResearch.WordTrace]
  refine ⟨208835295479589482262873107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139223530319726321508582071 208835295479589482262873107)
  ·
    refine ⟨313252943219384223394309661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208835295479589482262873107 313252943219384223394309661)
    ·
      refine ⟨117469853707269083772866123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313252943219384223394309661 117469853707269083772866123)
      ·
        refine ⟨176204780560903625659299185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117469853707269083772866123 176204780560903625659299185)
        ·
          refine ⟨132153585420677719244474389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176204780560903625659299185 132153585420677719244474389)
          ·
            refine ⟨6194699316594268089584737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132153585420677719244474389 6194699316594268089584737)
            ·
              refine ⟨4646024487445701067188553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6194699316594268089584737 4646024487445701067188553)
              ·
                refine ⟨3484518365584275800391415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4646024487445701067188553 3484518365584275800391415)
                ·
                  refine ⟨5226777548376413700587123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3484518365584275800391415 5226777548376413700587123)
                  ·
                    refine ⟨7840166322564620550880685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5226777548376413700587123 7840166322564620550880685)
                    ·
                      refine ⟨2940062370961732706580257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7840166322564620550880685 2940062370961732706580257)
                      ·
                        rfl

theorem cell23_5725751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 1, 1, 3].length) (baseStart_5725751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725751 prefixEnd_5725751 := by exact prefixLift 5725751
  have htrace : WordTrace (prefixWord ++ tailWord_5725751) baseStart_5725751 baseEnd_5725751 := by
    simpa [prefixWord, tailWord_5725751, baseEnd_5725751] using wordTrace_append hprefix tailTrace_5725751
  have hstable : (prefixWord ++ tailWord_5725751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725751).length < 2 ^ (prefixWord ++ tailWord_5725751).sum := by decide
  have hdescent : baseEnd_5725751 < baseStart_5725751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725770 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_5725770 : Nat := 118140960795 + 5725770 * 2 ^ 59
def prefixEnd_5725770 : Nat := 4983230072969 + 3 ^ 40 * 5725770 * 2
def baseEnd_5725770 : Nat := 2940072127094168132242669

theorem tailTrace_5725770 : CollatzResearch.WordTrace tailWord_5725770 prefixEnd_5725770 2940072127094168132242669 := by
  unfold tailWord_5725770
  simp only [CollatzResearch.WordTrace]
  refine ⟨52208997116630162126953691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139223992311013765671876509 52208997116630162126953691)
  ·
    refine ⟨78313495674945243190430537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52208997116630162126953691 78313495674945243190430537)
    ·
      refine ⟨58735121756208932392822903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78313495674945243190430537 58735121756208932392822903)
      ·
        refine ⟨88102682634313398589234355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58735121756208932392822903 88102682634313398589234355)
        ·
          refine ⟨132154023951470097883851533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88102682634313398589234355 132154023951470097883851533)
          ·
            refine ⟨49557758981801286706444325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132154023951470097883851533 49557758981801286706444325)
            ·
              refine ⟨9292079809087741257458311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49557758981801286706444325 9292079809087741257458311)
              ·
                refine ⟨13938119713631611886187467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9292079809087741257458311 13938119713631611886187467)
                ·
                  refine ⟨20907179570447417829281201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13938119713631611886187467 20907179570447417829281201)
                  ·
                    refine ⟨15680384677835563371960901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20907179570447417829281201 15680384677835563371960901)
                    ·
                      refine ⟨2940072127094168132242669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15680384677835563371960901 2940072127094168132242669)
                      ·
                        rfl

theorem cell23_5725770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_5725770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725770 prefixEnd_5725770 := by exact prefixLift 5725770
  have htrace : WordTrace (prefixWord ++ tailWord_5725770) baseStart_5725770 baseEnd_5725770 := by
    simpa [prefixWord, tailWord_5725770, baseEnd_5725770] using wordTrace_append hprefix tailTrace_5725770
  have hstable : (prefixWord ++ tailWord_5725770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725770).length < 2 ^ (prefixWord ++ tailWord_5725770).sum := by decide
  have hdescent : baseEnd_5725770 < baseStart_5725770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725780 : List Nat := [2, 4, 1, 1, 1, 2, 5, 7]
def baseStart_5725780 : Nat := 118140960795 + 5725780 * 2 ^ 59
def prefixEnd_5725780 : Nat := 4983230072969 + 3 ^ 40 * 5725780 * 2
def baseEnd_5725780 : Nat := 108891750440767151596949

theorem tailTrace_5725780 : CollatzResearch.WordTrace tailWord_5725780 prefixEnd_5725780 108891750440767151596949 := by
  unfold tailWord_5725780
  simp only [CollatzResearch.WordTrace]
  refine ⟨104418176598242210107839397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139224235464322946810452529 104418176598242210107839397)
  ·
    refine ⟨19578408112170414395219887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104418176598242210107839397 19578408112170414395219887)
    ·
      refine ⟨29367612168255621592829831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19578408112170414395219887 29367612168255621592829831)
      ·
        refine ⟨44051418252383432389244747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29367612168255621592829831 44051418252383432389244747)
        ·
          refine ⟨66077127378575148583867121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44051418252383432389244747 66077127378575148583867121)
          ·
            refine ⟨49557845533931361437900341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66077127378575148583867121 49557845533931361437900341)
            ·
              refine ⟨4646048018806065134803157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49557845533931361437900341 4646048018806065134803157)
              ·
                refine ⟨108891750440767151596949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4646048018806065134803157 108891750440767151596949)
                ·
                  rfl

theorem cell23_5725780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 7].length) (baseStart_5725780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725780 prefixEnd_5725780 := by exact prefixLift 5725780
  have htrace : WordTrace (prefixWord ++ tailWord_5725780) baseStart_5725780 baseEnd_5725780 := by
    simpa [prefixWord, tailWord_5725780, baseEnd_5725780] using wordTrace_append hprefix tailTrace_5725780
  have hstable : (prefixWord ++ tailWord_5725780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725780).length < 2 ^ (prefixWord ++ tailWord_5725780).sum := by decide
  have hdescent : baseEnd_5725780 < baseStart_5725780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725824 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 2, 1, 3]
def baseStart_5725824 : Nat := 118140960795 + 5725824 * 2 ^ 59
def prefixEnd_5725824 : Nat := 4983230072969 + 3 ^ 40 * 5725824 * 2
def baseEnd_5725824 : Nat := 2940099855049510920967421

theorem tailTrace_5725824 : CollatzResearch.WordTrace tailWord_5725824 prefixEnd_5725824 2940099855049510920967421 := by
  unfold tailWord_5725824
  simp only [CollatzResearch.WordTrace]
  refine ⟨104418979004162507865140263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139225305338883343820187017 104418979004162507865140263)
  ·
    refine ⟨156628468506243761797710395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104418979004162507865140263 156628468506243761797710395)
    ·
      refine ⟨234942702759365642696565593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156628468506243761797710395 234942702759365642696565593)
      ·
        refine ⟨176207027069524232022424195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234942702759365642696565593 176207027069524232022424195)
        ·
          refine ⟨264310540604286348033636293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176207027069524232022424195 264310540604286348033636293)
          ·
            refine ⟨49558226363303690256306805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264310540604286348033636293 49558226363303690256306805)
            ·
              refine ⟨4646083721559720961528763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49558226363303690256306805 4646083721559720961528763)
              ·
                refine ⟨6969125582339581442293145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4646083721559720961528763 6969125582339581442293145)
                ·
                  refine ⟨5226844186754686081719859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6969125582339581442293145 5226844186754686081719859)
                  ·
                    refine ⟨7840266280132029122579789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5226844186754686081719859 7840266280132029122579789)
                    ·
                      refine ⟨2940099855049510920967421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7840266280132029122579789 2940099855049510920967421)
                      ·
                        rfl

theorem cell23_5725824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 2, 1, 3].length) (baseStart_5725824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725824 prefixEnd_5725824 := by exact prefixLift 5725824
  have htrace : WordTrace (prefixWord ++ tailWord_5725824) baseStart_5725824 baseEnd_5725824 := by
    simpa [prefixWord, tailWord_5725824, baseEnd_5725824] using wordTrace_append hprefix tailTrace_5725824
  have hstable : (prefixWord ++ tailWord_5725824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725824).length < 2 ^ (prefixWord ++ tailWord_5725824).sum := by decide
  have hdescent : baseEnd_5725824 < baseStart_5725824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725834 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2]
def baseStart_5725834 : Nat := 118140960795 + 5725834 * 2 ^ 59
def prefixEnd_5725834 : Nat := 4983230072969 + 3 ^ 40 * 5725834 * 2
def baseEnd_5725834 : Nat := 2940104989856055881842375

theorem tailTrace_5725834 : CollatzResearch.WordTrace tailWord_5725834 prefixEnd_5725834 2940104989856055881842375 := by
  unfold tailWord_5725834
  simp only [CollatzResearch.WordTrace]
  refine ⟨52209580684572196859536139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139225548492192524958763037 52209580684572196859536139)
  ·
    refine ⟨78314371026858295289304209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52209580684572196859536139 78314371026858295289304209)
    ·
      refine ⟨58735778270143721466978157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78314371026858295289304209 58735778270143721466978157)
      ·
        refine ⟨22025916851303895550116809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58735778270143721466978157 22025916851303895550116809)
        ·
          refine ⟨16519437638477921662587607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22025916851303895550116809 16519437638477921662587607)
          ·
            refine ⟨24779156457716882493881411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16519437638477921662587607 24779156457716882493881411)
            ·
              refine ⟨37168734686575323740822117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24779156457716882493881411 37168734686575323740822117)
              ·
                refine ⟨6969137753732873201404147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37168734686575323740822117 6969137753732873201404147)
                ·
                  refine ⟨10453706630599309802106221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6969137753732873201404147 10453706630599309802106221)
                  ·
                    refine ⟨3920139986474741175789833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10453706630599309802106221 3920139986474741175789833)
                    ·
                      refine ⟨2940104989856055881842375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920139986474741175789833 2940104989856055881842375)
                      ·
                        rfl

theorem cell23_5725834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_5725834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725834 prefixEnd_5725834 := by exact prefixLift 5725834
  have htrace : WordTrace (prefixWord ++ tailWord_5725834) baseStart_5725834 baseEnd_5725834 := by
    simpa [prefixWord, tailWord_5725834, baseEnd_5725834] using wordTrace_append hprefix tailTrace_5725834
  have hstable : (prefixWord ++ tailWord_5725834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725834).length < 2 ^ (prefixWord ++ tailWord_5725834).sum := by decide
  have hdescent : baseEnd_5725834 < baseStart_5725834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725880 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 2, 3, 3]
def baseStart_5725880 : Nat := 118140960795 + 5725880 * 2 ^ 59
def prefixEnd_5725880 : Nat := 4983230072969 + 3 ^ 40 * 5725880 * 2
def baseEnd_5725880 : Nat := 2940128609966162701867163

theorem tailTrace_5725880 : CollatzResearch.WordTrace tailWord_5725880 prefixEnd_5725880 2940128609966162701867163 := by
  unfold tailWord_5725880
  simp only [CollatzResearch.WordTrace]
  refine ⟨104420000248061068647159547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139226666997414758196212729 104420000248061068647159547)
  ·
    refine ⟨156630000372091602970739321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104420000248061068647159547 156630000372091602970739321)
    ·
      refine ⟨117472500279068702228054491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156630000372091602970739321 117472500279068702228054491)
      ·
        refine ⟨176208750418603053342081737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117472500279068702228054491 176208750418603053342081737)
        ·
          refine ⟨132156562813952290006561303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176208750418603053342081737 132156562813952290006561303)
          ·
            refine ⟨198234844220928435009841955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132156562813952290006561303 198234844220928435009841955)
            ·
              refine ⟨297352266331392652514762933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198234844220928435009841955 297352266331392652514762933)
              ·
                refine ⟨27876774968568061173259025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 297352266331392652514762933 27876774968568061173259025)
                ·
                  refine ⟨20907581226426045879944269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27876774968568061173259025 20907581226426045879944269)
                  ·
                    refine ⟨7840342959909767204979101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20907581226426045879944269 7840342959909767204979101)
                    ·
                      refine ⟨2940128609966162701867163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7840342959909767204979101 2940128609966162701867163)
                      ·
                        rfl

theorem cell23_5725880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_5725880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725880 prefixEnd_5725880 := by exact prefixLift 5725880
  have htrace : WordTrace (prefixWord ++ tailWord_5725880) baseStart_5725880 baseEnd_5725880 := by
    simpa [prefixWord, tailWord_5725880, baseEnd_5725880] using wordTrace_append hprefix tailTrace_5725880
  have hstable : (prefixWord ++ tailWord_5725880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725880).length < 2 ^ (prefixWord ++ tailWord_5725880).sum := by decide
  have hdescent : baseEnd_5725880 < baseStart_5725880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725881 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 2, 2, 2]
def baseStart_5725881 : Nat := 118140960795 + 5725881 * 2 ^ 59
def prefixEnd_5725881 : Nat := 4983230072969 + 3 ^ 40 * 5725881 * 2
def baseEnd_5725881 : Nat := 2940129123446817197954659

theorem tailTrace_5725881 : CollatzResearch.WordTrace tailWord_5725881 prefixEnd_5725881 2940129123446817197954659 := by
  unfold tailWord_5725881
  simp only [CollatzResearch.WordTrace]
  refine ⟨208840036969118514465105497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139226691312745676310070331 208840036969118514465105497)
  ·
    refine ⟨156630027726838885848829123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208840036969118514465105497 156630027726838885848829123)
    ·
      refine ⟨234945041590258328773243685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156630027726838885848829123 234945041590258328773243685)
      ·
        refine ⟨44052195298173436644983191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234945041590258328773243685 44052195298173436644983191)
        ·
          refine ⟨66078292947260154967474787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44052195298173436644983191 66078292947260154967474787)
          ·
            refine ⟨99117439420890232451212181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66078292947260154967474787 99117439420890232451212181)
            ·
              refine ⟨4646129972854229646150571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99117439420890232451212181 4646129972854229646150571)
              ·
                refine ⟨6969194959281344469225857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4646129972854229646150571 6969194959281344469225857)
                ·
                  refine ⟨5226896219461008351919393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6969194959281344469225857 5226896219461008351919393)
                  ·
                    refine ⟨3920172164595756263939545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5226896219461008351919393 3920172164595756263939545)
                    ·
                      refine ⟨2940129123446817197954659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920172164595756263939545 2940129123446817197954659)
                      ·
                        rfl

theorem cell23_5725881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_5725881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725881 prefixEnd_5725881 := by exact prefixLift 5725881
  have htrace : WordTrace (prefixWord ++ tailWord_5725881) baseStart_5725881 baseEnd_5725881 := by
    simpa [prefixWord, tailWord_5725881, baseEnd_5725881] using wordTrace_append hprefix tailTrace_5725881
  have hstable : (prefixWord ++ tailWord_5725881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725881).length < 2 ^ (prefixWord ++ tailWord_5725881).sum := by decide
  have hdescent : baseEnd_5725881 < baseStart_5725881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725883 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 3, 7]
def baseStart_5725883 : Nat := 118140960795 + 5725883 * 2 ^ 59
def prefixEnd_5725883 : Nat := 4983230072969 + 3 ^ 40 * 5725883 * 2
def baseEnd_5725883 : Nat := 980043383469375396709883

theorem tailTrace_5725883 : CollatzResearch.WordTrace tailWord_5725883 prefixEnd_5725883 980043383469375396709883 := by
  unfold tailWord_5725883
  simp only [CollatzResearch.WordTrace]
  refine ⟨208840109915111268806678303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139226739943407512537785535 208840109915111268806678303)
  ·
    refine ⟨313260164872666903210017455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208840109915111268806678303 313260164872666903210017455)
    ·
      refine ⟨469890247309000354815026183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313260164872666903210017455 469890247309000354815026183)
      ·
        refine ⟨704835370963500532222539275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469890247309000354815026183 704835370963500532222539275)
        ·
          refine ⟨1057253056445250798333808913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704835370963500532222539275 1057253056445250798333808913)
          ·
            refine ⟨792939792333938098750356685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057253056445250798333808913 792939792333938098750356685)
            ·
              refine ⟨297352422125226787031383757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 792939792333938098750356685 297352422125226787031383757)
              ·
                refine ⟨111507158296960045136768909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297352422125226787031383757 111507158296960045136768909)
                ·
                  refine ⟨41815184361360016926288341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111507158296960045136768909 41815184361360016926288341)
                  ·
                    refine ⟨980043383469375396709883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41815184361360016926288341 980043383469375396709883)
                    ·
                      rfl

theorem cell23_5725883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 7].length) (baseStart_5725883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725883 prefixEnd_5725883 := by exact prefixLift 5725883
  have htrace : WordTrace (prefixWord ++ tailWord_5725883) baseStart_5725883 baseEnd_5725883 := by
    simpa [prefixWord, tailWord_5725883, baseEnd_5725883] using wordTrace_append hprefix tailTrace_5725883
  have hstable : (prefixWord ++ tailWord_5725883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725883).length < 2 ^ (prefixWord ++ tailWord_5725883).sum := by decide
  have hdescent : baseEnd_5725883 < baseStart_5725883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725921 : List Nat := [1, 2, 3, 1, 5, 2, 2, 2, 5]
def baseStart_5725921 : Nat := 118140960795 + 5725921 * 2 ^ 59
def prefixEnd_5725921 : Nat := 4983230072969 + 3 ^ 40 * 5725921 * 2
def baseEnd_5725921 : Nat := 326683295852555226828275

theorem tailTrace_5725921 : CollatzResearch.WordTrace tailWord_5725921 prefixEnd_5725921 326683295852555226828275 := by
  unfold tailWord_5725921
  simp only [CollatzResearch.WordTrace]
  refine ⟨208841495888973601296561617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139227663925982400864374411 208841495888973601296561617)
  ·
    refine ⟨156631121916730200972421213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208841495888973601296561617 156631121916730200972421213)
    ·
      refine ⟨58736670718773825364657955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156631121916730200972421213 58736670718773825364657955)
      ·
        refine ⟨88105006078160738046986933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58736670718773825364657955 88105006078160738046986933)
        ·
          refine ⟨8259844319827569191905025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88105006078160738046986933 8259844319827569191905025)
          ·
            refine ⟨6194883239870676893928769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8259844319827569191905025 6194883239870676893928769)
            ·
              refine ⟨4646162429903007670446577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6194883239870676893928769 4646162429903007670446577)
              ·
                refine ⟨3484621822427255752834933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4646162429903007670446577 3484621822427255752834933)
                ·
                  refine ⟨326683295852555226828275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3484621822427255752834933 326683295852555226828275)
                  ·
                    rfl

theorem cell23_5725921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 5].length) (baseStart_5725921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725921 prefixEnd_5725921 := by exact prefixLift 5725921
  have htrace : WordTrace (prefixWord ++ tailWord_5725921) baseStart_5725921 baseEnd_5725921 := by
    simpa [prefixWord, tailWord_5725921, baseEnd_5725921] using wordTrace_append hprefix tailTrace_5725921
  have hstable : (prefixWord ++ tailWord_5725921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725921).length < 2 ^ (prefixWord ++ tailWord_5725921).sum := by decide
  have hdescent : baseEnd_5725921 < baseStart_5725921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725937 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 1, 6, 2]
def baseStart_5725937 : Nat := 118140960795 + 5725937 * 2 ^ 59
def prefixEnd_5725937 : Nat := 4983230072969 + 3 ^ 40 * 5725937 * 2
def baseEnd_5725937 : Nat := 2940157878363468978854401

theorem tailTrace_5725937 : CollatzResearch.WordTrace tailWord_5725937 prefixEnd_5725937 2940157878363468978854401 := by
  unfold tailWord_5725937
  simp only [CollatzResearch.WordTrace]
  refine ⟨208842079456915636029144065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139228052971277090686096043 208842079456915636029144065)
  ·
    refine ⟨156631559592686727021858049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208842079456915636029144065 156631559592686727021858049)
    ·
      refine ⟨117473669694515045266393537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156631559592686727021858049 117473669694515045266393537)
      ·
        refine ⟨88105252270886283949795153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117473669694515045266393537 88105252270886283949795153)
        ·
          refine ⟨66078939203164712962346365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88105252270886283949795153 66078939203164712962346365)
          ·
            refine ⟨24779602201186767360879887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66078939203164712962346365 24779602201186767360879887)
            ·
              refine ⟨37169403301780151041319831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24779602201186767360879887 37169403301780151041319831)
              ·
                refine ⟨55754104952670226561979747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37169403301780151041319831 55754104952670226561979747)
                ·
                  refine ⟨83631157429005339842969621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55754104952670226561979747 83631157429005339842969621)
                  ·
                    refine ⟨3920210504484625305139201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83631157429005339842969621 3920210504484625305139201)
                    ·
                      refine ⟨2940157878363468978854401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920210504484625305139201 2940157878363468978854401)
                      ·
                        rfl

theorem cell23_5725937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_5725937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725937 prefixEnd_5725937 := by exact prefixLift 5725937
  have htrace : WordTrace (prefixWord ++ tailWord_5725937) baseStart_5725937 baseEnd_5725937 := by
    simpa [prefixWord, tailWord_5725937, baseEnd_5725937] using wordTrace_append hprefix tailTrace_5725937
  have hstable : (prefixWord ++ tailWord_5725937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725937).length < 2 ^ (prefixWord ++ tailWord_5725937).sum := by decide
  have hdescent : baseEnd_5725937 < baseStart_5725937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725954 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_5725954 : Nat := 118140960795 + 5725954 * 2 ^ 59
def prefixEnd_5725954 : Nat := 4983230072969 + 3 ^ 40 * 5725954 * 2
def baseEnd_5725954 : Nat := 2940166607534595412341823

theorem tailTrace_5725954 : CollatzResearch.WordTrace tailWord_5725954 prefixEnd_5725954 2940166607534595412341823 := by
  unfold tailWord_5725954
  simp only [CollatzResearch.WordTrace]
  refine ⟨52210674874463511983128229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139228466331902698621675277 52210674874463511983128229)
  ·
    refine ⟨9789501538961908496836543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52210674874463511983128229 9789501538961908496836543)
    ·
      refine ⟨14684252308442862745254815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9789501538961908496836543 14684252308442862745254815)
      ·
        refine ⟨22026378462664294117882223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14684252308442862745254815 22026378462664294117882223)
        ·
          refine ⟨33039567693996441176823335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22026378462664294117882223 33039567693996441176823335)
          ·
            refine ⟨49559351540994661765235003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33039567693996441176823335 49559351540994661765235003)
            ·
              refine ⟨74339027311491992647852505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49559351540994661765235003 74339027311491992647852505)
              ·
                refine ⟨55754270483618994485889379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74339027311491992647852505 55754270483618994485889379)
                ·
                  refine ⟨83631405725428491728834069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55754270483618994485889379 83631405725428491728834069)
                  ·
                    refine ⟨3920222143379460549789097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83631405725428491728834069 3920222143379460549789097)
                    ·
                      refine ⟨2940166607534595412341823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920222143379460549789097 2940166607534595412341823)
                      ·
                        rfl

theorem cell23_5725954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_5725954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725954 prefixEnd_5725954 := by exact prefixLift 5725954
  have htrace : WordTrace (prefixWord ++ tailWord_5725954) baseStart_5725954 baseEnd_5725954 := by
    simpa [prefixWord, tailWord_5725954, baseEnd_5725954] using wordTrace_append hprefix tailTrace_5725954
  have hstable : (prefixWord ++ tailWord_5725954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725954).length < 2 ^ (prefixWord ++ tailWord_5725954).sum := by decide
  have hdescent : baseEnd_5725954 < baseStart_5725954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725960 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 8]
def baseStart_5725960 : Nat := 118140960795 + 5725960 * 2 ^ 59
def prefixEnd_5725960 : Nat := 4983230072969 + 3 ^ 40 * 5725960 * 2
def baseEnd_5725960 : Nat := 326685520935391376540755

theorem tailTrace_5725960 : CollatzResearch.WordTrace tailWord_5725960 prefixEnd_5725960 326685520935391376540755 := by
  unfold tailWord_5725960
  simp only [CollatzResearch.WordTrace]
  refine ⟨104421459167916155478615667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139228612223888207304820889 104421459167916155478615667)
  ·
    refine ⟨156632188751874233217923501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104421459167916155478615667 156632188751874233217923501)
    ·
      refine ⟨58737070781952837456721313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156632188751874233217923501 58737070781952837456721313)
      ·
        refine ⟨44052803086464628092540985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58737070781952837456721313 44052803086464628092540985)
        ·
          refine ⟨33039602314848471069405739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44052803086464628092540985 33039602314848471069405739)
          ·
            refine ⟨49559403472272706604108609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33039602314848471069405739 49559403472272706604108609)
            ·
              refine ⟨37169552604204529953081457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49559403472272706604108609 37169552604204529953081457)
              ·
                refine ⟨27877164453153397464811093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37169552604204529953081457 27877164453153397464811093)
                ·
                  refine ⟨326685520935391376540755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27877164453153397464811093 326685520935391376540755)
                  ·
                    rfl

theorem cell23_5725960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 8].length) (baseStart_5725960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725960 prefixEnd_5725960 := by exact prefixLift 5725960
  have htrace : WordTrace (prefixWord ++ tailWord_5725960) baseStart_5725960 baseEnd_5725960 := by
    simpa [prefixWord, tailWord_5725960, baseEnd_5725960] using wordTrace_append hprefix tailTrace_5725960
  have hstable : (prefixWord ++ tailWord_5725960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725960).length < 2 ^ (prefixWord ++ tailWord_5725960).sum := by decide
  have hdescent : baseEnd_5725960 < baseStart_5725960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725964 : List Nat := [2, 2, 1, 2, 2, 1, 3, 5, 1, 4]
def baseStart_5725964 : Nat := 118140960795 + 5725964 * 2 ^ 59
def prefixEnd_5725964 : Nat := 4983230072969 + 3 ^ 40 * 5725964 * 2
def baseEnd_5725964 : Nat := 980057247447046791072259

theorem tailTrace_5725964 : CollatzResearch.WordTrace tailWord_5725964 prefixEnd_5725964 980057247447046791072259 := by
  unfold tailWord_5725964
  simp only [CollatzResearch.WordTrace]
  refine ⟨104421532113908909820188473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139228709485211879760251297 104421532113908909820188473)
  ·
    refine ⟨78316149085431682365141355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104421532113908909820188473 78316149085431682365141355)
    ·
      refine ⟨117474223628147523547712033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78316149085431682365141355 117474223628147523547712033)
      ·
        refine ⟨88105667721110642660784025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117474223628147523547712033 88105667721110642660784025)
        ·
          refine ⟨66079250790832981995588019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88105667721110642660784025 66079250790832981995588019)
          ·
            refine ⟨99118876186249472993382029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66079250790832981995588019 99118876186249472993382029)
            ·
              refine ⟨37169578569843552372518261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99118876186249472993382029 37169578569843552372518261)
              ·
                refine ⟨3484647990922833034923587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37169578569843552372518261 3484647990922833034923587)
                ·
                  refine ⟨5226971986384249552385381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3484647990922833034923587 5226971986384249552385381)
                  ·
                    refine ⟨980057247447046791072259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5226971986384249552385381 980057247447046791072259)
                    ·
                      rfl

theorem cell23_5725964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_5725964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725964 prefixEnd_5725964 := by exact prefixLift 5725964
  have htrace : WordTrace (prefixWord ++ tailWord_5725964) baseStart_5725964 baseEnd_5725964 := by
    simpa [prefixWord, tailWord_5725964, baseEnd_5725964] using wordTrace_append hprefix tailTrace_5725964
  have hstable : (prefixWord ++ tailWord_5725964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725964).length < 2 ^ (prefixWord ++ tailWord_5725964).sum := by decide
  have hdescent : baseEnd_5725964 < baseStart_5725964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5725980 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_5725980 : Nat := 118140960795 + 5725980 * 2 ^ 59
def prefixEnd_5725980 : Nat := 4983230072969 + 3 ^ 40 * 5725980 * 2
def baseEnd_5725980 : Nat := 2940179958031612310616703

theorem tailTrace_5725980 : CollatzResearch.WordTrace tailWord_5725980 prefixEnd_5725980 2940179958031612310616703 := by
  unfold tailWord_5725980
  simp only [CollatzResearch.WordTrace]
  refine ⟨104421823897879927186479697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139229098530506569581972929 104421823897879927186479697)
  ·
    refine ⟨78316367923409945389859773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104421823897879927186479697 78316367923409945389859773)
    ·
      refine ⟨29368637971278729521197415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78316367923409945389859773 29368637971278729521197415)
      ·
        refine ⟨44052956956918094281796123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29368637971278729521197415 44052956956918094281796123)
        ·
          refine ⟨66079435435377141422694185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44052956956918094281796123 66079435435377141422694185)
          ·
            refine ⟨49559576576532856067020639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66079435435377141422694185 49559576576532856067020639)
            ·
              refine ⟨74339364864799284100530959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49559576576532856067020639 74339364864799284100530959)
              ·
                refine ⟨111509047297198926150796439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74339364864799284100530959 111509047297198926150796439)
                ·
                  refine ⟨167263570945798389226194659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111509047297198926150796439 167263570945798389226194659)
                  ·
                    refine ⟨250895356418697583839291989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167263570945798389226194659 250895356418697583839291989)
                    ·
                      refine ⟨2940179958031612310616703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 250895356418697583839291989 2940179958031612310616703)
                      ·
                        rfl

theorem cell23_5725980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_5725980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5725980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5725980 prefixEnd_5725980 := by exact prefixLift 5725980
  have htrace : WordTrace (prefixWord ++ tailWord_5725980) baseStart_5725980 baseEnd_5725980 := by
    simpa [prefixWord, tailWord_5725980, baseEnd_5725980] using wordTrace_append hprefix tailTrace_5725980
  have hstable : (prefixWord ++ tailWord_5725980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5725980).length < 2 ^ (prefixWord ++ tailWord_5725980).sum := by decide
  have hdescent : baseEnd_5725980 < baseStart_5725980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5725980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726047 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 5]
def baseStart_5726047 : Nat := 118140960795 + 5726047 * 2 ^ 59
def prefixEnd_5726047 : Nat := 4983230072969 + 3 ^ 40 * 5726047 * 2
def baseEnd_5726047 : Nat := 2940214361235463548478895

theorem tailTrace_5726047 : CollatzResearch.WordTrace tailWord_5726047 prefixEnd_5726047 2940214361235463548478895 := by
  unfold tailWord_5726047
  simp only [CollatzResearch.WordTrace]
  refine ⟨208846091486517124815648395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139230727657678083210432263 208846091486517124815648395)
  ·
    refine ⟨313269137229775687223472593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208846091486517124815648395 313269137229775687223472593)
    ·
      refine ⟨234951852922331765417604445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313269137229775687223472593 234951852922331765417604445)
      ·
        refine ⟨88106944845874412031601667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234951852922331765417604445 88106944845874412031601667)
        ·
          refine ⟨132160417268811618047402501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88106944845874412031601667 132160417268811618047402501)
          ·
            refine ⟨24780078237902178383887969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132160417268811618047402501 24780078237902178383887969)
            ·
              refine ⟨18585058678426633787915977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24780078237902178383887969 18585058678426633787915977)
              ·
                refine ⟨13938794008819975340936983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18585058678426633787915977 13938794008819975340936983)
                ·
                  refine ⟨20908191013229963011405475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13938794008819975340936983 20908191013229963011405475)
                  ·
                    refine ⟨31362286519844944517108213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20908191013229963011405475 31362286519844944517108213)
                    ·
                      refine ⟨2940214361235463548478895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31362286519844944517108213 2940214361235463548478895)
                      ·
                        rfl

theorem cell23_5726047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_5726047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726047 prefixEnd_5726047 := by exact prefixLift 5726047
  have htrace : WordTrace (prefixWord ++ tailWord_5726047) baseStart_5726047 baseEnd_5726047 := by
    simpa [prefixWord, tailWord_5726047, baseEnd_5726047] using wordTrace_append hprefix tailTrace_5726047
  have hstable : (prefixWord ++ tailWord_5726047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726047).length < 2 ^ (prefixWord ++ tailWord_5726047).sum := by decide
  have hdescent : baseEnd_5726047 < baseStart_5726047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726058 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 1, 5]
def baseStart_5726058 : Nat := 118140960795 + 5726058 * 2 ^ 59
def prefixEnd_5726058 : Nat := 4983230072969 + 3 ^ 40 * 5726058 * 2
def baseEnd_5726058 : Nat := 980073336507554335147115

theorem tailTrace_5726058 : CollatzResearch.WordTrace tailWord_5726058 prefixEnd_5726058 980073336507554335147115 := by
  unfold tailWord_5726058
  simp only [CollatzResearch.WordTrace]
  refine ⟨52211623172369318423574707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139230995126318182462865885 52211623172369318423574707)
  ·
    refine ⟨78317434758553977635362061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52211623172369318423574707 78317434758553977635362061)
    ·
      refine ⟨29369038034457741613260773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78317434758553977635362061 29369038034457741613260773)
      ·
        refine ⟨5506694631460826552486395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29369038034457741613260773 5506694631460826552486395)
        ·
          refine ⟨8260041947191239828729593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5506694631460826552486395 8260041947191239828729593)
          ·
            refine ⟨6195031460393429871547195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8260041947191239828729593 6195031460393429871547195)
            ·
              refine ⟨9292547190590144807320793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6195031460393429871547195 9292547190590144807320793)
              ·
                refine ⟨6969410392942608605490595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9292547190590144807320793 6969410392942608605490595)
                ·
                  refine ⟨10454115589413912908235893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6969410392942608605490595 10454115589413912908235893)
                  ·
                    refine ⟨980073336507554335147115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10454115589413912908235893 980073336507554335147115)
                    ·
                      rfl

theorem cell23_5726058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_5726058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726058 prefixEnd_5726058 := by exact prefixLift 5726058
  have htrace : WordTrace (prefixWord ++ tailWord_5726058) baseStart_5726058 baseEnd_5726058 := by
    simpa [prefixWord, tailWord_5726058, baseEnd_5726058] using wordTrace_append hprefix tailTrace_5726058
  have hstable : (prefixWord ++ tailWord_5726058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726058).length < 2 ^ (prefixWord ++ tailWord_5726058).sum := by decide
  have hdescent : baseEnd_5726058 < baseStart_5726058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726061 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_5726061 : Nat := 118140960795 + 5726061 * 2 ^ 59
def prefixEnd_5726061 : Nat := 4983230072969 + 3 ^ 40 * 5726061 * 2
def baseEnd_5726061 : Nat := 2940221549964626493703831

theorem tailTrace_5726061 : CollatzResearch.WordTrace tailWord_5726061 prefixEnd_5726061 2940221549964626493703831 := by
  unfold tailWord_5726061
  simp only [CollatzResearch.WordTrace]
  refine ⟨208846602108466405206658037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139231068072310936804438691 208846602108466405206658037)
  ·
    refine ⟨19579368947668725488124191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208846602108466405206658037 19579368947668725488124191)
    ·
      refine ⟨29369053421503088232186287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19579368947668725488124191 29369053421503088232186287)
      ·
        refine ⟨44053580132254632348279431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29369053421503088232186287 44053580132254632348279431)
        ·
          refine ⟨66080370198381948522419147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44053580132254632348279431 66080370198381948522419147)
          ·
            refine ⟨99120555297572922783628721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66080370198381948522419147 99120555297572922783628721)
            ·
              refine ⟨74340416473179692087721541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99120555297572922783628721 74340416473179692087721541)
              ·
                refine ⟨13938828088721192266447789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74340416473179692087721541 13938828088721192266447789)
                ·
                  refine ⟨5227060533270447099917921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13938828088721192266447789 5227060533270447099917921)
                  ·
                    refine ⟨3920295399952835324938441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5227060533270447099917921 3920295399952835324938441)
                    ·
                      refine ⟨2940221549964626493703831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920295399952835324938441 2940221549964626493703831)
                      ·
                        rfl

theorem cell23_5726061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_5726061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726061 prefixEnd_5726061 := by exact prefixLift 5726061
  have htrace : WordTrace (prefixWord ++ tailWord_5726061) baseStart_5726061 baseEnd_5726061 := by
    simpa [prefixWord, tailWord_5726061, baseEnd_5726061] using wordTrace_append hprefix tailTrace_5726061
  have hstable : (prefixWord ++ tailWord_5726061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726061).length < 2 ^ (prefixWord ++ tailWord_5726061).sum := by decide
  have hdescent : baseEnd_5726061 < baseStart_5726061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726111 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 3]
def baseStart_5726111 : Nat := 118140960795 + 5726111 * 2 ^ 59
def prefixEnd_5726111 : Nat := 4983230072969 + 3 ^ 40 * 5726111 * 2
def baseEnd_5726111 : Nat := 2940247223997351298078601

theorem tailTrace_5726111 : CollatzResearch.WordTrace tailWord_5726111 prefixEnd_5726111 2940247223997351298078601 := by
  unfold tailWord_5726111
  simp only [CollatzResearch.WordTrace]
  refine ⟨208848425758285263745978187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139232283838856842497318791 208848425758285263745978187)
  ·
    refine ⟨313272638637427895618967281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208848425758285263745978187 313272638637427895618967281)
    ·
      refine ⟨234954478978070921714225461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313272638637427895618967281 234954478978070921714225461)
      ·
        refine ⟨22026982404194148910708637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234954478978070921714225461 22026982404194148910708637)
        ·
          refine ⟨8260118401572805841515739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22026982404194148910708637 8260118401572805841515739)
          ·
            refine ⟨12390177602359208762273609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8260118401572805841515739 12390177602359208762273609)
            ·
              refine ⟨9292633201769406571705207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12390177602359208762273609 9292633201769406571705207)
              ·
                refine ⟨13938949802654109857557811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9292633201769406571705207 13938949802654109857557811)
                ·
                  refine ⟨20908424703981164786336717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13938949802654109857557811 20908424703981164786336717)
                  ·
                    refine ⟨7840659263992936794876269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20908424703981164786336717 7840659263992936794876269)
                    ·
                      refine ⟨2940247223997351298078601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7840659263992936794876269 2940247223997351298078601)
                      ·
                        rfl

theorem cell23_5726111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_5726111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726111 prefixEnd_5726111 := by exact prefixLift 5726111
  have htrace : WordTrace (prefixWord ++ tailWord_5726111) baseStart_5726111 baseEnd_5726111 := by
    simpa [prefixWord, tailWord_5726111, baseEnd_5726111] using wordTrace_append hprefix tailTrace_5726111
  have hstable : (prefixWord ++ tailWord_5726111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726111).length < 2 ^ (prefixWord ++ tailWord_5726111).sum := by decide
  have hdescent : baseEnd_5726111 < baseStart_5726111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726132 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_5726132 : Nat := 118140960795 + 5726132 * 2 ^ 59
def prefixEnd_5726132 : Nat := 4983230072969 + 3 ^ 40 * 5726132 * 2
def baseEnd_5726132 : Nat := 2940258007091095715916005

theorem tailTrace_5726132 : CollatzResearch.WordTrace tailWord_5726132 prefixEnd_5726132 2940258007091095715916005 := by
  unfold tailWord_5726132
  simp only [CollatzResearch.WordTrace]
  refine ⟨104424595845604592166246325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139232794460806122888328433 104424595845604592166246325)
  ·
    refine ⟨9789805860525430515585593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104424595845604592166246325 9789805860525430515585593)
    ·
      refine ⟨7342354395394072886689195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9789805860525430515585593 7342354395394072886689195)
      ·
        refine ⟨11013531593091109330033793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7342354395394072886689195 11013531593091109330033793)
        ·
          refine ⟨8260148694818331997525345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11013531593091109330033793 8260148694818331997525345)
          ·
            refine ⟨6195111521113748998144009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8260148694818331997525345 6195111521113748998144009)
            ·
              refine ⟨4646333640835311748608007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6195111521113748998144009 4646333640835311748608007)
              ·
                refine ⟨6969500461252967622912011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4646333640835311748608007 6969500461252967622912011)
                ·
                  refine ⟨10454250691879451434368017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6969500461252967622912011 10454250691879451434368017)
                  ·
                    refine ⟨7840688018909588575776013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10454250691879451434368017 7840688018909588575776013)
                    ·
                      refine ⟨2940258007091095715916005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7840688018909588575776013 2940258007091095715916005)
                      ·
                        rfl

theorem cell23_5726132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_5726132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726132 prefixEnd_5726132 := by exact prefixLift 5726132
  have htrace : WordTrace (prefixWord ++ tailWord_5726132) baseStart_5726132 baseEnd_5726132 := by
    simpa [prefixWord, tailWord_5726132, baseEnd_5726132] using wordTrace_append hprefix tailTrace_5726132
  have hstable : (prefixWord ++ tailWord_5726132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726132).length < 2 ^ (prefixWord ++ tailWord_5726132).sum := by decide
  have hdescent : baseEnd_5726132 < baseStart_5726132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726137 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_5726137 : Nat := 118140960795 + 5726137 * 2 ^ 59
def prefixEnd_5726137 : Nat := 4983230072969 + 3 ^ 40 * 5726137 * 2
def baseEnd_5726137 : Nat := 2940260574494368196353481

theorem tailTrace_5726137 : CollatzResearch.WordTrace tailWord_5726137 prefixEnd_5726137 2940260574494368196353481 := by
  unfold tailWord_5726137
  simp only [CollatzResearch.WordTrace]
  refine ⟨208849374056191070186424665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139232916037460713457616443 208849374056191070186424665)
  ·
    refine ⟨156637030542143302639818499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208849374056191070186424665 156637030542143302639818499)
    ·
      refine ⟨234955545813214953959727749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156637030542143302639818499 234955545813214953959727749)
      ·
        refine ⟨44054164839977803867448953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234955545813214953959727749 44054164839977803867448953)
        ·
          refine ⟨33040623629983352900586715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44054164839977803867448953 33040623629983352900586715)
          ·
            refine ⟨49560935444975029350880073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33040623629983352900586715 49560935444975029350880073)
            ·
              refine ⟨37170701583731272013160055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49560935444975029350880073 37170701583731272013160055)
              ·
                refine ⟨55756052375596908019740083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37170701583731272013160055 55756052375596908019740083)
                ·
                  refine ⟨83634078563395362029610125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55756052375596908019740083 83634078563395362029610125)
                  ·
                    refine ⟨31362779461273260761103797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83634078563395362029610125 31362779461273260761103797)
                    ·
                      refine ⟨2940260574494368196353481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31362779461273260761103797 2940260574494368196353481)
                      ·
                        rfl

theorem cell23_5726137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_5726137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726137 prefixEnd_5726137 := by exact prefixLift 5726137
  have htrace : WordTrace (prefixWord ++ tailWord_5726137) baseStart_5726137 baseEnd_5726137 := by
    simpa [prefixWord, tailWord_5726137, baseEnd_5726137] using wordTrace_append hprefix tailTrace_5726137
  have hstable : (prefixWord ++ tailWord_5726137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726137).length < 2 ^ (prefixWord ++ tailWord_5726137).sum := by decide
  have hdescent : baseEnd_5726137 < baseStart_5726137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726164 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_5726164 : Nat := 118140960795 + 5726164 * 2 ^ 59
def prefixEnd_5726164 : Nat := 4983230072969 + 3 ^ 40 * 5726164 * 2
def baseEnd_5726164 : Nat := 2940274438472039590715857

theorem tailTrace_5726164 : CollatzResearch.WordTrace tailWord_5726164 prefixEnd_5726164 2940274438472039590715857 := by
  unfold tailWord_5726164
  simp only [CollatzResearch.WordTrace]
  refine ⟨104425179413546626898828773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139233572551395502531771697 104425179413546626898828773)
  ·
    refine ⟨19579721140039992543530395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104425179413546626898828773 19579721140039992543530395)
    ·
      refine ⟨29369581710059988815295593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19579721140039992543530395 29369581710059988815295593)
      ·
        refine ⟨22027186282544991611471695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29369581710059988815295593 22027186282544991611471695)
        ·
          refine ⟨33040779423817487417207543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22027186282544991611471695 33040779423817487417207543)
          ·
            refine ⟨49561169135726231125811315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33040779423817487417207543 49561169135726231125811315)
            ·
              refine ⟨74341753703589346688716973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49561169135726231125811315 74341753703589346688716973)
              ·
                refine ⟨27878157638846005008268865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74341753703589346688716973 27878157638846005008268865)
                ·
                  refine ⟨20908618229134503756201649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27878157638846005008268865 20908618229134503756201649)
                  ·
                    refine ⟨15681463671850877817151237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20908618229134503756201649 15681463671850877817151237)
                    ·
                      refine ⟨2940274438472039590715857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15681463671850877817151237 2940274438472039590715857)
                      ·
                        rfl

theorem cell23_5726164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_5726164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726164 prefixEnd_5726164 := by exact prefixLift 5726164
  have htrace : WordTrace (prefixWord ++ tailWord_5726164) baseStart_5726164 baseEnd_5726164 := by
    simpa [prefixWord, tailWord_5726164, baseEnd_5726164] using wordTrace_append hprefix tailTrace_5726164
  have hstable : (prefixWord ++ tailWord_5726164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726164).length < 2 ^ (prefixWord ++ tailWord_5726164).sum := by decide
  have hdescent : baseEnd_5726164 < baseStart_5726164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726187 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 6, 5]
def baseStart_5726187 : Nat := 118140960795 + 5726187 * 2 ^ 59
def prefixEnd_5726187 : Nat := 4983230072969 + 3 ^ 40 * 5726187 * 2
def baseEnd_5726187 : Nat := 980095416175697666909417

theorem tailTrace_5726187 : CollatzResearch.WordTrace tailWord_5726187 prefixEnd_5726187 980095416175697666909417 := by
  unfold tailWord_5726187
  simp only [CollatzResearch.WordTrace]
  refine ⟨208851197706009928725744815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139234131804006619150496543 208851197706009928725744815)
  ·
    refine ⟨313276796559014893088617223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208851197706009928725744815 313276796559014893088617223)
    ·
      refine ⟨469915194838522339632925835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313276796559014893088617223 469915194838522339632925835)
      ·
        refine ⟨704872792257783509449388753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469915194838522339632925835 704872792257783509449388753)
        ·
          refine ⟨528654594193337632087041565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704872792257783509449388753 528654594193337632087041565)
          ·
            refine ⟨198245472822501612032640587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 528654594193337632087041565 198245472822501612032640587)
            ·
              refine ⟨297368209233752418048960881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198245472822501612032640587 297368209233752418048960881)
              ·
                refine ⟨223026156925314313536720661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297368209233752418048960881 223026156925314313536720661)
                ·
                  refine ⟨10454351105874108447033781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 223026156925314313536720661 10454351105874108447033781)
                  ·
                    refine ⟨980095416175697666909417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10454351105874108447033781 980095416175697666909417)
                    ·
                      rfl

theorem cell23_5726187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 5].length) (baseStart_5726187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726187 prefixEnd_5726187 := by exact prefixLift 5726187
  have htrace : WordTrace (prefixWord ++ tailWord_5726187) baseStart_5726187 baseEnd_5726187 := by
    simpa [prefixWord, tailWord_5726187, baseEnd_5726187] using wordTrace_append hprefix tailTrace_5726187
  have hstable : (prefixWord ++ tailWord_5726187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726187).length < 2 ^ (prefixWord ++ tailWord_5726187).sum := by decide
  have hdescent : baseEnd_5726187 < baseStart_5726187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726204 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_5726204 : Nat := 118140960795 + 5726204 * 2 ^ 59
def prefixEnd_5726204 : Nat := 4983230072969 + 3 ^ 40 * 5726204 * 2
def baseEnd_5726204 : Nat := 980098325899406478071891

theorem tailTrace_5726204 : CollatzResearch.WordTrace tailWord_5726204 prefixEnd_5726204 980098325899406478071891 := by
  unfold tailWord_5726204
  simp only [CollatzResearch.WordTrace]
  refine ⟨104425908873474170314556833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139234545164632227086075777 104425908873474170314556833)
  ·
    refine ⟨78319431655105627735917625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104425908873474170314556833 78319431655105627735917625)
    ·
      refine ⟨58739573741329220801938219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78319431655105627735917625 58739573741329220801938219)
      ·
        refine ⟨88109360611993831202907329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58739573741329220801938219 88109360611993831202907329)
        ·
          refine ⟨66082020458995373402180497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88109360611993831202907329 66082020458995373402180497)
          ·
            refine ⟨49561515344246530051635373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66082020458995373402180497 49561515344246530051635373)
            ·
              refine ⟨18585568254092448769363265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49561515344246530051635373 18585568254092448769363265)
              ·
                refine ⟨13939176190569336577022449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18585568254092448769363265 13939176190569336577022449)
                ·
                  refine ⟨10454382142927002432766837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13939176190569336577022449 10454382142927002432766837)
                  ·
                    refine ⟨980098325899406478071891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10454382142927002432766837 980098325899406478071891)
                    ·
                      rfl

theorem cell23_5726204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_5726204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726204 prefixEnd_5726204 := by exact prefixLift 5726204
  have htrace : WordTrace (prefixWord ++ tailWord_5726204) baseStart_5726204 baseEnd_5726204 := by
    simpa [prefixWord, tailWord_5726204, baseEnd_5726204] using wordTrace_append hprefix tailTrace_5726204
  have hstable : (prefixWord ++ tailWord_5726204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726204).length < 2 ^ (prefixWord ++ tailWord_5726204).sum := by decide
  have hdescent : baseEnd_5726204 < baseStart_5726204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726261 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_5726261 : Nat := 118140960795 + 5726261 * 2 ^ 59
def prefixEnd_5726261 : Nat := 4983230072969 + 3 ^ 40 * 5726261 * 2
def baseEnd_5726261 : Nat := 2940324246095525711202911

theorem tailTrace_5726261 : CollatzResearch.WordTrace tailWord_5726261 prefixEnd_5726261 2940324246095525711202911 := by
  unfold tailWord_5726261
  simp only [CollatzResearch.WordTrace]
  refine ⟨208853896707741839363938637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139235931138494559575959091 208853896707741839363938637)
  ·
    refine ⟨78320211265403189761476989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208853896707741839363938637 78320211265403189761476989)
    ·
      refine ⟨29370079224526196160553871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78320211265403189761476989 29370079224526196160553871)
      ·
        refine ⟨44055118836789294240830807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29370079224526196160553871 44055118836789294240830807)
        ·
          refine ⟨66082678255183941361246211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44055118836789294240830807 66082678255183941361246211)
          ·
            refine ⟨99124017382775912041869317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66082678255183941361246211 99124017382775912041869317)
            ·
              refine ⟨18585753259270483507850497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99124017382775912041869317 18585753259270483507850497)
              ·
                refine ⟨13939314944452862630887873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18585753259270483507850497 13939314944452862630887873)
                ·
                  refine ⟨10454486208339646973165905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13939314944452862630887873 10454486208339646973165905)
                  ·
                    refine ⟨7840864656254735229874429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10454486208339646973165905 7840864656254735229874429)
                    ·
                      refine ⟨2940324246095525711202911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7840864656254735229874429 2940324246095525711202911)
                      ·
                        rfl

theorem cell23_5726261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_5726261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726261 prefixEnd_5726261 := by exact prefixLift 5726261
  have htrace : WordTrace (prefixWord ++ tailWord_5726261) baseStart_5726261 baseEnd_5726261 := by
    simpa [prefixWord, tailWord_5726261, baseEnd_5726261] using wordTrace_append hprefix tailTrace_5726261
  have hstable : (prefixWord ++ tailWord_5726261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726261).length < 2 ^ (prefixWord ++ tailWord_5726261).sum := by decide
  have hdescent : baseEnd_5726261 < baseStart_5726261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726267 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 8]
def baseStart_5726267 : Nat := 118140960795 + 5726267 * 2 ^ 59
def prefixEnd_5726267 : Nat := 4983230072969 + 3 ^ 40 * 5726267 * 2
def baseEnd_5726267 : Nat := 2940327326979452687727883

theorem tailTrace_5726267 : CollatzResearch.WordTrace tailWord_5726267 prefixEnd_5726267 2940327326979452687727883 := by
  unfold tailWord_5726267
  simp only [CollatzResearch.WordTrace]
  refine ⟨208854115545720102388657055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139236077030480068259104703 208854115545720102388657055)
  ·
    refine ⟨313281173318580153582985583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208854115545720102388657055 313281173318580153582985583)
    ·
      refine ⟨469921759977870230374478375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313281173318580153582985583 469921759977870230374478375)
      ·
        refine ⟨704882639966805345561717563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469921759977870230374478375 704882639966805345561717563)
        ·
          refine ⟨1057323959950208018342576345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704882639966805345561717563 1057323959950208018342576345)
          ·
            refine ⟨792992969962656013756932259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057323959950208018342576345 792992969962656013756932259)
            ·
              refine ⟨1189489454943984020635398389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792992969962656013756932259 1189489454943984020635398389)
              ·
                refine ⟨111514636400998501934568599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1189489454943984020635398389 111514636400998501934568599)
                ·
                  refine ⟨167271954601497752901852899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111514636400998501934568599 167271954601497752901852899)
                  ·
                    refine ⟨250907931902246629352779349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167271954601497752901852899 250907931902246629352779349)
                    ·
                      refine ⟨2940327326979452687727883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 250907931902246629352779349 2940327326979452687727883)
                      ·
                        rfl

theorem cell23_5726267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_5726267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726267 prefixEnd_5726267 := by exact prefixLift 5726267
  have htrace : WordTrace (prefixWord ++ tailWord_5726267) baseStart_5726267 baseEnd_5726267 := by
    simpa [prefixWord, tailWord_5726267, baseEnd_5726267] using wordTrace_append hprefix tailTrace_5726267
  have hstable : (prefixWord ++ tailWord_5726267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726267).length < 2 ^ (prefixWord ++ tailWord_5726267).sum := by decide
  have hdescent : baseEnd_5726267 < baseStart_5726267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726268 : List Nat := [2, 2, 2, 2, 2, 1, 3, 4, 1, 4]
def baseStart_5726268 : Nat := 118140960795 + 5726268 * 2 ^ 59
def prefixEnd_5726268 : Nat := 4983230072969 + 3 ^ 40 * 5726268 * 2
def baseEnd_5726268 : Nat := 980109280153369061271793

theorem tailTrace_5726268 : CollatzResearch.WordTrace tailWord_5726268 prefixEnd_5726268 980109280153369061271793 := by
  unfold tailWord_5726268
  simp only [CollatzResearch.WordTrace]
  refine ⟨104427076009358239779721729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139236101345810986372962305 104427076009358239779721729)
  ·
    refine ⟨78320307007018679834791297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104427076009358239779721729 78320307007018679834791297)
    ·
      refine ⟨58740230255264009876093473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78320307007018679834791297 58740230255264009876093473)
      ·
        refine ⟨44055172691448007407070105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58740230255264009876093473 44055172691448007407070105)
        ·
          refine ⟨33041379518586005555302579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44055172691448007407070105 33041379518586005555302579)
          ·
            refine ⟨49562069277879008332953869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33041379518586005555302579 49562069277879008332953869)
            ·
              refine ⟨18585775979204628124857701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49562069277879008332953869 18585775979204628124857701)
              ·
                refine ⟨3484832996100867773410819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18585775979204628124857701 3484832996100867773410819)
                ·
                  refine ⟨5227249494151301660116229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3484832996100867773410819 5227249494151301660116229)
                  ·
                    refine ⟨980109280153369061271793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227249494151301660116229 980109280153369061271793)
                    ·
                      rfl

theorem cell23_5726268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_5726268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726268 prefixEnd_5726268 := by exact prefixLift 5726268
  have htrace : WordTrace (prefixWord ++ tailWord_5726268) baseStart_5726268 baseEnd_5726268 := by
    simpa [prefixWord, tailWord_5726268, baseEnd_5726268] using wordTrace_append hprefix tailTrace_5726268
  have hstable : (prefixWord ++ tailWord_5726268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726268).length < 2 ^ (prefixWord ++ tailWord_5726268).sum := by decide
  have hdescent : baseEnd_5726268 < baseStart_5726268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726278 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_5726278 : Nat := 118140960795 + 5726278 * 2 ^ 59
def prefixEnd_5726278 : Nat := 4983230072969 + 3 ^ 40 * 5726278 * 2
def baseEnd_5726278 : Nat := 2940332975266652144690333

theorem tailTrace_5726278 : CollatzResearch.WordTrace tailWord_5726278 prefixEnd_5726278 2940332975266652144690333 := by
  unfold tailWord_5726278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6526703648396257852103359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139236344499120167511538325 6526703648396257852103359)
  ·
    refine ⟨9790055472594386778155039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6526703648396257852103359 9790055472594386778155039)
    ·
      refine ⟨14685083208891580167232559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9790055472594386778155039 14685083208891580167232559)
      ·
        refine ⟨22027624813337370250848839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14685083208891580167232559 22027624813337370250848839)
        ·
          refine ⟨33041437220006055376273259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22027624813337370250848839 33041437220006055376273259)
          ·
            refine ⟨49562155830009083064409889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33041437220006055376273259 49562155830009083064409889)
            ·
              refine ⟨37171616872506812298307417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49562155830009083064409889 37171616872506812298307417)
              ·
                refine ⟨27878712654380109223730563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37171616872506812298307417 27878712654380109223730563)
                ·
                  refine ⟨41818068981570163835595845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27878712654380109223730563 41818068981570163835595845)
                  ·
                    refine ⟨7840887934044405719174221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41818068981570163835595845 7840887934044405719174221)
                    ·
                      refine ⟨2940332975266652144690333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7840887934044405719174221 2940332975266652144690333)
                      ·
                        rfl

theorem cell23_5726278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_5726278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726278 prefixEnd_5726278 := by exact prefixLift 5726278
  have htrace : WordTrace (prefixWord ++ tailWord_5726278) baseStart_5726278 baseEnd_5726278 := by
    simpa [prefixWord, tailWord_5726278, baseEnd_5726278] using wordTrace_append hprefix tailTrace_5726278
  have hstable : (prefixWord ++ tailWord_5726278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726278).length < 2 ^ (prefixWord ++ tailWord_5726278).sum := by decide
  have hdescent : baseEnd_5726278 < baseStart_5726278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726311 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 1, 5]
def baseStart_5726311 : Nat := 118140960795 + 5726311 * 2 ^ 59
def prefixEnd_5726311 : Nat := 4983230072969 + 3 ^ 40 * 5726311 * 2
def baseEnd_5726311 : Nat := 980116640042750171859227

theorem tailTrace_5726311 : CollatzResearch.WordTrace tailWord_5726311 prefixEnd_5726311 980116640042750171859227 := by
  unfold tailWord_5726311
  simp only [CollatzResearch.WordTrace]
  refine ⟨208855720357560697903258787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139237146905040465268839191 208855720357560697903258787)
  ·
    refine ⟨313283580536341046854888181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208855720357560697903258787 313283580536341046854888181)
    ·
      refine ⟨29370335675281973142645767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 313283580536341046854888181 29370335675281973142645767)
      ·
        refine ⟨44055503512922959713968651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29370335675281973142645767 44055503512922959713968651)
        ·
          refine ⟨66083255269384439570952977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44055503512922959713968651 66083255269384439570952977)
          ·
            refine ⟨49562441452038329678214733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66083255269384439570952977 49562441452038329678214733)
            ·
              refine ⟨18585915544514373629330525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49562441452038329678214733 18585915544514373629330525)
              ·
                refine ⟨6969718329192890110998947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18585915544514373629330525 6969718329192890110998947)
                ·
                  refine ⟨10454577493789335166498421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6969718329192890110998947 10454577493789335166498421)
                  ·
                    refine ⟨980116640042750171859227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10454577493789335166498421 980116640042750171859227)
                    ·
                      rfl

theorem cell23_5726311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_5726311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726311 prefixEnd_5726311 := by exact prefixLift 5726311
  have htrace : WordTrace (prefixWord ++ tailWord_5726311) baseStart_5726311 baseEnd_5726311 := by
    simpa [prefixWord, tailWord_5726311, baseEnd_5726311] using wordTrace_append hprefix tailTrace_5726311
  have hstable : (prefixWord ++ tailWord_5726311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726311).length < 2 ^ (prefixWord ++ tailWord_5726311).sum := by decide
  have hdescent : baseEnd_5726311 < baseStart_5726311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726318 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_5726318 : Nat := 118140960795 + 5726318 * 2 ^ 59
def prefixEnd_5726318 : Nat := 4983230072969 + 3 ^ 40 * 5726318 * 2
def baseEnd_5726318 : Nat := 2940353514492831988190149

theorem tailTrace_5726318 : CollatzResearch.WordTrace tailWord_5726318 prefixEnd_5726318 2940353514492831988190149 := by
  unfold tailWord_5726318
  simp only [CollatzResearch.WordTrace]
  refine ⟨26106996958566917262345451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139237317112356892065842405 26106996958566917262345451)
  ·
    refine ⟨39160495437850375893518177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26106996958566917262345451 39160495437850375893518177)
    ·
      refine ⟨29370371578387781920138633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39160495437850375893518177 29370371578387781920138633)
      ·
        refine ⟨22027778683790836440103975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29370371578387781920138633 22027778683790836440103975)
        ·
          refine ⟨33041668025686254660155963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22027778683790836440103975 33041668025686254660155963)
          ·
            refine ⟨49562502038529381990233945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33041668025686254660155963 49562502038529381990233945)
            ·
              refine ⟨37171876528897036492675459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49562502038529381990233945 37171876528897036492675459)
              ·
                refine ⟨55757814793345554739013189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37171876528897036492675459 55757814793345554739013189)
                ·
                  refine ⟨10454590273752291513564973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55757814793345554739013189 10454590273752291513564973)
                  ·
                    refine ⟨3920471352657109317586865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10454590273752291513564973 3920471352657109317586865)
                    ·
                      refine ⟨2940353514492831988190149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920471352657109317586865 2940353514492831988190149)
                      ·
                        rfl

theorem cell23_5726318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_5726318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726318 prefixEnd_5726318 := by exact prefixLift 5726318
  have htrace : WordTrace (prefixWord ++ tailWord_5726318) baseStart_5726318 baseEnd_5726318 := by
    simpa [prefixWord, tailWord_5726318, baseEnd_5726318] using wordTrace_append hprefix tailTrace_5726318
  have hstable : (prefixWord ++ tailWord_5726318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726318).length < 2 ^ (prefixWord ++ tailWord_5726318).sum := by decide
  have hdescent : baseEnd_5726318 < baseStart_5726318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726341 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 1, 6]
def baseStart_5726341 : Nat := 118140960795 + 5726341 * 2 ^ 59
def prefixEnd_5726341 : Nat := 4983230072969 + 3 ^ 40 * 5726341 * 2
def baseEnd_5726341 : Nat := 980121774849295132734181

theorem tailTrace_5726341 : CollatzResearch.WordTrace tailWord_5726341 prefixEnd_5726341 980121774849295132734181 := by
  unfold tailWord_5726341
  simp only [CollatzResearch.WordTrace]
  refine ⟨208856814547452013026850877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139237876364968008684567251 208856814547452013026850877)
  ·
    refine ⟨78321305455294504885069079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208856814547452013026850877 78321305455294504885069079)
    ·
      refine ⟨117481958182941757327603619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78321305455294504885069079 117481958182941757327603619)
      ·
        refine ⟨176222937274412635991405429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117481958182941757327603619 176222937274412635991405429)
        ·
          refine ⟨16520900369476184624194259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176222937274412635991405429 16520900369476184624194259)
          ·
            refine ⟨24781350554214276936291389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16520900369476184624194259 24781350554214276936291389)
            ·
              refine ⟨9293006457830353851109271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24781350554214276936291389 9293006457830353851109271)
              ·
                refine ⟨13939509686745530776663907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9293006457830353851109271 13939509686745530776663907)
                ·
                  refine ⟨20909264530118296164995861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13939509686745530776663907 20909264530118296164995861)
                  ·
                    refine ⟨980121774849295132734181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20909264530118296164995861 980121774849295132734181)
                    ·
                      rfl

theorem cell23_5726341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_5726341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726341 prefixEnd_5726341 := by exact prefixLift 5726341
  have htrace : WordTrace (prefixWord ++ tailWord_5726341) baseStart_5726341 baseEnd_5726341 := by
    simpa [prefixWord, tailWord_5726341, baseEnd_5726341] using wordTrace_append hprefix tailTrace_5726341
  have hstable : (prefixWord ++ tailWord_5726341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726341).length < 2 ^ (prefixWord ++ tailWord_5726341).sum := by decide
  have hdescent : baseEnd_5726341 < baseStart_5726341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726359 : List Nat := [1, 1, 3, 3, 5, 1, 1, 3, 1, 1, 3]
def baseStart_5726359 : Nat := 118140960795 + 5726359 * 2 ^ 59
def prefixEnd_5726359 : Nat := 4983230072969 + 3 ^ 40 * 5726359 * 2
def baseEnd_5726359 : Nat := 2940374567199666327777461

theorem tailTrace_5726359 : CollatzResearch.WordTrace tailWord_5726359 prefixEnd_5726359 2940374567199666327777461 := by
  unfold tailWord_5726359
  simp only [CollatzResearch.WordTrace]
  refine ⟨208857471061386802101006131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139238314040924534734004087 208857471061386802101006131)
  ·
    refine ⟨313286206592080203151509197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208857471061386802101006131 313286206592080203151509197)
    ·
      refine ⟨117482327472030076181815949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313286206592080203151509197 117482327472030076181815949)
      ·
        refine ⟨44055872802011278568180981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117482327472030076181815949 44055872802011278568180981)
        ·
          refine ⟨4130238075188557365766967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44055872802011278568180981 4130238075188557365766967)
          ·
            refine ⟨6195357112782836048650451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130238075188557365766967 6195357112782836048650451)
            ·
              refine ⟨9293035669174254072975677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6195357112782836048650451 9293035669174254072975677)
              ·
                refine ⟨3484888375940345277365879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9293035669174254072975677 3484888375940345277365879)
                ·
                  refine ⟨5227332563910517916048819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3484888375940345277365879 5227332563910517916048819)
                  ·
                    refine ⟨7840998845865776874073229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5227332563910517916048819 7840998845865776874073229)
                    ·
                      refine ⟨2940374567199666327777461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7840998845865776874073229 2940374567199666327777461)
                      ·
                        rfl

theorem cell23_5726359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_5726359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726359 prefixEnd_5726359 := by exact prefixLift 5726359
  have htrace : WordTrace (prefixWord ++ tailWord_5726359) baseStart_5726359 baseEnd_5726359 := by
    simpa [prefixWord, tailWord_5726359, baseEnd_5726359] using wordTrace_append hprefix tailTrace_5726359
  have hstable : (prefixWord ++ tailWord_5726359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726359).length < 2 ^ (prefixWord ++ tailWord_5726359).sum := by decide
  have hdescent : baseEnd_5726359 < baseStart_5726359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726368 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 3]
def baseStart_5726368 : Nat := 118140960795 + 5726368 * 2 ^ 59
def prefixEnd_5726368 : Nat := 4983230072969 + 3 ^ 40 * 5726368 * 2
def baseEnd_5726368 : Nat := 2940379188525556792564919

theorem tailTrace_5726368 : CollatzResearch.WordTrace tailWord_5726368 prefixEnd_5726368 2940379188525556792564919 := by
  unfold tailWord_5726368
  simp only [CollatzResearch.WordTrace]
  refine ⟨104428899659177098319041879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139238532878902797758722505 104428899659177098319041879)
  ·
    refine ⟨156643349488765647478562819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104428899659177098319041879 156643349488765647478562819)
    ·
      refine ⟨234965024233148471217844229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156643349488765647478562819 234965024233148471217844229)
      ·
        refine ⟨44055942043715338353345793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234965024233148471217844229 44055942043715338353345793)
        ·
          refine ⟨33041956532786503765009345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44055942043715338353345793 33041956532786503765009345)
          ·
            refine ⟨24781467399589877823757009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33041956532786503765009345 24781467399589877823757009)
            ·
              refine ⟨18586100549692408367817757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24781467399589877823757009 18586100549692408367817757)
              ·
                refine ⟨6969787706134653137931659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18586100549692408367817757 6969787706134653137931659)
                ·
                  refine ⟨10454681559201979706897489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6969787706134653137931659 10454681559201979706897489)
                  ·
                    refine ⟨7841011169401484780173117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10454681559201979706897489 7841011169401484780173117)
                    ·
                      refine ⟨2940379188525556792564919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7841011169401484780173117 2940379188525556792564919)
                      ·
                        rfl

theorem cell23_5726368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_5726368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726368 prefixEnd_5726368 := by exact prefixLift 5726368
  have htrace : WordTrace (prefixWord ++ tailWord_5726368) baseStart_5726368 baseEnd_5726368 := by
    simpa [prefixWord, tailWord_5726368, baseEnd_5726368] using wordTrace_append hprefix tailTrace_5726368
  have hstable : (prefixWord ++ tailWord_5726368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726368).length < 2 ^ (prefixWord ++ tailWord_5726368).sum := by decide
  have hdescent : baseEnd_5726368 < baseStart_5726368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726402 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_5726402 : Nat := 118140960795 + 5726402 * 2 ^ 59
def prefixEnd_5726402 : Nat := 4983230072969 + 3 ^ 40 * 5726402 * 2
def baseEnd_5726402 : Nat := 2940396646867809659539763

theorem tailTrace_5726402 : CollatzResearch.WordTrace tailWord_5726402 prefixEnd_5726402 2940396646867809659539763 := by
  unfold tailWord_5726402
  simp only [CollatzResearch.WordTrace]
  refine ⟨52214759850057755111205365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139239359600154013629880973 52214759850057755111205365)
  ·
    refine ⟨4895133735942914541675503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52214759850057755111205365 4895133735942914541675503)
    ·
      refine ⟨7342700603914371812513255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4895133735942914541675503 7342700603914371812513255)
      ·
        refine ⟨11014050905871557718769883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7342700603914371812513255 11014050905871557718769883)
        ·
          refine ⟨16521076358807336578154825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11014050905871557718769883 16521076358807336578154825)
          ·
            refine ⟨12390807269105502433616119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16521076358807336578154825 12390807269105502433616119)
            ·
              refine ⟨18586210903658253650424179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12390807269105502433616119 18586210903658253650424179)
              ·
                refine ⟨27879316355487380475636269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18586210903658253650424179 27879316355487380475636269)
                ·
                  refine ⟨10454743633307767678363601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27879316355487380475636269 10454743633307767678363601)
                  ·
                    refine ⟨7841057724980825758772701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10454743633307767678363601 7841057724980825758772701)
                    ·
                      refine ⟨2940396646867809659539763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7841057724980825758772701 2940396646867809659539763)
                      ·
                        rfl

theorem cell23_5726402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_5726402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726402 prefixEnd_5726402 := by exact prefixLift 5726402
  have htrace : WordTrace (prefixWord ++ tailWord_5726402) baseStart_5726402 baseEnd_5726402 := by
    simpa [prefixWord, tailWord_5726402, baseEnd_5726402] using wordTrace_append hprefix tailTrace_5726402
  have hstable : (prefixWord ++ tailWord_5726402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726402).length < 2 ^ (prefixWord ++ tailWord_5726402).sum := by decide
  have hdescent : baseEnd_5726402 < baseStart_5726402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726451 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 4]
def baseStart_5726451 : Nat := 118140960795 + 5726451 * 2 ^ 59
def prefixEnd_5726451 : Nat := 4983230072969 + 3 ^ 40 * 5726451 * 2
def baseEnd_5726451 : Nat := 2940421807419879967827037

theorem tailTrace_5726451 : CollatzResearch.WordTrace tailWord_5726451 prefixEnd_5726451 2940421807419879967827037 := by
  unfold tailWord_5726451
  simp only [CollatzResearch.WordTrace]
  refine ⟨208860826577053501813355207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139240551051369001208903471 208860826577053501813355207)
  ·
    refine ⟨313291239865580252720032811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208860826577053501813355207 313291239865580252720032811)
    ·
      refine ⟨469936859798370379080049217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313291239865580252720032811 469936859798370379080049217)
      ·
        refine ⟨352452644848777784310036913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469936859798370379080049217 352452644848777784310036913)
        ·
          refine ⟨264339483636583338232527685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352452644848777784310036913 264339483636583338232527685)
          ·
            refine ⟨49563653181859375918598941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264339483636583338232527685 49563653181859375918598941)
            ·
              refine ⟨18586369943197265969474603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49563653181859375918598941 18586369943197265969474603)
              ·
                refine ⟨27879554914795898954211905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18586369943197265969474603 27879554914795898954211905)
                ·
                  refine ⟨20909666186096924215658929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27879554914795898954211905 20909666186096924215658929)
                  ·
                    refine ⟨15682249639572693161744197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20909666186096924215658929 15682249639572693161744197)
                    ·
                      refine ⟨2940421807419879967827037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15682249639572693161744197 2940421807419879967827037)
                      ·
                        rfl

theorem cell23_5726451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_5726451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726451 prefixEnd_5726451 := by exact prefixLift 5726451
  have htrace : WordTrace (prefixWord ++ tailWord_5726451) baseStart_5726451 baseEnd_5726451 := by
    simpa [prefixWord, tailWord_5726451, baseEnd_5726451] using wordTrace_append hprefix tailTrace_5726451
  have hstable : (prefixWord ++ tailWord_5726451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726451).length < 2 ^ (prefixWord ++ tailWord_5726451).sum := by decide
  have hdescent : baseEnd_5726451 < baseStart_5726451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726491 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 2, 5]
def baseStart_5726491 : Nat := 118140960795 + 5726491 * 2 ^ 59
def prefixEnd_5726491 : Nat := 4983230072969 + 3 ^ 40 * 5726491 * 2
def baseEnd_5726491 : Nat := 980147448882019937108951

theorem tailTrace_5726491 : CollatzResearch.WordTrace tailWord_5726491 prefixEnd_5726491 980147448882019937108951 := by
  unfold tailWord_5726491
  simp only [CollatzResearch.WordTrace]
  refine ⟨208862285496908588644811327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139241523664605725763207551 208862285496908588644811327)
  ·
    refine ⟨313293428245362882967216991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208862285496908588644811327 313293428245362882967216991)
    ·
      refine ⟨469940142368044324450825487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313293428245362882967216991 469940142368044324450825487)
      ·
        refine ⟨704910213552066486676238231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469940142368044324450825487 704910213552066486676238231)
        ·
          refine ⟨1057365320328099730014357347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704910213552066486676238231 1057365320328099730014357347)
          ·
            refine ⟨1586047980492149595021536021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057365320328099730014357347 1586047980492149595021536021)
            ·
              refine ⟨74345999085569512266634501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1586047980492149595021536021 74345999085569512266634501)
              ·
                refine ⟨13939874828544283549993969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74345999085569512266634501 13939874828544283549993969)
                ·
                  refine ⟨10454906121408212662495477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13939874828544283549993969 10454906121408212662495477)
                  ·
                    refine ⟨980147448882019937108951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10454906121408212662495477 980147448882019937108951)
                    ·
                      rfl

theorem cell23_5726491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 5].length) (baseStart_5726491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726491 prefixEnd_5726491 := by exact prefixLift 5726491
  have htrace : WordTrace (prefixWord ++ tailWord_5726491) baseStart_5726491 baseEnd_5726491 := by
    simpa [prefixWord, tailWord_5726491, baseEnd_5726491] using wordTrace_append hprefix tailTrace_5726491
  have hstable : (prefixWord ++ tailWord_5726491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726491).length < 2 ^ (prefixWord ++ tailWord_5726491).sum := by decide
  have hdescent : baseEnd_5726491 < baseStart_5726491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726506 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_5726506 : Nat := 118140960795 + 5726506 * 2 ^ 59
def prefixEnd_5726506 : Nat := 4983230072969 + 3 ^ 40 * 5726506 * 2
def baseEnd_5726506 : Nat := 2940450048855877252639285

theorem tailTrace_5726506 : CollatzResearch.WordTrace tailWord_5726506 prefixEnd_5726506 2940450048855877252639285 := by
  unfold tailWord_5726506
  simp only [CollatzResearch.WordTrace]
  refine ⟨52215708147963561551651843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139241888394569497471071581 52215708147963561551651843)
  ·
    refine ⟨78323562221945342327477765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52215708147963561551651843 78323562221945342327477765)
    ·
      refine ⟨14685667916614751686402081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78323562221945342327477765 14685667916614751686402081)
      ·
        refine ⟨11014250937461063764801561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14685667916614751686402081 11014250937461063764801561)
        ·
          refine ⟨8260688203095797823601171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11014250937461063764801561 8260688203095797823601171)
          ·
            refine ⟨12391032304643696735401757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8260688203095797823601171 12391032304643696735401757)
            ·
              refine ⟨4646637114241386275775659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12391032304643696735401757 4646637114241386275775659)
              ·
                refine ⟨6969955671362079413663489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4646637114241386275775659 6969955671362079413663489)
                ·
                  refine ⟨5227466753521559560247617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6969955671362079413663489 5227466753521559560247617)
                  ·
                    refine ⟨3920600065141169670185713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5227466753521559560247617 3920600065141169670185713)
                    ·
                      refine ⟨2940450048855877252639285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920600065141169670185713 2940450048855877252639285)
                      ·
                        rfl

theorem cell23_5726506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_5726506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726506 prefixEnd_5726506 := by exact prefixLift 5726506
  have htrace : WordTrace (prefixWord ++ tailWord_5726506) baseStart_5726506 baseEnd_5726506 := by
    simpa [prefixWord, tailWord_5726506, baseEnd_5726506] using wordTrace_append hprefix tailTrace_5726506
  have hstable : (prefixWord ++ tailWord_5726506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726506).length < 2 ^ (prefixWord ++ tailWord_5726506).sum := by decide
  have hdescent : baseEnd_5726506 < baseStart_5726506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726511 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 4]
def baseStart_5726511 : Nat := 118140960795 + 5726511 * 2 ^ 59
def prefixEnd_5726511 : Nat := 4983230072969 + 3 ^ 40 * 5726511 * 2
def baseEnd_5726511 : Nat := 2940452616259149733076761

theorem tailTrace_5726511 : CollatzResearch.WordTrace tailWord_5726511 prefixEnd_5726511 2940452616259149733076761 := by
  unfold tailWord_5726511
  simp only [CollatzResearch.WordTrace]
  refine ⟨208863014956836132060539387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139242009971224088040359591 208863014956836132060539387)
  ·
    refine ⟨313294522435254198090809081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208863014956836132060539387 313294522435254198090809081)
    ·
      refine ⟨234970891826440648568106811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313294522435254198090809081 234970891826440648568106811)
      ·
        refine ⟨352456337739660972852160217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234970891826440648568106811 352456337739660972852160217)
        ·
          refine ⟨264342253304745729639120163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352456337739660972852160217 264342253304745729639120163)
          ·
            refine ⟨396513379957118594458680245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264342253304745729639120163 396513379957118594458680245)
            ·
              refine ⟨37173129370979868230501273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 396513379957118594458680245 37173129370979868230501273)
              ·
                refine ⟨27879847028234901172875955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37173129370979868230501273 27879847028234901172875955)
                ·
                  refine ⟨41819770542352351759313933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27879847028234901172875955 41819770542352351759313933)
                  ·
                    refine ⟨15682413953382131909742725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41819770542352351759313933 15682413953382131909742725)
                    ·
                      refine ⟨2940452616259149733076761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15682413953382131909742725 2940452616259149733076761)
                      ·
                        rfl

theorem cell23_5726511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_5726511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726511 prefixEnd_5726511 := by exact prefixLift 5726511
  have htrace : WordTrace (prefixWord ++ tailWord_5726511) baseStart_5726511 baseEnd_5726511 := by
    simpa [prefixWord, tailWord_5726511, baseEnd_5726511] using wordTrace_append hprefix tailTrace_5726511
  have hstable : (prefixWord ++ tailWord_5726511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726511).length < 2 ^ (prefixWord ++ tailWord_5726511).sum := by decide
  have hdescent : baseEnd_5726511 < baseStart_5726511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726528 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 4, 4, 2]
def baseStart_5726528 : Nat := 118140960795 + 5726528 * 2 ^ 59
def prefixEnd_5726528 : Nat := 4983230072969 + 3 ^ 40 * 5726528 * 2
def baseEnd_5726528 : Nat := 2940461345430276166564183

theorem tailTrace_5726528 : CollatzResearch.WordTrace tailWord_5726528 prefixEnd_5726528 2940461345430276166564183 := by
  unfold tailWord_5726528
  simp only [CollatzResearch.WordTrace]
  refine ⟨104431817498887271981954119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139242423331849695975938825 104431817498887271981954119)
  ·
    refine ⟨156647726248330907972931179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104431817498887271981954119 156647726248330907972931179)
    ·
      refine ⟨234971589372496361959396769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156647726248330907972931179 234971589372496361959396769)
      ·
        refine ⟨176228692029372271469547577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234971589372496361959396769 176228692029372271469547577)
        ·
          refine ⟨132171519022029203602160683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176228692029372271469547577 132171519022029203602160683)
          ·
            refine ⟨198257278533043805403241025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132171519022029203602160683 198257278533043805403241025)
            ·
              refine ⟨148692958899782854052430769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198257278533043805403241025 148692958899782854052430769)
              ·
                refine ⟨111519719174837140539323077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148692958899782854052430769 111519719174837140539323077)
                ·
                  refine ⟨20909947345281963851123077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111519719174837140539323077 20909947345281963851123077)
                  ·
                    refine ⟨3920615127240368222085577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20909947345281963851123077 3920615127240368222085577)
                    ·
                      refine ⟨2940461345430276166564183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920615127240368222085577 2940461345430276166564183)
                      ·
                        rfl

theorem cell23_5726528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 4, 2].length) (baseStart_5726528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726528 prefixEnd_5726528 := by exact prefixLift 5726528
  have htrace : WordTrace (prefixWord ++ tailWord_5726528) baseStart_5726528 baseEnd_5726528 := by
    simpa [prefixWord, tailWord_5726528, baseEnd_5726528] using wordTrace_append hprefix tailTrace_5726528
  have hstable : (prefixWord ++ tailWord_5726528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726528).length < 2 ^ (prefixWord ++ tailWord_5726528).sum := by decide
  have hdescent : baseEnd_5726528 < baseStart_5726528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726529 : List Nat := [1, 2, 5, 2, 3, 1, 1, 3, 5]
def baseStart_5726529 : Nat := 118140960795 + 5726529 * 2 ^ 59
def prefixEnd_5726529 : Nat := 4983230072969 + 3 ^ 40 * 5726529 * 2
def baseEnd_5726529 : Nat := 326717984323436740294631

theorem tailTrace_5726529 : CollatzResearch.WordTrace tailWord_5726529 prefixEnd_5726529 326717984323436740294631 := by
  unfold tailWord_5726529
  simp only [CollatzResearch.WordTrace]
  refine ⟨208863671470770921134694641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139242447647180614089796427 208863671470770921134694641)
  ·
    refine ⟨156647753603078190851020981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208863671470770921134694641 156647753603078190851020981)
    ·
      refine ⟨14685726900288580392283217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156647753603078190851020981 14685726900288580392283217)
      ·
        refine ⟨11014295175216435294212413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14685726900288580392283217 11014295175216435294212413)
        ·
          refine ⟨4130360690706163235329655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11014295175216435294212413 4130360690706163235329655)
          ·
            refine ⟨6195541036059244852994483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130360690706163235329655 6195541036059244852994483)
            ·
              refine ⟨9293311554088867279491725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6195541036059244852994483 9293311554088867279491725)
              ·
                refine ⟨3484991832783325229809397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9293311554088867279491725 3484991832783325229809397)
                ·
                  refine ⟨326717984323436740294631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3484991832783325229809397 326717984323436740294631)
                  ·
                    rfl

theorem cell23_5726529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 5].length) (baseStart_5726529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726529 prefixEnd_5726529 := by exact prefixLift 5726529
  have htrace : WordTrace (prefixWord ++ tailWord_5726529) baseStart_5726529 baseEnd_5726529 := by
    simpa [prefixWord, tailWord_5726529, baseEnd_5726529] using wordTrace_append hprefix tailTrace_5726529
  have hstable : (prefixWord ++ tailWord_5726529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726529).length < 2 ^ (prefixWord ++ tailWord_5726529).sum := by decide
  have hdescent : baseEnd_5726529 < baseStart_5726529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726551 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 8]
def baseStart_5726551 : Nat := 118140960795 + 5726551 * 2 ^ 59
def prefixEnd_5726551 : Nat := 4983230072969 + 3 ^ 40 * 5726551 * 2
def baseEnd_5726551 : Nat := 326719239498369952952953

theorem tailTrace_5726551 : CollatzResearch.WordTrace tailWord_5726551 prefixEnd_5726551 326719239498369952952953 := by
  unfold tailWord_5726551
  simp only [CollatzResearch.WordTrace]
  refine ⟨208864473876691218891995507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139242982584460812594663671 208864473876691218891995507)
  ·
    refine ⟨313296710815036828337993261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208864473876691218891995507 313296710815036828337993261)
    ·
      refine ⟨117486266555638810626747473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313296710815036828337993261 117486266555638810626747473)
      ·
        refine ⟨88114699916729107970060605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117486266555638810626747473 88114699916729107970060605)
        ·
          refine ⟨33043012468773415488772727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88114699916729107970060605 33043012468773415488772727)
          ·
            refine ⟨49564518703160123233159091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33043012468773415488772727 49564518703160123233159091)
            ·
              refine ⟨74346778054740184849738637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49564518703160123233159091 74346778054740184849738637)
              ·
                refine ⟨27880041770527569318651989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74346778054740184849738637 27880041770527569318651989)
                ·
                  refine ⟨326719239498369952952953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27880041770527569318651989 326719239498369952952953)
                  ·
                    rfl

theorem cell23_5726551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 8].length) (baseStart_5726551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726551 prefixEnd_5726551 := by exact prefixLift 5726551
  have htrace : WordTrace (prefixWord ++ tailWord_5726551) baseStart_5726551 baseEnd_5726551 := by
    simpa [prefixWord, tailWord_5726551, baseEnd_5726551] using wordTrace_append hprefix tailTrace_5726551
  have hstable : (prefixWord ++ tailWord_5726551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726551).length < 2 ^ (prefixWord ++ tailWord_5726551).sum := by decide
  have hdescent : baseEnd_5726551 < baseStart_5726551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726602 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 6]
def baseStart_5726602 : Nat := 118140960795 + 5726602 * 2 ^ 59
def prefixEnd_5726602 : Nat := 4983230072969 + 3 ^ 40 * 5726602 * 2
def baseEnd_5726602 : Nat := 326722149222078764115427

theorem tailTrace_5726602 : CollatzResearch.WordTrace tailWord_5726602 prefixEnd_5726602 326722149222078764115427 := by
  unfold tailWord_5726602
  simp only [CollatzResearch.WordTrace]
  refine ⟨52216583499876613650525515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139244222666337636401401373 52216583499876613650525515)
  ·
    refine ⟨78324875249814920475788273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52216583499876613650525515 78324875249814920475788273)
    ·
      refine ⟨58743656437361190356841205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78324875249814920475788273 58743656437361190356841205)
      ·
        refine ⟨5507217791002611595953863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58743656437361190356841205 5507217791002611595953863)
        ·
          refine ⟨8260826686503917393930795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5507217791002611595953863 8260826686503917393930795)
          ·
            refine ⟨12391240029755876090896193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8260826686503917393930795 12391240029755876090896193)
            ·
              refine ⟨9293430022316907068172145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12391240029755876090896193 9293430022316907068172145)
              ·
                refine ⟨6970072516737680301129109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9293430022316907068172145 6970072516737680301129109)
                ·
                  refine ⟨326722149222078764115427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6970072516737680301129109 326722149222078764115427)
                  ·
                    rfl

theorem cell23_5726602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_5726602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726602 prefixEnd_5726602 := by exact prefixLift 5726602
  have htrace : WordTrace (prefixWord ++ tailWord_5726602) baseStart_5726602 baseEnd_5726602 := by
    simpa [prefixWord, tailWord_5726602, baseEnd_5726602] using wordTrace_append hprefix tailTrace_5726602
  have hstable : (prefixWord ++ tailWord_5726602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726602).length < 2 ^ (prefixWord ++ tailWord_5726602).sum := by decide
  have hdescent : baseEnd_5726602 < baseStart_5726602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726606 : List Nat := [4, 1, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_5726606 : Nat := 118140960795 + 5726606 * 2 ^ 59
def prefixEnd_5726606 : Nat := 4983230072969 + 3 ^ 40 * 5726606 * 2
def baseEnd_5726606 : Nat := 980167132307108953796275

theorem tailTrace_5726606 : CollatzResearch.WordTrace tailWord_5726606 prefixEnd_5726606 980167132307108953796275 := by
  unfold tailWord_5726606
  simp only [CollatzResearch.WordTrace]
  refine ⟨26108309986436495410655959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139244319927661308856831781 26108309986436495410655959)
  ·
    refine ⟨39162464979654743115983939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26108309986436495410655959 39162464979654743115983939)
    ·
      refine ⟨58743697469482114673975909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39162464979654743115983939 58743697469482114673975909)
      ·
        refine ⟨11014443275527896501370483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58743697469482114673975909 11014443275527896501370483)
        ·
          refine ⟨16521664913291844752055725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11014443275527896501370483 16521664913291844752055725)
          ·
            refine ⟨6195624342484441782020897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16521664913291844752055725 6195624342484441782020897)
            ·
              refine ⟨4646718256863331336515673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6195624342484441782020897 4646718256863331336515673)
              ·
                refine ⟨3485038692647498502386755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4646718256863331336515673 3485038692647498502386755)
                ·
                  refine ⟨5227558038971247753580133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485038692647498502386755 5227558038971247753580133)
                  ·
                    refine ⟨980167132307108953796275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227558038971247753580133 980167132307108953796275)
                    ·
                      rfl

theorem cell23_5726606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_5726606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726606 prefixEnd_5726606 := by exact prefixLift 5726606
  have htrace : WordTrace (prefixWord ++ tailWord_5726606) baseStart_5726606 baseEnd_5726606 := by
    simpa [prefixWord, tailWord_5726606, baseEnd_5726606] using wordTrace_append hprefix tailTrace_5726606
  have hstable : (prefixWord ++ tailWord_5726606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726606).length < 2 ^ (prefixWord ++ tailWord_5726606).sum := by decide
  have hdescent : baseEnd_5726606 < baseStart_5726606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726628 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_5726628 : Nat := 118140960795 + 5726628 * 2 ^ 59
def prefixEnd_5726628 : Nat := 4983230072969 + 3 ^ 40 * 5726628 * 2
def baseEnd_5726628 : Nat := 980170897831908591771241

theorem tailTrace_5726628 : CollatzResearch.WordTrace tailWord_5726628 prefixEnd_5726628 980170897831908591771241 := by
  unfold tailWord_5726628
  simp only [CollatzResearch.WordTrace]
  refine ⟨104433641148706130521274269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139244854864941507361699025 104433641148706130521274269)
  ·
    refine ⟨39162615430764798945477851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104433641148706130521274269 39162615430764798945477851)
    ·
      refine ⟨58743923146147198418216777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39162615430764798945477851 58743923146147198418216777)
      ·
        refine ⟨44057942359610398813662583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58743923146147198418216777 44057942359610398813662583)
        ·
          refine ⟨66086913539415598220493875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44057942359610398813662583 66086913539415598220493875)
          ·
            refine ⟨99130370309123397330740813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66086913539415598220493875 99130370309123397330740813)
            ·
              refine ⟨37173888865921273999027805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99130370309123397330740813 37173888865921273999027805)
              ·
                refine ⟨13940208324720477749635427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37173888865921273999027805 13940208324720477749635427)
                ·
                  refine ⟨20910312487080716624453141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13940208324720477749635427 20910312487080716624453141)
                  ·
                    refine ⟨980170897831908591771241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20910312487080716624453141 980170897831908591771241)
                    ·
                      rfl

theorem cell23_5726628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_5726628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726628 prefixEnd_5726628 := by exact prefixLift 5726628
  have htrace : WordTrace (prefixWord ++ tailWord_5726628) baseStart_5726628 baseEnd_5726628 := by
    simpa [prefixWord, tailWord_5726628, baseEnd_5726628] using wordTrace_append hprefix tailTrace_5726628
  have hstable : (prefixWord ++ tailWord_5726628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726628).length < 2 ^ (prefixWord ++ tailWord_5726628).sum := by decide
  have hdescent : baseEnd_5726628 < baseStart_5726628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726652 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_5726652 : Nat := 118140960795 + 5726652 * 2 ^ 59
def prefixEnd_5726652 : Nat := 4983230072969 + 3 ^ 40 * 5726652 * 2
def baseEnd_5726652 : Nat := 2940525017031433681413613

theorem tailTrace_5726652 : CollatzResearch.WordTrace tailWord_5726652 prefixEnd_5726652 2940525017031433681413613 := by
  unfold tailWord_5726652
  simp only [CollatzResearch.WordTrace]
  refine ⟨104434078824662656570711105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139245438432883542094281473 104434078824662656570711105)
  ·
    refine ⟨78325559118496992428033329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104434078824662656570711105 78325559118496992428033329)
    ·
      refine ⟨58744169338872744321024997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78325559118496992428033329 58744169338872744321024997)
      ·
        refine ⟨11014531751038639560192187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58744169338872744321024997 11014531751038639560192187)
        ·
          refine ⟨16521797626557959340288281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11014531751038639560192187 16521797626557959340288281)
          ·
            refine ⟨12391348219918469505216211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16521797626557959340288281 12391348219918469505216211)
            ·
              refine ⟨18587022329877704257824317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12391348219918469505216211 18587022329877704257824317)
              ·
                refine ⟨6970133373704139096684119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18587022329877704257824317 6970133373704139096684119)
                ·
                  refine ⟨10455200060556208645026179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970133373704139096684119 10455200060556208645026179)
                  ·
                    refine ⟨15682800090834312967539269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10455200060556208645026179 15682800090834312967539269)
                    ·
                      refine ⟨2940525017031433681413613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15682800090834312967539269 2940525017031433681413613)
                      ·
                        rfl

theorem cell23_5726652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_5726652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726652 prefixEnd_5726652 := by exact prefixLift 5726652
  have htrace : WordTrace (prefixWord ++ tailWord_5726652) baseStart_5726652 baseEnd_5726652 := by
    simpa [prefixWord, tailWord_5726652, baseEnd_5726652] using wordTrace_append hprefix tailTrace_5726652
  have hstable : (prefixWord ++ tailWord_5726652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726652).length < 2 ^ (prefixWord ++ tailWord_5726652).sum := by decide
  have hdescent : baseEnd_5726652 < baseStart_5726652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726702 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_5726702 : Nat := 118140960795 + 5726702 * 2 ^ 59
def prefixEnd_5726702 : Nat := 4983230072969 + 3 ^ 40 * 5726702 * 2
def baseEnd_5726702 : Nat := 2940550691064158485788383

theorem tailTrace_5726702 : CollatzResearch.WordTrace tailWord_5726702 prefixEnd_5726702 2940550691064158485788383 := by
  unfold tailWord_5726702
  simp only [CollatzResearch.WordTrace]
  refine ⟨26108747662393021460092795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139246654199429447787161573 26108747662393021460092795)
  ·
    refine ⟨39163121493589532190139193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26108747662393021460092795 39163121493589532190139193)
    ·
      refine ⟨29372341120192149142604395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39163121493589532190139193 29372341120192149142604395)
      ·
        refine ⟨44058511680288223713906593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29372341120192149142604395 44058511680288223713906593)
        ·
          refine ⟨33043883760216167785429945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44058511680288223713906593 33043883760216167785429945)
          ·
            refine ⟨24782912820162125839072459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33043883760216167785429945 24782912820162125839072459)
            ·
              refine ⟨37174369230243188758608689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24782912820162125839072459 37174369230243188758608689)
              ·
                refine ⟨27880776922682391568956517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37174369230243188758608689 27880776922682391568956517)
                ·
                  refine ⟨5227645673002948419179347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27880776922682391568956517 5227645673002948419179347)
                  ·
                    refine ⟨7841468509504422628769021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5227645673002948419179347 7841468509504422628769021)
                    ·
                      refine ⟨2940550691064158485788383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7841468509504422628769021 2940550691064158485788383)
                      ·
                        rfl

theorem cell23_5726702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_5726702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726702 prefixEnd_5726702 := by exact prefixLift 5726702
  have htrace : WordTrace (prefixWord ++ tailWord_5726702) baseStart_5726702 baseEnd_5726702 := by
    simpa [prefixWord, tailWord_5726702, baseEnd_5726702] using wordTrace_append hprefix tailTrace_5726702
  have hstable : (prefixWord ++ tailWord_5726702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726702).length < 2 ^ (prefixWord ++ tailWord_5726702).sum := by decide
  have hdescent : baseEnd_5726702 < baseStart_5726702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726712 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 1, 3, 2]
def baseStart_5726712 : Nat := 118140960795 + 5726712 * 2 ^ 59
def prefixEnd_5726712 : Nat := 4983230072969 + 3 ^ 40 * 5726712 * 2
def baseEnd_5726712 : Nat := 2940555825870703446663337

theorem tailTrace_5726712 : CollatzResearch.WordTrace tailWord_5726712 prefixEnd_5726712 2940555825870703446663337 := by
  unfold tailWord_5726712
  simp only [CollatzResearch.WordTrace]
  refine ⟨104435173014553971694303195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139246897352738628925737593 104435173014553971694303195)
  ·
    refine ⟨156652759521830957541454793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104435173014553971694303195 156652759521830957541454793)
    ·
      refine ⟨117489569641373218156091095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156652759521830957541454793 117489569641373218156091095)
      ·
        refine ⟨176234354462059827234136643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117489569641373218156091095 176234354462059827234136643)
        ·
          refine ⟨264351531693089740851204965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176234354462059827234136643 264351531693089740851204965)
          ·
            refine ⟨49565912192454326409600931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264351531693089740851204965 49565912192454326409600931)
            ·
              refine ⟨74348868288681489614401397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49565912192454326409600931 74348868288681489614401397)
              ·
                refine ⟨6970206402063889651350131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74348868288681489614401397 6970206402063889651350131)
                ·
                  refine ⟨10455309603095834477025197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970206402063889651350131 10455309603095834477025197)
                  ·
                    refine ⟨3920741101160937928884449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10455309603095834477025197 3920741101160937928884449)
                    ·
                      refine ⟨2940555825870703446663337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920741101160937928884449 2940555825870703446663337)
                      ·
                        rfl

theorem cell23_5726712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 3, 2].length) (baseStart_5726712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726712 prefixEnd_5726712 := by exact prefixLift 5726712
  have htrace : WordTrace (prefixWord ++ tailWord_5726712) baseStart_5726712 baseEnd_5726712 := by
    simpa [prefixWord, tailWord_5726712, baseEnd_5726712] using wordTrace_append hprefix tailTrace_5726712
  have hstable : (prefixWord ++ tailWord_5726712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726712).length < 2 ^ (prefixWord ++ tailWord_5726712).sum := by decide
  have hdescent : baseEnd_5726712 < baseStart_5726712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726728 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_5726728 : Nat := 118140960795 + 5726728 * 2 ^ 59
def prefixEnd_5726728 : Nat := 4983230072969 + 3 ^ 40 * 5726728 * 2
def baseEnd_5726728 : Nat := 2940564041561175384063263

theorem tailTrace_5726728 : CollatzResearch.WordTrace tailWord_5726728 prefixEnd_5726728 2940564041561175384063263 := by
  unfold tailWord_5726728
  simp only [CollatzResearch.WordTrace]
  refine ⟨104435464798524989060594419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139247286398033318747459225 104435464798524989060594419)
  ·
    refine ⟨156653197197787483590891629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104435464798524989060594419 156653197197787483590891629)
    ·
      refine ⟨58744948949170306346584361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156653197197787483590891629 58744948949170306346584361)
      ·
        refine ⟨44058711711877729759938271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58744948949170306346584361 44058711711877729759938271)
        ·
          refine ⟨66088067567816594639907407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44058711711877729759938271 66088067567816594639907407)
          ·
            refine ⟨99132101351724891959861111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66088067567816594639907407 99132101351724891959861111)
            ·
              refine ⟨148698152027587337939791667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99132101351724891959861111 148698152027587337939791667)
              ·
                refine ⟨223047228041381006909687501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148698152027587337939791667 223047228041381006909687501)
                ·
                  refine ⟨83642710515517877591132813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223047228041381006909687501 83642710515517877591132813)
                  ·
                    refine ⟨31366016443319204096674805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83642710515517877591132813 31366016443319204096674805)
                    ·
                      refine ⟨2940564041561175384063263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31366016443319204096674805 2940564041561175384063263)
                      ·
                        rfl

theorem cell23_5726728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_5726728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726728 prefixEnd_5726728 := by exact prefixLift 5726728
  have htrace : WordTrace (prefixWord ++ tailWord_5726728) baseStart_5726728 baseEnd_5726728 := by
    simpa [prefixWord, tailWord_5726728, baseEnd_5726728] using wordTrace_append hprefix tailTrace_5726728
  have hstable : (prefixWord ++ tailWord_5726728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726728).length < 2 ^ (prefixWord ++ tailWord_5726728).sum := by decide
  have hdescent : baseEnd_5726728 < baseStart_5726728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726775 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 3]
def baseStart_5726775 : Nat := 118140960795 + 5726775 * 2 ^ 59
def prefixEnd_5726775 : Nat := 4983230072969 + 3 ^ 40 * 5726775 * 2
def baseEnd_5726775 : Nat := 2940588175151936700175547

theorem tailTrace_5726775 : CollatzResearch.WordTrace tailWord_5726775 prefixEnd_5726775 2940588175151936700175547 := by
  unfold tailWord_5726775
  simp only [CollatzResearch.WordTrace]
  refine ⟨208872643827879705148149779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139248429218586470098766519 208872643827879705148149779)
  ·
    refine ⟨313308965741819557722224669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208872643827879705148149779 313308965741819557722224669)
    ·
      refine ⟨117490862153182334145834251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313308965741819557722224669 117490862153182334145834251)
      ·
        refine ⟨176236293229773501218751377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117490862153182334145834251 176236293229773501218751377)
        ·
          refine ⟨132177219922330125914063533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176236293229773501218751377 132177219922330125914063533)
          ·
            refine ⟨49566457470873797217773825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132177219922330125914063533 49566457470873797217773825)
            ·
              refine ⟨37174843103155347913330369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49566457470873797217773825 37174843103155347913330369)
              ·
                refine ⟨27881132327366510934997777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37174843103155347913330369 27881132327366510934997777)
                ·
                  refine ⟨20910849245524883201248333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27881132327366510934997777 20910849245524883201248333)
                  ·
                    refine ⟨7841568467071831200468125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20910849245524883201248333 7841568467071831200468125)
                    ·
                      refine ⟨2940588175151936700175547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7841568467071831200468125 2940588175151936700175547)
                      ·
                        rfl

theorem cell23_5726775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_5726775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726775 prefixEnd_5726775 := by exact prefixLift 5726775
  have htrace : WordTrace (prefixWord ++ tailWord_5726775) baseStart_5726775 baseEnd_5726775 := by
    simpa [prefixWord, tailWord_5726775, baseEnd_5726775] using wordTrace_append hprefix tailTrace_5726775
  have hstable : (prefixWord ++ tailWord_5726775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726775).length < 2 ^ (prefixWord ++ tailWord_5726775).sum := by decide
  have hdescent : baseEnd_5726775 < baseStart_5726775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726802 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_5726802 : Nat := 118140960795 + 5726802 * 2 ^ 59
def prefixEnd_5726802 : Nat := 4983230072969 + 3 ^ 40 * 5726802 * 2
def baseEnd_5726802 : Nat := 2940602039129608094537923

theorem tailTrace_5726802 : CollatzResearch.WordTrace tailWord_5726802 prefixEnd_5726802 2940602039129608094537923 := by
  unfold tailWord_5726802
  simp only [CollatzResearch.WordTrace]
  refine ⟨52218407149695472189845665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139249085732521259172921773 52218407149695472189845665)
  ·
    refine ⟨39163805362271604142384249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52218407149695472189845665 39163805362271604142384249)
    ·
      refine ⟨29372854021703703106788187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39163805362271604142384249 29372854021703703106788187)
      ·
        refine ⟨44059281032555554660182281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29372854021703703106788187 44059281032555554660182281)
        ·
          refine ⟨33044460774416665995136711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44059281032555554660182281 33044460774416665995136711)
          ·
            refine ⟨49566691161624998992705067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33044460774416665995136711 49566691161624998992705067)
            ·
              refine ⟨74350036742437498489057601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49566691161624998992705067 74350036742437498489057601)
              ·
                refine ⟨55762527556828123866793201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74350036742437498489057601 55762527556828123866793201)
                ·
                  refine ⟨41821895667621092900094901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55762527556828123866793201 41821895667621092900094901)
                  ·
                    refine ⟨3920802718839477459383897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41821895667621092900094901 3920802718839477459383897)
                    ·
                      refine ⟨2940602039129608094537923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920802718839477459383897 2940602039129608094537923)
                      ·
                        rfl

theorem cell23_5726802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_5726802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726802 prefixEnd_5726802 := by exact prefixLift 5726802
  have htrace : WordTrace (prefixWord ++ tailWord_5726802) baseStart_5726802 baseEnd_5726802 := by
    simpa [prefixWord, tailWord_5726802, baseEnd_5726802] using wordTrace_append hprefix tailTrace_5726802
  have hstable : (prefixWord ++ tailWord_5726802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726802).length < 2 ^ (prefixWord ++ tailWord_5726802).sum := by decide
  have hdescent : baseEnd_5726802 < baseStart_5726802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726812 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 1, 7]
def baseStart_5726812 : Nat := 118140960795 + 5726812 * 2 ^ 59
def prefixEnd_5726812 : Nat := 4983230072969 + 3 ^ 40 * 5726812 * 2
def baseEnd_5726812 : Nat := 980202391312051018470959

theorem tailTrace_5726812 : CollatzResearch.WordTrace tailWord_5726812 prefixEnd_5726812 980202391312051018470959 := by
  unfold tailWord_5726812
  simp only [CollatzResearch.WordTrace]
  refine ⟨104436996664372830233623345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139249328885830440311497793 104436996664372830233623345)
  ·
    refine ⟨78327747498279622675217509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104436996664372830233623345 78327747498279622675217509)
    ·
      refine ⟨14686452655927429251603283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78327747498279622675217509 14686452655927429251603283)
      ·
        refine ⟨22029678983891143877404925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14686452655927429251603283 22029678983891143877404925)
        ·
          refine ⟨8261129618959178954026847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22029678983891143877404925 8261129618959178954026847)
          ·
            refine ⟨12391694428438768431040271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8261129618959178954026847 12391694428438768431040271)
            ·
              refine ⟨18587541642658152646560407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12391694428438768431040271 18587541642658152646560407)
              ·
                refine ⟨27881312463987228969840611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18587541642658152646560407 27881312463987228969840611)
                ·
                  refine ⟨41821968695980843454760917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27881312463987228969840611 41821968695980843454760917)
                  ·
                    refine ⟨980202391312051018470959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41821968695980843454760917 980202391312051018470959)
                    ·
                      rfl

theorem cell23_5726812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_5726812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726812 prefixEnd_5726812 := by exact prefixLift 5726812
  have htrace : WordTrace (prefixWord ++ tailWord_5726812) baseStart_5726812 baseEnd_5726812 := by
    simpa [prefixWord, tailWord_5726812, baseEnd_5726812] using wordTrace_append hprefix tailTrace_5726812
  have hstable : (prefixWord ++ tailWord_5726812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726812).length < 2 ^ (prefixWord ++ tailWord_5726812).sum := by decide
  have hdescent : baseEnd_5726812 < baseStart_5726812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726814 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_5726814 : Nat := 118140960795 + 5726814 * 2 ^ 59
def prefixEnd_5726814 : Nat := 4983230072969 + 3 ^ 40 * 5726814 * 2
def baseEnd_5726814 : Nat := 2940608200897462047587869

theorem tailTrace_5726814 : CollatzResearch.WordTrace tailWord_5726814 prefixEnd_5726814 2940608200897462047587869 := by
  unfold tailWord_5726814
  simp only [CollatzResearch.WordTrace]
  refine ⟨26109258284342301851102437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139249377516492276539212997 26109258284342301851102437)
  ·
    refine ⟨4895485928314181597081707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26109258284342301851102437 4895485928314181597081707)
    ·
      refine ⟨7343228892471272395622561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4895485928314181597081707 7343228892471272395622561)
      ·
        refine ⟨5507421669353454296716921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7343228892471272395622561 5507421669353454296716921)
        ·
          refine ⟨4130566252015090722537691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5507421669353454296716921 4130566252015090722537691)
          ·
            refine ⟨6195849378022636083806537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130566252015090722537691 6195849378022636083806537)
            ·
              refine ⟨4646887033516977062854903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6195849378022636083806537 4646887033516977062854903)
              ·
                refine ⟨6970330550275465594282355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4646887033516977062854903 6970330550275465594282355)
                ·
                  refine ⟨10455495825413198391423533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970330550275465594282355 10455495825413198391423533)
                  ·
                    refine ⟨3920810934529949396783825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10455495825413198391423533 3920810934529949396783825)
                    ·
                      refine ⟨2940608200897462047587869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920810934529949396783825 2940608200897462047587869)
                      ·
                        rfl

theorem cell23_5726814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_5726814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726814 prefixEnd_5726814 := by exact prefixLift 5726814
  have htrace : WordTrace (prefixWord ++ tailWord_5726814) baseStart_5726814 baseEnd_5726814 := by
    simpa [prefixWord, tailWord_5726814, baseEnd_5726814] using wordTrace_append hprefix tailTrace_5726814
  have hstable : (prefixWord ++ tailWord_5726814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726814).length < 2 ^ (prefixWord ++ tailWord_5726814).sum := by decide
  have hdescent : baseEnd_5726814 < baseStart_5726814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726825 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 7, 4]
def baseStart_5726825 : Nat := 118140960795 + 5726825 * 2 ^ 59
def prefixEnd_5726825 : Nat := 4983230072969 + 3 ^ 40 * 5726825 * 2
def baseEnd_5726825 : Nat := 980204616394887168183439

theorem tailTrace_5726825 : CollatzResearch.WordTrace tailWord_5726825 prefixEnd_5726825 980204616394887168183439 := by
  unfold tailWord_5726825
  simp only [CollatzResearch.WordTrace]
  refine ⟨208874467477698563687469929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139249644985132375791646619 208874467477698563687469929)
  ·
    refine ⟨156655850608273922765602447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208874467477698563687469929 156655850608273922765602447)
    ·
      refine ⟨234983775912410884148403671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156655850608273922765602447 234983775912410884148403671)
      ·
        refine ⟨352475663868616326222605507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234983775912410884148403671 352475663868616326222605507)
        ·
          refine ⟨528713495802924489333908261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352475663868616326222605507 528713495802924489333908261)
          ·
            refine ⟨99133780463048341750107799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 528713495802924489333908261 99133780463048341750107799)
            ·
              refine ⟨148700670694572512625161699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99133780463048341750107799 148700670694572512625161699)
              ·
                refine ⟨223051006041858768937742549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148700670694572512625161699 223051006041858768937742549)
                ·
                  refine ⟨5227757954106064896978341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 223051006041858768937742549 5227757954106064896978341)
                  ·
                    refine ⟨980204616394887168183439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227757954106064896978341 980204616394887168183439)
                    ·
                      rfl

theorem cell23_5726825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 4].length) (baseStart_5726825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726825 prefixEnd_5726825 := by exact prefixLift 5726825
  have htrace : WordTrace (prefixWord ++ tailWord_5726825) baseStart_5726825 baseEnd_5726825 := by
    simpa [prefixWord, tailWord_5726825, baseEnd_5726825] using wordTrace_append hprefix tailTrace_5726825
  have hstable : (prefixWord ++ tailWord_5726825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726825).length < 2 ^ (prefixWord ++ tailWord_5726825).sum := by decide
  have hdescent : baseEnd_5726825 < baseStart_5726825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726852 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_5726852 : Nat := 118140960795 + 5726852 * 2 ^ 59
def prefixEnd_5726852 : Nat := 4983230072969 + 3 ^ 40 * 5726852 * 2
def baseEnd_5726852 : Nat := 2940627713162332898912693

theorem tailTrace_5726852 : CollatzResearch.WordTrace tailWord_5726852 prefixEnd_5726852 2940627713162332898912693 := by
  unfold tailWord_5726852
  simp only [CollatzResearch.WordTrace]
  refine ⟨104437726124300373649351405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139250301499067164865801873 104437726124300373649351405)
  ·
    refine ⟨39164147296612640118506777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104437726124300373649351405 39164147296612640118506777)
    ·
      refine ⟨29373110472459480088880083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39164147296612640118506777 29373110472459480088880083)
      ·
        refine ⟨44059665708689220133320125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29373110472459480088880083 44059665708689220133320125)
        ·
          refine ⟨16522374640758457549995047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44059665708689220133320125 16522374640758457549995047)
          ·
            refine ⟨24783561961137686324992571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16522374640758457549995047 24783561961137686324992571)
            ·
              refine ⟨37175342941706529487488857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24783561961137686324992571 37175342941706529487488857)
              ·
                refine ⟨27881507206279897115616643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37175342941706529487488857 27881507206279897115616643)
                ·
                  refine ⟨41822260809419845673424965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27881507206279897115616643 41822260809419845673424965)
                  ·
                    refine ⟨7841673901766221063767181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41822260809419845673424965 7841673901766221063767181)
                    ·
                      refine ⟨2940627713162332898912693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7841673901766221063767181 2940627713162332898912693)
                      ·
                        rfl

theorem cell23_5726852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_5726852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726852 prefixEnd_5726852 := by exact prefixLift 5726852
  have htrace : WordTrace (prefixWord ++ tailWord_5726852) baseStart_5726852 baseEnd_5726852 := by
    simpa [prefixWord, tailWord_5726852, baseEnd_5726852] using wordTrace_append hprefix tailTrace_5726852
  have hstable : (prefixWord ++ tailWord_5726852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726852).length < 2 ^ (prefixWord ++ tailWord_5726852).sum := by decide
  have hdescent : baseEnd_5726852 < baseStart_5726852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726876 : List Nat := [2, 2, 3, 2, 2, 1, 3, 3, 1, 4]
def baseStart_5726876 : Nat := 118140960795 + 5726876 * 2 ^ 59
def prefixEnd_5726876 : Nat := 4983230072969 + 3 ^ 40 * 5726876 * 2
def baseEnd_5726876 : Nat := 980213345566013601670861

theorem tailTrace_5726876 : CollatzResearch.WordTrace tailWord_5726876 prefixEnd_5726876 980213345566013601670861 := by
  unfold tailWord_5726876
  simp only [CollatzResearch.WordTrace]
  refine ⟨104438163800256899698788241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139250885067009199598384321 104438163800256899698788241)
  ·
    refine ⟨78328622850192674774091181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104438163800256899698788241 78328622850192674774091181)
    ·
      refine ⟨29373233568822253040284193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78328622850192674774091181 29373233568822253040284193)
      ·
        refine ⟨22029925176616689780213145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29373233568822253040284193 22029925176616689780213145)
        ·
          refine ⟨16522443882462517335159859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22029925176616689780213145 16522443882462517335159859)
          ·
            refine ⟨24783665823693776002739789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16522443882462517335159859 24783665823693776002739789)
            ·
              refine ⟨9293874683885166001027421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24783665823693776002739789 9293874683885166001027421)
              ·
                refine ⟨3485203006456937250385283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9293874683885166001027421 3485203006456937250385283)
                ·
                  refine ⟨5227804509685405875577925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485203006456937250385283 5227804509685405875577925)
                  ·
                    refine ⟨980213345566013601670861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227804509685405875577925 980213345566013601670861)
                    ·
                      rfl

theorem cell23_5726876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_5726876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726876 prefixEnd_5726876 := by exact prefixLift 5726876
  have htrace : WordTrace (prefixWord ++ tailWord_5726876) baseStart_5726876 baseEnd_5726876 := by
    simpa [prefixWord, tailWord_5726876, baseEnd_5726876] using wordTrace_append hprefix tailTrace_5726876
  have hstable : (prefixWord ++ tailWord_5726876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726876).length < 2 ^ (prefixWord ++ tailWord_5726876).sum := by decide
  have hdescent : baseEnd_5726876 < baseStart_5726876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726885 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_5726885 : Nat := 118140960795 + 5726885 * 2 ^ 59
def prefixEnd_5726885 : Nat := 4983230072969 + 3 ^ 40 * 5726885 * 2
def baseEnd_5726885 : Nat := 980214886007977089933347

theorem tailTrace_5726885 : CollatzResearch.WordTrace tailWord_5726885 prefixEnd_5726885 980214886007977089933347 := by
  unfold tailWord_5726885
  simp only [CollatzResearch.WordTrace]
  refine ⟨208876655857481193934654109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139251103904987462623102739 208876655857481193934654109)
  ·
    refine ⟨78328745946555447725495291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208876655857481193934654109 78328745946555447725495291)
    ·
      refine ⟨117493118919833171588242937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78328745946555447725495291 117493118919833171588242937)
      ·
        refine ⟨88119839189874878691182203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117493118919833171588242937 88119839189874878691182203)
        ·
          refine ⟨132179758784812318036773305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88119839189874878691182203 132179758784812318036773305)
          ·
            refine ⟨99134819088609238527579979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132179758784812318036773305 99134819088609238527579979)
            ·
              refine ⟨148702228632913857791369969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99134819088609238527579979 148702228632913857791369969)
              ·
                refine ⟨111526671474685393343527477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148702228632913857791369969 111526671474685393343527477)
                ·
                  refine ⟨10455625450751755625955701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111526671474685393343527477 10455625450751755625955701)
                  ·
                    refine ⟨980214886007977089933347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10455625450751755625955701 980214886007977089933347)
                    ·
                      rfl

theorem cell23_5726885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_5726885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726885 prefixEnd_5726885 := by exact prefixLift 5726885
  have htrace : WordTrace (prefixWord ++ tailWord_5726885) baseStart_5726885 baseEnd_5726885 := by
    simpa [prefixWord, tailWord_5726885, baseEnd_5726885] using wordTrace_append hprefix tailTrace_5726885
  have hstable : (prefixWord ++ tailWord_5726885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726885).length < 2 ^ (prefixWord ++ tailWord_5726885).sum := by decide
  have hdescent : baseEnd_5726885 < baseStart_5726885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726893 : List Nat := [1, 5, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_5726893 : Nat := 118140960795 + 5726893 * 2 ^ 59
def prefixEnd_5726893 : Nat := 4983230072969 + 3 ^ 40 * 5726893 * 2
def baseEnd_5726893 : Nat := 980216255289722412833335

theorem tailTrace_5726893 : CollatzResearch.WordTrace tailWord_5726893 prefixEnd_5726893 980216255289722412833335 := by
  unfold tailWord_5726893
  simp only [CollatzResearch.WordTrace]
  refine ⟨208876947641452211300945333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139251298427634807533963555 208876947641452211300945333)
  ·
    refine ⟨19582213841386144809463625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208876947641452211300945333 19582213841386144809463625)
    ·
      refine ⟨14686660381039608607097719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19582213841386144809463625 14686660381039608607097719)
      ·
        refine ⟨22029990571559412910646579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14686660381039608607097719 22029990571559412910646579)
        ·
          refine ⟨33044985857339119365969869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22029990571559412910646579 33044985857339119365969869)
          ·
            refine ⟨12391869696502169762238701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33044985857339119365969869 12391869696502169762238701)
            ·
              refine ⟨4646951136188313660839513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12391869696502169762238701 4646951136188313660839513)
              ·
                refine ⟨3485213352141235245629635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4646951136188313660839513 3485213352141235245629635)
                ·
                  refine ⟨5227820028211852868444453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485213352141235245629635 5227820028211852868444453)
                  ·
                    refine ⟨980216255289722412833335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227820028211852868444453 980216255289722412833335)
                    ·
                      rfl

theorem cell23_5726893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_5726893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726893 prefixEnd_5726893 := by exact prefixLift 5726893
  have htrace : WordTrace (prefixWord ++ tailWord_5726893) baseStart_5726893 baseEnd_5726893 := by
    simpa [prefixWord, tailWord_5726893, baseEnd_5726893] using wordTrace_append hprefix tailTrace_5726893
  have hstable : (prefixWord ++ tailWord_5726893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726893).length < 2 ^ (prefixWord ++ tailWord_5726893).sum := by decide
  have hdescent : baseEnd_5726893 < baseStart_5726893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726899 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 3, 1, 3]
def baseStart_5726899 : Nat := 118140960795 + 5726899 * 2 ^ 59
def prefixEnd_5726899 : Nat := 4983230072969 + 3 ^ 40 * 5726899 * 2
def baseEnd_5726899 : Nat := 2940651846753094215024977

theorem tailTrace_5726899 : CollatzResearch.WordTrace tailWord_5726899 prefixEnd_5726899 2940651846753094215024977 := by
  unfold tailWord_5726899
  simp only [CollatzResearch.WordTrace]
  refine ⟨208877166479430474325663751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139251444319620316217109167 208877166479430474325663751)
  ·
    refine ⟨313315749719145711488495627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208877166479430474325663751 313315749719145711488495627)
    ·
      refine ⟨469973624578718567232743441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313315749719145711488495627 469973624578718567232743441)
      ·
        refine ⟨352480218434038925424557581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469973624578718567232743441 352480218434038925424557581)
        ·
          refine ⟨132180081912764597034209093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352480218434038925424557581 132180081912764597034209093)
          ·
            refine ⟨24783765358643361943914205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132180081912764597034209093 24783765358643361943914205)
            ·
              refine ⟨9293912009491260728967827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24783765358643361943914205 9293912009491260728967827)
              ·
                refine ⟨13940868014236891093451741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9293912009491260728967827 13940868014236891093451741)
                ·
                  refine ⟨5227825505338834160044403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13940868014236891093451741 5227825505338834160044403)
                  ·
                    refine ⟨7841738258008251240066605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5227825505338834160044403 7841738258008251240066605)
                    ·
                      refine ⟨2940651846753094215024977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7841738258008251240066605 2940651846753094215024977)
                      ·
                        rfl

theorem cell23_5726899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 1, 3].length) (baseStart_5726899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726899 prefixEnd_5726899 := by exact prefixLift 5726899
  have htrace : WordTrace (prefixWord ++ tailWord_5726899) baseStart_5726899 baseEnd_5726899 := by
    simpa [prefixWord, tailWord_5726899, baseEnd_5726899] using wordTrace_append hprefix tailTrace_5726899
  have hstable : (prefixWord ++ tailWord_5726899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726899).length < 2 ^ (prefixWord ++ tailWord_5726899).sum := by decide
  have hdescent : baseEnd_5726899 < baseStart_5726899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726905 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 4]
def baseStart_5726905 : Nat := 118140960795 + 5726905 * 2 ^ 59
def prefixEnd_5726905 : Nat := 4983230072969 + 3 ^ 40 * 5726905 * 2
def baseEnd_5726905 : Nat := 2940654927637021191549949

theorem tailTrace_5726905 : CollatzResearch.WordTrace tailWord_5726905 prefixEnd_5726905 2940654927637021191549949 := by
  unfold tailWord_5726905
  simp only [CollatzResearch.WordTrace]
  refine ⟨208877385317408737350382169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139251590211605824900254779 208877385317408737350382169)
  ·
    refine ⟨156658038988056553012786627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208877385317408737350382169 156658038988056553012786627)
    ·
      refine ⟨234987058482084829519179941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156658038988056553012786627 234987058482084829519179941)
      ·
        refine ⟨44060073465390905534846239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234987058482084829519179941 44060073465390905534846239)
        ·
          refine ⟨66090110198086358302269359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44060073465390905534846239 66090110198086358302269359)
          ·
            refine ⟨99135165297129537453404039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66090110198086358302269359 99135165297129537453404039)
            ·
              refine ⟨148702747945694306180106059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99135165297129537453404039 148702747945694306180106059)
              ·
                refine ⟨223054121918541459270159089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148702747945694306180106059 223054121918541459270159089)
                ·
                  refine ⟨167290591438906094452619317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223054121918541459270159089 167290591438906094452619317)
                  ·
                    refine ⟨15683492947397446354933061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 167290591438906094452619317 15683492947397446354933061)
                    ·
                      refine ⟨2940654927637021191549949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15683492947397446354933061 2940654927637021191549949)
                      ·
                        rfl

theorem cell23_5726905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_5726905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726905 prefixEnd_5726905 := by exact prefixLift 5726905
  have htrace : WordTrace (prefixWord ++ tailWord_5726905) baseStart_5726905 baseEnd_5726905 := by
    simpa [prefixWord, tailWord_5726905, baseEnd_5726905] using wordTrace_append hprefix tailTrace_5726905
  have hstable : (prefixWord ++ tailWord_5726905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726905).length < 2 ^ (prefixWord ++ tailWord_5726905).sum := by decide
  have hdescent : baseEnd_5726905 < baseStart_5726905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726926 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2]
def baseStart_5726926 : Nat := 118140960795 + 5726926 * 2 ^ 59
def prefixEnd_5726926 : Nat := 4983230072969 + 3 ^ 40 * 5726926 * 2
def baseEnd_5726926 : Nat := 2940665710730765609387353

theorem tailTrace_5726926 : CollatzResearch.WordTrace tailWord_5726926 prefixEnd_5726926 2940665710730765609387353 := by
  unfold tailWord_5726926
  simp only [CollatzResearch.WordTrace]
  refine ⟨26109768906291582242112079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139252100833555105291264421 26109768906291582242112079)
  ·
    refine ⟨39164653359437373363168119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26109768906291582242112079 39164653359437373363168119)
    ·
      refine ⟨58746980039156060044752179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39164653359437373363168119 58746980039156060044752179)
      ·
        refine ⟨88120470058734090067128269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58746980039156060044752179 88120470058734090067128269)
        ·
          refine ⟨33045176272025283775173101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88120470058734090067128269 33045176272025283775173101)
          ·
            refine ⟨12391941102009481415689913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33045176272025283775173101 12391941102009481415689913)
            ·
              refine ⟨9293955826507111061767435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12391941102009481415689913 9293955826507111061767435)
              ·
                refine ⟨13940933739760666592651153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9293955826507111061767435 13940933739760666592651153)
                ·
                  refine ⟨10455700304820499944488365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13940933739760666592651153 10455700304820499944488365)
                  ·
                    refine ⟨3920887614307687479183137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10455700304820499944488365 3920887614307687479183137)
                    ·
                      refine ⟨2940665710730765609387353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920887614307687479183137 2940665710730765609387353)
                      ·
                        rfl

theorem cell23_5726926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_5726926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726926 prefixEnd_5726926 := by exact prefixLift 5726926
  have htrace : WordTrace (prefixWord ++ tailWord_5726926) baseStart_5726926 baseEnd_5726926 := by
    simpa [prefixWord, tailWord_5726926, baseEnd_5726926] using wordTrace_append hprefix tailTrace_5726926
  have hstable : (prefixWord ++ tailWord_5726926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726926).length < 2 ^ (prefixWord ++ tailWord_5726926).sum := by decide
  have hdescent : baseEnd_5726926 < baseStart_5726926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726945 : List Nat := [1, 2, 3, 1, 4, 12]
def baseStart_5726945 : Nat := 118140960795 + 5726945 * 2 ^ 59
def prefixEnd_5726945 : Nat := 4983230072969 + 3 ^ 40 * 5726945 * 2
def baseEnd_5726945 : Nat := 12101545131124284094855

theorem tailTrace_5726945 : CollatzResearch.WordTrace tailWord_5726945 prefixEnd_5726945 12101545131124284094855 := by
  unfold tailWord_5726945
  simp only [CollatzResearch.WordTrace]
  refine ⟨208878844237263824181838289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139252562824842549454558859 208878844237263824181838289)
  ·
    refine ⟨156659133177947868136378717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208878844237263824181838289 156659133177947868136378717)
    ·
      refine ⟨58747174941730450551142019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156659133177947868136378717 58747174941730450551142019)
      ·
        refine ⟨88120762412595675826713029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58747174941730450551142019 88120762412595675826713029)
        ·
          refine ⟨16522642952361689217508693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88120762412595675826713029 16522642952361689217508693)
          ·
            refine ⟨12101545131124284094855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16522642952361689217508693 12101545131124284094855)
            ·
              rfl

theorem cell23_5726945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 12].length) (baseStart_5726945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726945 prefixEnd_5726945 := by exact prefixLift 5726945
  have htrace : WordTrace (prefixWord ++ tailWord_5726945) baseStart_5726945 baseEnd_5726945 := by
    simpa [prefixWord, tailWord_5726945, baseEnd_5726945] using wordTrace_append hprefix tailTrace_5726945
  have hstable : (prefixWord ++ tailWord_5726945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726945).length < 2 ^ (prefixWord ++ tailWord_5726945).sum := by decide
  have hdescent : baseEnd_5726945 < baseStart_5726945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726949 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 2, 4]
def baseStart_5726949 : Nat := 118140960795 + 5726949 * 2 ^ 59
def prefixEnd_5726949 : Nat := 4983230072969 + 3 ^ 40 * 5726949 * 2
def baseEnd_5726949 : Nat := 980225840261939673133249

theorem tailTrace_5726949 : CollatzResearch.WordTrace tailWord_5726949 prefixEnd_5726949 980225840261939673133249 := by
  unfold tailWord_5726949
  simp only [CollatzResearch.WordTrace]
  refine ⟨208878990129249332864983901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139252660086166221909989267 208878990129249332864983901)
  ·
    refine ⟨78329621298468499824368963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208878990129249332864983901 78329621298468499824368963)
    ·
      refine ⟨117494431947702749736553445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78329621298468499824368963 117494431947702749736553445)
      ·
        refine ⟨22030205990194265575603771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117494431947702749736553445 22030205990194265575603771)
        ·
          refine ⟨33045308985291398363405657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22030205990194265575603771 33045308985291398363405657)
          ·
            refine ⟨24783981738968548772554243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33045308985291398363405657 24783981738968548772554243)
            ·
              refine ⟨37175972608452823158831365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24783981738968548772554243 37175972608452823158831365)
              ·
                refine ⟨6970494864084904342280881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37175972608452823158831365 6970494864084904342280881)
                ·
                  refine ⟨5227871148063678256710661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6970494864084904342280881 5227871148063678256710661)
                  ·
                    refine ⟨980225840261939673133249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5227871148063678256710661 980225840261939673133249)
                    ·
                      rfl

theorem cell23_5726949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_5726949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726949 prefixEnd_5726949 := by exact prefixLift 5726949
  have htrace : WordTrace (prefixWord ++ tailWord_5726949) baseStart_5726949 baseEnd_5726949 := by
    simpa [prefixWord, tailWord_5726949, baseEnd_5726949] using wordTrace_append hprefix tailTrace_5726949
  have hstable : (prefixWord ++ tailWord_5726949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726949).length < 2 ^ (prefixWord ++ tailWord_5726949).sum := by decide
  have hdescent : baseEnd_5726949 < baseStart_5726949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726962 : List Nat := [3, 2, 1, 3, 1, 2, 3, 8]
def baseStart_5726962 : Nat := 118140960795 + 5726962 * 2 ^ 59
def prefixEnd_5726962 : Nat := 4983230072969 + 3 ^ 40 * 5726962 * 2
def baseEnd_5726962 : Nat := 108914229482752869205081

theorem tailTrace_5726962 : CollatzResearch.WordTrace tailWord_5726962 prefixEnd_5726962 108914229482752869205081 := by
  unfold tailWord_5726962
  simp only [CollatzResearch.WordTrace]
  refine ⟨52219866069550559021301785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139252976185468157390138093 52219866069550559021301785)
  ·
    refine ⟨39164899552162919265976339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52219866069550559021301785 39164899552162919265976339)
    ·
      refine ⟨58747349328244378898964509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39164899552162919265976339 58747349328244378898964509)
      ·
        refine ⟨22030255998091642087111691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58747349328244378898964509 22030255998091642087111691)
        ·
          refine ⟨33045383997137463130667537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22030255998091642087111691 33045383997137463130667537)
          ·
            refine ⟨24784037997853097348000653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33045383997137463130667537 24784037997853097348000653)
            ·
              refine ⟨9294014249194911505500245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24784037997853097348000653 9294014249194911505500245)
              ·
                refine ⟨108914229482752869205081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9294014249194911505500245 108914229482752869205081)
                ·
                  rfl

theorem cell23_5726962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 8].length) (baseStart_5726962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726962 prefixEnd_5726962 := by exact prefixLift 5726962
  have htrace : WordTrace (prefixWord ++ tailWord_5726962) baseStart_5726962 baseEnd_5726962 := by
    simpa [prefixWord, tailWord_5726962, baseEnd_5726962] using wordTrace_append hprefix tailTrace_5726962
  have hstable : (prefixWord ++ tailWord_5726962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726962).length < 2 ^ (prefixWord ++ tailWord_5726962).sum := by decide
  have hdescent : baseEnd_5726962 < baseStart_5726962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5726975 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 4, 7]
def baseStart_5726975 : Nat := 118140960795 + 5726975 * 2 ^ 59
def prefixEnd_5726975 : Nat := 4983230072969 + 3 ^ 40 * 5726975 * 2
def baseEnd_5726975 : Nat := 980230290427611972558209

theorem tailTrace_5726975 : CollatzResearch.WordTrace tailWord_5726975 prefixEnd_5726975 980230290427611972558209 := by
  unfold tailWord_5726975
  simp only [CollatzResearch.WordTrace]
  refine ⟨208879938427155139305430379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139253292284770092870286919 208879938427155139305430379)
  ·
    refine ⟨313319907640732708958145569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208879938427155139305430379 313319907640732708958145569)
    ·
      refine ⟨234989930730549531718609177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313319907640732708958145569 234989930730549531718609177)
      ·
        refine ⟨176242448047912148788956883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234989930730549531718609177 176242448047912148788956883)
        ·
          refine ⟨264363672071868223183435325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176242448047912148788956883 264363672071868223183435325)
          ·
            refine ⟨99136377026950583693788247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264363672071868223183435325 99136377026950583693788247)
            ·
              refine ⟨148704565540425875540682371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99136377026950583693788247 148704565540425875540682371)
              ·
                refine ⟨223056848310638813311023557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148704565540425875540682371 223056848310638813311023557)
                ·
                  refine ⟨41823159058244777495816917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223056848310638813311023557 41823159058244777495816917)
                  ·
                    refine ⟨980230290427611972558209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41823159058244777495816917 980230290427611972558209)
                    ·
                      rfl

theorem cell23_5726975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_5726975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5726975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5726975 prefixEnd_5726975 := by exact prefixLift 5726975
  have htrace : WordTrace (prefixWord ++ tailWord_5726975) baseStart_5726975 baseEnd_5726975 := by
    simpa [prefixWord, tailWord_5726975, baseEnd_5726975] using wordTrace_append hprefix tailTrace_5726975
  have hstable : (prefixWord ++ tailWord_5726975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5726975).length < 2 ^ (prefixWord ++ tailWord_5726975).sum := by decide
  have hdescent : baseEnd_5726975 < baseStart_5726975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5726975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727032 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_5727032 : Nat := 118140960795 + 5727032 * 2 ^ 59
def prefixEnd_5727032 : Nat := 4983230072969 + 3 ^ 40 * 5727032 * 2
def baseEnd_5727032 : Nat := 2940720139680142194661865

theorem tailTrace_5727032 : CollatzResearch.WordTrace tailWord_5727032 prefixEnd_5727032 2940720139680142194661865 := by
  unfold tailWord_5727032
  simp only [CollatzResearch.WordTrace]
  refine ⟨104441008693974319020127675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139254678258632425360170233 104441008693974319020127675)
  ·
    refine ⟨156661513040961478530191513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104441008693974319020127675 156661513040961478530191513)
    ·
      refine ⟨117496134780721108897643635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156661513040961478530191513 117496134780721108897643635)
      ·
        refine ⟨176244202171081663346465453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117496134780721108897643635 176244202171081663346465453)
        ·
          refine ⟨66091575814155623754924545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176244202171081663346465453 66091575814155623754924545)
          ·
            refine ⟨49568681860616717816193409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66091575814155623754924545 49568681860616717816193409)
            ·
              refine ⟨37176511395462538362145057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49568681860616717816193409 37176511395462538362145057)
              ·
                refine ⟨27882383546596903771608793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37176511395462538362145057 27882383546596903771608793)
                ·
                  refine ⟨20911787659947677828706595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27882383546596903771608793 20911787659947677828706595)
                  ·
                    refine ⟨31367681489921516743059893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20911787659947677828706595 31367681489921516743059893)
                    ·
                      refine ⟨2940720139680142194661865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31367681489921516743059893 2940720139680142194661865)
                      ·
                        rfl

theorem cell23_5727032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_5727032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727032 prefixEnd_5727032 := by exact prefixLift 5727032
  have htrace : WordTrace (prefixWord ++ tailWord_5727032) baseStart_5727032 baseEnd_5727032 := by
    simpa [prefixWord, tailWord_5727032, baseEnd_5727032] using wordTrace_append hprefix tailTrace_5727032
  have hstable : (prefixWord ++ tailWord_5727032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727032).length < 2 ^ (prefixWord ++ tailWord_5727032).sum := by decide
  have hdescent : baseEnd_5727032 < baseStart_5727032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727080 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_5727080 : Nat := 118140960795 + 5727080 * 2 ^ 59
def prefixEnd_5727080 : Nat := 4983230072969 + 3 ^ 40 * 5727080 * 2
def baseEnd_5727080 : Nat := 2940744786751558006861645

theorem tailTrace_5727080 : CollatzResearch.WordTrace tailWord_5727080 prefixEnd_5727080 2940744786751558006861645 := by
  unfold tailWord_5727080
  simp only [CollatzResearch.WordTrace]
  refine ⟨104441884045887371119001347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139255845394516494825335129 104441884045887371119001347)
  ·
    refine ⟨156662826068831056678502021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104441884045887371119001347 156662826068831056678502021)
    ·
      refine ⟨29374279887905823127219129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156662826068831056678502021 29374279887905823127219129)
      ·
        refine ⟨22030709915929367345414347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29374279887905823127219129 22030709915929367345414347)
        ·
          refine ⟨33046064873894051018121521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22030709915929367345414347 33046064873894051018121521)
          ·
            refine ⟨24784548655420538263591141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33046064873894051018121521 24784548655420538263591141)
            ·
              refine ⟨4647102872891350924423339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24784548655420538263591141 4647102872891350924423339)
              ·
                refine ⟨6970654309337026386635009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647102872891350924423339 6970654309337026386635009)
                ·
                  refine ⟨5227990732002769789976257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6970654309337026386635009 5227990732002769789976257)
                  ·
                    refine ⟨3920993049002077342482193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5227990732002769789976257 3920993049002077342482193)
                    ·
                      refine ⟨2940744786751558006861645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3920993049002077342482193 2940744786751558006861645)
                      ·
                        rfl

theorem cell23_5727080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_5727080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727080 prefixEnd_5727080 := by exact prefixLift 5727080
  have htrace : WordTrace (prefixWord ++ tailWord_5727080) baseStart_5727080 baseEnd_5727080 := by
    simpa [prefixWord, tailWord_5727080, baseEnd_5727080] using wordTrace_append hprefix tailTrace_5727080
  have hstable : (prefixWord ++ tailWord_5727080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727080).length < 2 ^ (prefixWord ++ tailWord_5727080).sum := by decide
  have hdescent : baseEnd_5727080 < baseStart_5727080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727129 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 3, 4]
def baseStart_5727129 : Nat := 118140960795 + 5727129 * 2 ^ 59
def prefixEnd_5727129 : Nat := 4983230072969 + 3 ^ 40 * 5727129 * 2
def baseEnd_5727129 : Nat := 980256649101209438382973

theorem tailTrace_5727129 : CollatzResearch.WordTrace tailWord_5727129 prefixEnd_5727129 980256649101209438382973 := by
  unfold tailWord_5727129
  simp only [CollatzResearch.WordTrace]
  refine ⟨208885555268597223606536441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139257036845731482404357627 208885555268597223606536441)
  ·
    refine ⟨156664166451447917704902331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208885555268597223606536441 156664166451447917704902331)
    ·
      refine ⟨234996249677171876557353497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156664166451447917704902331 234996249677171876557353497)
      ·
        refine ⟨176247187257878907418015123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234996249677171876557353497 176247187257878907418015123)
        ·
          refine ⟨264370780886818361127022685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176247187257878907418015123 264370780886818361127022685)
          ·
            refine ⟨99139042832556885422633507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264370780886818361127022685 99139042832556885422633507)
            ·
              refine ⟨148708564248835328133950261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99139042832556885422633507 148708564248835328133950261)
              ·
                refine ⟨13941427898328312012557837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148708564248835328133950261 13941427898328312012557837)
                ·
                  refine ⟨5228035461873117004709189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13941427898328312012557837 5228035461873117004709189)
                  ·
                    refine ⟨980256649101209438382973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5228035461873117004709189 980256649101209438382973)
                    ·
                      rfl

theorem cell23_5727129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 4].length) (baseStart_5727129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727129 prefixEnd_5727129 := by exact prefixLift 5727129
  have htrace : WordTrace (prefixWord ++ tailWord_5727129) baseStart_5727129 baseEnd_5727129 := by
    simpa [prefixWord, tailWord_5727129, baseEnd_5727129] using wordTrace_append hprefix tailTrace_5727129
  have hstable : (prefixWord ++ tailWord_5727129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727129).length < 2 ^ (prefixWord ++ tailWord_5727129).sum := by decide
  have hdescent : baseEnd_5727129 < baseStart_5727129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727139 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 3]
def baseStart_5727139 : Nat := 118140960795 + 5727139 * 2 ^ 59
def prefixEnd_5727139 : Nat := 4983230072969 + 3 ^ 40 * 5727139 * 2
def baseEnd_5727139 : Nat := 2940775082110173276023873

theorem tailTrace_5727139 : CollatzResearch.WordTrace tailWord_5727139 prefixEnd_5727139 2940775082110173276023873 := by
  unfold tailWord_5727139
  simp only [CollatzResearch.WordTrace]
  refine ⟨208885919998560995314400471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139257279999040663542933647 208885919998560995314400471)
  ·
    refine ⟨313328879997841492971600707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208885919998560995314400471 313328879997841492971600707)
    ·
      refine ⟨469993319996762239457401061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313328879997841492971600707 469993319996762239457401061)
      ·
        refine ⟨88123747499392919898262699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 469993319996762239457401061 88123747499392919898262699)
        ·
          refine ⟨132185621249089379847394049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88123747499392919898262699 132185621249089379847394049)
          ·
            refine ⟨99139215936817034885545537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132185621249089379847394049 99139215936817034885545537)
            ·
              refine ⟨74354411952612776164159153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99139215936817034885545537 74354411952612776164159153)
              ·
                refine ⟨55765808964459582123119365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74354411952612776164159153 55765808964459582123119365)
                ·
                  refine ⟨10456089180836171648084881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55765808964459582123119365 10456089180836171648084881)
                  ·
                    refine ⟨7842066885627128736063661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10456089180836171648084881 7842066885627128736063661)
                    ·
                      refine ⟨2940775082110173276023873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7842066885627128736063661 2940775082110173276023873)
                      ·
                        rfl

theorem cell23_5727139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_5727139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727139 prefixEnd_5727139 := by exact prefixLift 5727139
  have htrace : WordTrace (prefixWord ++ tailWord_5727139) baseStart_5727139 baseEnd_5727139 := by
    simpa [prefixWord, tailWord_5727139, baseEnd_5727139] using wordTrace_append hprefix tailTrace_5727139
  have hstable : (prefixWord ++ tailWord_5727139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727139).length < 2 ^ (prefixWord ++ tailWord_5727139).sum := by decide
  have hdescent : baseEnd_5727139 < baseStart_5727139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727153 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 4]
def baseStart_5727153 : Nat := 118140960795 + 5727153 * 2 ^ 59
def prefixEnd_5727153 : Nat := 4983230072969 + 3 ^ 40 * 5727153 * 2
def baseEnd_5727153 : Nat := 2940782270839336221248809

theorem tailTrace_5727153 : CollatzResearch.WordTrace tailWord_5727153 prefixEnd_5727153 2940782270839336221248809 := by
  unfold tailWord_5727153
  simp only [CollatzResearch.WordTrace]
  refine ⟨208886430620510275705410113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139257620413673517136940075 208886430620510275705410113)
  ·
    refine ⟨156664822965382706779057585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208886430620510275705410113 156664822965382706779057585)
    ·
      refine ⟨117498617224037030084293189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156664822965382706779057585 117498617224037030084293189)
      ·
        refine ⟨22030990729506943140804973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117498617224037030084293189 22030990729506943140804973)
        ·
          refine ⟨8261621523565103677801865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22030990729506943140804973 8261621523565103677801865)
          ·
            refine ⟨6196216142673827758351399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8261621523565103677801865 6196216142673827758351399)
            ·
              refine ⟨9294324214010741637527099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6196216142673827758351399 9294324214010741637527099)
              ·
                refine ⟨13941486321016112456290649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9294324214010741637527099 13941486321016112456290649)
                ·
                  refine ⟨10456114740762084342217987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13941486321016112456290649 10456114740762084342217987)
                  ·
                    refine ⟨15684172111143126513326981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10456114740762084342217987 15684172111143126513326981)
                    ·
                      refine ⟨2940782270839336221248809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15684172111143126513326981 2940782270839336221248809)
                      ·
                        rfl

theorem cell23_5727153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_5727153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727153 prefixEnd_5727153 := by exact prefixLift 5727153
  have htrace : WordTrace (prefixWord ++ tailWord_5727153) baseStart_5727153 baseEnd_5727153 := by
    simpa [prefixWord, tailWord_5727153, baseEnd_5727153] using wordTrace_append hprefix tailTrace_5727153
  have hstable : (prefixWord ++ tailWord_5727153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727153).length < 2 ^ (prefixWord ++ tailWord_5727153).sum := by decide
  have hdescent : baseEnd_5727153 < baseStart_5727153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727239 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_5727239 : Nat := 118140960795 + 5727239 * 2 ^ 59
def prefixEnd_5727239 : Nat := 4983230072969 + 3 ^ 40 * 5727239 * 2
def baseEnd_5727239 : Nat := 2940826430175622884773413

theorem tailTrace_5727239 : CollatzResearch.WordTrace tailWord_5727239 prefixEnd_5727239 2940826430175622884773413 := by
  unfold tailWord_5727239
  simp only [CollatzResearch.WordTrace]
  refine ⟨208889567298198712393040771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139259711532132474928693847 208889567298198712393040771)
  ·
    refine ⟨313334350947298068589561157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208889567298198712393040771 313334350947298068589561157)
    ·
      refine ⟨58750190802618387860542717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313334350947298068589561157 58750190802618387860542717)
      ·
        refine ⟨22031321550981895447703519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58750190802618387860542717 22031321550981895447703519)
        ·
          refine ⟨33046982326472843171555279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22031321550981895447703519 33046982326472843171555279)
          ·
            refine ⟨49570473489709264757332919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33046982326472843171555279 49570473489709264757332919)
            ·
              refine ⟨74355710234563897135999379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49570473489709264757332919 74355710234563897135999379)
              ·
                refine ⟨111533565351845845703999069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74355710234563897135999379 111533565351845845703999069)
                ·
                  refine ⟨41825087006942192138999651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111533565351845845703999069 41825087006942192138999651)
                  ·
                    refine ⟨62737630510413288208499477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41825087006942192138999651 62737630510413288208499477)
                    ·
                      refine ⟨2940826430175622884773413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62737630510413288208499477 2940826430175622884773413)
                      ·
                        rfl

theorem cell23_5727239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_5727239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727239 prefixEnd_5727239 := by exact prefixLift 5727239
  have htrace : WordTrace (prefixWord ++ tailWord_5727239) baseStart_5727239 baseEnd_5727239 := by
    simpa [prefixWord, tailWord_5727239, baseEnd_5727239] using wordTrace_append hprefix tailTrace_5727239
  have hstable : (prefixWord ++ tailWord_5727239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727239).length < 2 ^ (prefixWord ++ tailWord_5727239).sum := by decide
  have hdescent : baseEnd_5727239 < baseStart_5727239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727246 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_5727246 : Nat := 118140960795 + 5727246 * 2 ^ 59
def prefixEnd_5727246 : Nat := 4983230072969 + 3 ^ 40 * 5727246 * 2
def baseEnd_5727246 : Nat := 2940830024540204357385881

theorem tailTrace_5727246 : CollatzResearch.WordTrace tailWord_5727246 prefixEnd_5727246 2940830024540204357385881 := by
  unfold tailWord_5727246
  simp only [CollatzResearch.WordTrace]
  refine ⟨26111227826146669073568199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139259881739448901725697061 26111227826146669073568199)
  ·
    refine ⟨39166841739220003610352299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26111227826146669073568199 39166841739220003610352299)
    ·
      refine ⟨58750262608830005415528449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39166841739220003610352299 58750262608830005415528449)
      ·
        refine ⟨44062696956622504061646337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58750262608830005415528449 44062696956622504061646337)
        ·
          refine ⟨33047022717466878046234753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44062696956622504061646337 33047022717466878046234753)
          ·
            refine ⟨24785267038100158534676065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33047022717466878046234753 24785267038100158534676065)
            ·
              refine ⟨18588950278575118901007049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24785267038100158534676065 18588950278575118901007049)
              ·
                refine ⟨13941712708931339175755287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18588950278575118901007049 13941712708931339175755287)
                ·
                  refine ⟨20912569063397008763632931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13941712708931339175755287 20912569063397008763632931)
                  ·
                    refine ⟨31368853595095513145449397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20912569063397008763632931 31368853595095513145449397)
                    ·
                      refine ⟨2940830024540204357385881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31368853595095513145449397 2940830024540204357385881)
                      ·
                        rfl

theorem cell23_5727246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_5727246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727246 prefixEnd_5727246 := by exact prefixLift 5727246
  have htrace : WordTrace (prefixWord ++ tailWord_5727246) baseStart_5727246 baseEnd_5727246 := by
    simpa [prefixWord, tailWord_5727246, baseEnd_5727246] using wordTrace_append hprefix tailTrace_5727246
  have hstable : (prefixWord ++ tailWord_5727246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727246).length < 2 ^ (prefixWord ++ tailWord_5727246).sum := by decide
  have hdescent : baseEnd_5727246 < baseStart_5727246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727253 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 2, 4]
def baseStart_5727253 : Nat := 118140960795 + 5727253 * 2 ^ 59
def prefixEnd_5727253 : Nat := 4983230072969 + 3 ^ 40 * 5727253 * 2
def baseEnd_5727253 : Nat := 980277872968261943332783

theorem tailTrace_5727253 : CollatzResearch.WordTrace tailWord_5727253 prefixEnd_5727253 980277872968261943332783 := by
  unfold tailWord_5727253
  simp only [CollatzResearch.WordTrace]
  refine ⟨208890077920147992784050413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139260051946765328522700275 208890077920147992784050413)
  ·
    refine ⟨78333779220055497294018905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208890077920147992784050413 78333779220055497294018905)
    ·
      refine ⟨58750334415041622970514179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78333779220055497294018905 58750334415041622970514179)
      ·
        refine ⟨88125501622562434455771269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58750334415041622970514179 88125501622562434455771269)
        ·
          refine ⟨16523531554230456460457113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88125501622562434455771269 16523531554230456460457113)
          ·
            refine ⟨12392648665672842345342835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16523531554230456460457113 12392648665672842345342835)
            ·
              refine ⟨18588972998509263518014253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12392648665672842345342835 18588972998509263518014253)
              ·
                refine ⟨6970864874440973819255345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18588972998509263518014253 6970864874440973819255345)
                ·
                  refine ⟨5228148655830730364441509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6970864874440973819255345 5228148655830730364441509)
                  ·
                    refine ⟨980277872968261943332783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5228148655830730364441509 980277872968261943332783)
                    ·
                      rfl

theorem cell23_5727253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_5727253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727253 prefixEnd_5727253 := by exact prefixLift 5727253
  have htrace : WordTrace (prefixWord ++ tailWord_5727253) baseStart_5727253 baseEnd_5727253 := by
    simpa [prefixWord, tailWord_5727253, baseEnd_5727253] using wordTrace_append hprefix tailTrace_5727253
  have hstable : (prefixWord ++ tailWord_5727253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727253).length < 2 ^ (prefixWord ++ tailWord_5727253).sum := by decide
  have hdescent : baseEnd_5727253 < baseStart_5727253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727260 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_5727260 : Nat := 118140960795 + 5727260 * 2 ^ 59
def prefixEnd_5727260 : Nat := 4983230072969 + 3 ^ 40 * 5727260 * 2
def baseEnd_5727260 : Nat := 2940837213269367302610817

theorem tailTrace_5727260 : CollatzResearch.WordTrace tailWord_5727260 prefixEnd_5727260 2940837213269367302610817 := by
  unfold tailWord_5727260
  simp only [CollatzResearch.WordTrace]
  refine ⟨104445166615561316489777617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139260222154081755319703489 104445166615561316489777617)
  ·
    refine ⟨78333874961670987367333213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104445166615561316489777617 78333874961670987367333213)
    ·
      refine ⟨29375203110626620262749955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78333874961670987367333213 29375203110626620262749955)
      ·
        refine ⟨44062804665939930394124933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29375203110626620262749955 44062804665939930394124933)
        ·
          refine ⟨8261775874863736948898425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44062804665939930394124933 8261775874863736948898425)
          ·
            refine ⟨6196331906147802711673819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8261775874863736948898425 6196331906147802711673819)
            ·
              refine ⟨9294497859221704067510729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6196331906147802711673819 9294497859221704067510729)
              ·
                refine ⟨6970873394416278050633047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9294497859221704067510729 6970873394416278050633047)
                ·
                  refine ⟨10456310091624417075949571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970873394416278050633047 10456310091624417075949571)
                  ·
                    refine ⟨15684465137436625613924357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10456310091624417075949571 15684465137436625613924357)
                    ·
                      refine ⟨2940837213269367302610817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15684465137436625613924357 2940837213269367302610817)
                      ·
                        rfl

theorem cell23_5727260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_5727260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727260 prefixEnd_5727260 := by exact prefixLift 5727260
  have htrace : WordTrace (prefixWord ++ tailWord_5727260) baseStart_5727260 baseEnd_5727260 := by
    simpa [prefixWord, tailWord_5727260, baseEnd_5727260] using wordTrace_append hprefix tailTrace_5727260
  have hstable : (prefixWord ++ tailWord_5727260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727260).length < 2 ^ (prefixWord ++ tailWord_5727260).sum := by decide
  have hdescent : baseEnd_5727260 < baseStart_5727260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727263 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 1, 2, 3]
def baseStart_5727263 : Nat := 118140960795 + 5727263 * 2 ^ 59
def prefixEnd_5727263 : Nat := 4983230072969 + 3 ^ 40 * 5727263 * 2
def baseEnd_5727263 : Nat := 2940838753711330790873303

theorem tailTrace_5727263 : CollatzResearch.WordTrace tailWord_5727263 prefixEnd_5727263 2940838753711330790873303 := by
  unfold tailWord_5727263
  simp only [CollatzResearch.WordTrace]
  refine ⟨208890442650111764491914443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139260295100074509661276295 208890442650111764491914443)
  ·
    refine ⟨313335663975167646737871665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208890442650111764491914443 313335663975167646737871665)
    ·
      refine ⟨235001747981375735053403749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313335663975167646737871665 235001747981375735053403749)
      ·
        refine ⟨44062827746507950322513203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235001747981375735053403749 44062827746507950322513203)
        ·
          refine ⟨66094241619761925483769805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44062827746507950322513203 66094241619761925483769805)
          ·
            refine ⟨24785340607410722056413677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66094241619761925483769805 24785340607410722056413677)
            ·
              refine ⟨9294502727779020771155129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24785340607410722056413677 9294502727779020771155129)
              ·
                refine ⟨6970877045834265578366347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9294502727779020771155129 6970877045834265578366347)
                ·
                  refine ⟨10456315568751398367549521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970877045834265578366347 10456315568751398367549521)
                  ·
                    refine ⟨7842236676563548775662141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10456315568751398367549521 7842236676563548775662141)
                    ·
                      refine ⟨2940838753711330790873303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7842236676563548775662141 2940838753711330790873303)
                      ·
                        rfl

theorem cell23_5727263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_5727263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727263 prefixEnd_5727263 := by exact prefixLift 5727263
  have htrace : WordTrace (prefixWord ++ tailWord_5727263) baseStart_5727263 baseEnd_5727263 := by
    simpa [prefixWord, tailWord_5727263, baseEnd_5727263] using wordTrace_append hprefix tailTrace_5727263
  have hstable : (prefixWord ++ tailWord_5727263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727263).length < 2 ^ (prefixWord ++ tailWord_5727263).sum := by decide
  have hdescent : baseEnd_5727263 < baseStart_5727263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727276 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 3]
def baseStart_5727276 : Nat := 118140960795 + 5727276 * 2 ^ 59
def prefixEnd_5727276 : Nat := 4983230072969 + 3 ^ 40 * 5727276 * 2
def baseEnd_5727276 : Nat := 2940845428959839240010743

theorem tailTrace_5727276 : CollatzResearch.WordTrace tailWord_5727276 prefixEnd_5727276 2940845428959839240010743 := by
  unfold tailWord_5727276
  simp only [CollatzResearch.WordTrace]
  refine ⟨104445458399532333856068841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139260611199376445141425121 104445458399532333856068841)
  ·
    refine ⟨78334093799649250392051631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104445458399532333856068841 78334093799649250392051631)
    ·
      refine ⟨117501140699473875588077447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78334093799649250392051631 117501140699473875588077447)
      ·
        refine ⟨176251711049210813382116171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117501140699473875588077447 176251711049210813382116171)
        ·
          refine ⟨264377566573816220073174257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176251711049210813382116171 264377566573816220073174257)
          ·
            refine ⟨198283174930362165054880693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264377566573816220073174257 198283174930362165054880693)
            ·
              refine ⟨18589047649721452973895065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 198283174930362165054880693 18589047649721452973895065)
              ·
                refine ⟨13941785737291089730421299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18589047649721452973895065 13941785737291089730421299)
                ·
                  refine ⟨20912678605936634595631949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13941785737291089730421299 20912678605936634595631949)
                  ·
                    refine ⟨7842254477226237973361981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20912678605936634595631949 7842254477226237973361981)
                    ·
                      refine ⟨2940845428959839240010743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7842254477226237973361981 2940845428959839240010743)
                      ·
                        rfl

theorem cell23_5727276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_5727276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727276 prefixEnd_5727276 := by exact prefixLift 5727276
  have htrace : WordTrace (prefixWord ++ tailWord_5727276) baseStart_5727276 baseEnd_5727276 := by
    simpa [prefixWord, tailWord_5727276, baseEnd_5727276] using wordTrace_append hprefix tailTrace_5727276
  have hstable : (prefixWord ++ tailWord_5727276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727276).length < 2 ^ (prefixWord ++ tailWord_5727276).sum := by decide
  have hdescent : baseEnd_5727276 < baseStart_5727276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727294 : List Nat := [4, 2, 1, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_5727294 : Nat := 118140960795 + 5727294 * 2 ^ 59
def prefixEnd_5727294 : Nat := 4983230072969 + 3 ^ 40 * 5727294 * 2
def baseEnd_5727294 : Nat := 2940854671611620169585661

theorem tailTrace_5727294 : CollatzResearch.WordTrace tailWord_5727294 prefixEnd_5727294 2940854671611620169585661 := by
  unfold tailWord_5727294
  simp only [CollatzResearch.WordTrace]
  refine ⟨26111446664124932098286617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139261048875332971190861957 26111446664124932098286617)
  ·
    refine ⟨19583584998093699073714963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26111446664124932098286617 19583584998093699073714963)
    ·
      refine ⟨29375377497140548610572445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19583584998093699073714963 29375377497140548610572445)
      ·
        refine ⟨11015766561427705728964667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29375377497140548610572445 11015766561427705728964667)
        ·
          refine ⟨16523649842141558593447001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11015766561427705728964667 16523649842141558593447001)
          ·
            refine ⟨12392737381606168945085251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16523649842141558593447001 12392737381606168945085251)
            ·
              refine ⟨18589106072409253417627877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12392737381606168945085251 18589106072409253417627877)
              ·
                refine ⟨3485457388576735015805227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18589106072409253417627877 3485457388576735015805227)
                ·
                  refine ⟨5228186082865102523707841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485457388576735015805227 5228186082865102523707841)
                  ·
                    refine ⟨3921139562148826892780881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5228186082865102523707841 3921139562148826892780881)
                    ·
                      refine ⟨2940854671611620169585661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921139562148826892780881 2940854671611620169585661)
                      ·
                        rfl

theorem cell23_5727294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_5727294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727294 prefixEnd_5727294 := by exact prefixLift 5727294
  have htrace : WordTrace (prefixWord ++ tailWord_5727294) baseStart_5727294 baseEnd_5727294 := by
    simpa [prefixWord, tailWord_5727294, baseEnd_5727294] using wordTrace_append hprefix tailTrace_5727294
  have hstable : (prefixWord ++ tailWord_5727294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727294).length < 2 ^ (prefixWord ++ tailWord_5727294).sum := by decide
  have hdescent : baseEnd_5727294 < baseStart_5727294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727299 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 4]
def baseStart_5727299 : Nat := 118140960795 + 5727299 * 2 ^ 59
def prefixEnd_5727299 : Nat := 4983230072969 + 3 ^ 40 * 5727299 * 2
def baseEnd_5727299 : Nat := 2940857239014892650023137

theorem tailTrace_5727299 : CollatzResearch.WordTrace tailWord_5727299 prefixEnd_5727299 2940857239014892650023137 := by
  unfold tailWord_5727299
  simp only [CollatzResearch.WordTrace]
  refine ⟨208891755677981342640224951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139261170451987561760149967 208891755677981342640224951)
  ·
    refine ⟨313337633516972013960337427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208891755677981342640224951 313337633516972013960337427)
    ·
      refine ⟨470006450275458020940506141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313337633516972013960337427 470006450275458020940506141)
      ·
        refine ⟨176252418853296757852689803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 470006450275458020940506141 176252418853296757852689803)
        ·
          refine ⟨264378628279945136779034705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176252418853296757852689803 264378628279945136779034705)
          ·
            refine ⟨198283971209958852584276029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264378628279945136779034705 198283971209958852584276029)
            ·
              refine ⟨74356489203734569719103511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198283971209958852584276029 74356489203734569719103511)
              ·
                refine ⟨111534733805601854578655267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74356489203734569719103511 111534733805601854578655267)
                ·
                  refine ⟨167302100708402781867982901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111534733805601854578655267 167302100708402781867982901)
                  ·
                    refine ⟨15684571941412760800123397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 167302100708402781867982901 15684571941412760800123397)
                    ·
                      refine ⟨2940857239014892650023137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15684571941412760800123397 2940857239014892650023137)
                      ·
                        rfl

theorem cell23_5727299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_5727299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727299 prefixEnd_5727299 := by exact prefixLift 5727299
  have htrace : WordTrace (prefixWord ++ tailWord_5727299) baseStart_5727299 baseEnd_5727299 := by
    simpa [prefixWord, tailWord_5727299, baseEnd_5727299] using wordTrace_append hprefix tailTrace_5727299
  have hstable : (prefixWord ++ tailWord_5727299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727299).length < 2 ^ (prefixWord ++ tailWord_5727299).sum := by decide
  have hdescent : baseEnd_5727299 < baseStart_5727299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727303 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 3, 3, 2]
def baseStart_5727303 : Nat := 118140960795 + 5727303 * 2 ^ 59
def prefixEnd_5727303 : Nat := 4983230072969 + 3 ^ 40 * 5727303 * 2
def baseEnd_5727303 : Nat := 2940859292937510634373119

theorem tailTrace_5727303 : CollatzResearch.WordTrace tailWord_5727303 prefixEnd_5727303 2940859292937510634373119 := by
  unfold tailWord_5727303
  simp only [CollatzResearch.WordTrace]
  refine ⟨208891901569966851323370563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139261267713311234215580375 208891901569966851323370563)
  ·
    refine ⟨313337852354950276985055845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208891901569966851323370563 313337852354950276985055845)
    ·
      refine ⟨58750847316553176934697971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313337852354950276985055845 58750847316553176934697971)
      ·
        refine ⟨88126270974829765402046957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58750847316553176934697971 88126270974829765402046957)
        ·
          refine ⟨33047351615561162025767609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88126270974829765402046957 33047351615561162025767609)
          ·
            refine ⟨24785513711670871519325707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33047351615561162025767609 24785513711670871519325707)
            ·
              refine ⟨37178270567506307278988561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24785513711670871519325707 37178270567506307278988561)
              ·
                refine ⟨27883702925629730459241421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37178270567506307278988561 27883702925629730459241421)
                ·
                  refine ⟨10456388597111148922215533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27883702925629730459241421 10456388597111148922215533)
                  ·
                    refine ⟨3921145723916680845830825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10456388597111148922215533 3921145723916680845830825)
                    ·
                      refine ⟨2940859292937510634373119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921145723916680845830825 2940859292937510634373119)
                      ·
                        rfl

theorem cell23_5727303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_5727303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727303 prefixEnd_5727303 := by exact prefixLift 5727303
  have htrace : WordTrace (prefixWord ++ tailWord_5727303) baseStart_5727303 baseEnd_5727303 := by
    simpa [prefixWord, tailWord_5727303, baseEnd_5727303] using wordTrace_append hprefix tailTrace_5727303
  have hstable : (prefixWord ++ tailWord_5727303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727303).length < 2 ^ (prefixWord ++ tailWord_5727303).sum := by decide
  have hdescent : baseEnd_5727303 < baseStart_5727303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727333 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 1, 4, 2]
def baseStart_5727333 : Nat := 118140960795 + 5727333 * 2 ^ 59
def prefixEnd_5727333 : Nat := 4983230072969 + 3 ^ 40 * 5727333 * 2
def baseEnd_5727333 : Nat := 2940874697357145516997981

theorem tailTrace_5727333 : CollatzResearch.WordTrace tailWord_5727333 prefixEnd_5727333 2940874697357145516997981 := by
  unfold tailWord_5727333
  simp only [CollatzResearch.WordTrace]
  refine ⟨208892995759858166446962653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139261997173238777631308435 208892995759858166446962653)
  ·
    refine ⟨78334873409946812417610995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208892995759858166446962653 78334873409946812417610995)
    ·
      refine ⟨117502310114920218626416493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78334873409946812417610995 117502310114920218626416493)
      ·
        refine ⟨44063366293095081984906185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117502310114920218626416493 44063366293095081984906185)
        ·
          refine ⟨33047524719821311488679639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44063366293095081984906185 33047524719821311488679639)
          ·
            refine ⟨49571287079731967233019459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33047524719821311488679639 49571287079731967233019459)
            ·
              refine ⟨74356930619597950849529189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49571287079731967233019459 74356930619597950849529189)
              ·
                refine ⟨13941924491174615784286723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74356930619597950849529189 13941924491174615784286723)
                ·
                  refine ⟨20912886736761923676430085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13941924491174615784286723 20912886736761923676430085)
                  ·
                    refine ⟨3921166263142860689330641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20912886736761923676430085 3921166263142860689330641)
                    ·
                      refine ⟨2940874697357145516997981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921166263142860689330641 2940874697357145516997981)
                      ·
                        rfl

theorem cell23_5727333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_5727333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727333 prefixEnd_5727333 := by exact prefixLift 5727333
  have htrace : WordTrace (prefixWord ++ tailWord_5727333) baseStart_5727333 baseEnd_5727333 := by
    simpa [prefixWord, tailWord_5727333, baseEnd_5727333] using wordTrace_append hprefix tailTrace_5727333
  have hstable : (prefixWord ++ tailWord_5727333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727333).length < 2 ^ (prefixWord ++ tailWord_5727333).sum := by decide
  have hdescent : baseEnd_5727333 < baseStart_5727333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727337 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 1, 3, 2]
def baseStart_5727337 : Nat := 118140960795 + 5727337 * 2 ^ 59
def prefixEnd_5727337 : Nat := 4983230072969 + 3 ^ 40 * 5727337 * 2
def baseEnd_5727337 : Nat := 2940876751279763501347963

theorem tailTrace_5727337 : CollatzResearch.WordTrace tailWord_5727337 prefixEnd_5727337 2940876751279763501347963 := by
  unfold tailWord_5727337
  simp only [CollatzResearch.WordTrace]
  refine ⟨208893141651843675130108265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139262094434562450086738843 208893141651843675130108265)
  ·
    refine ⟨156669856238882756347581199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208893141651843675130108265 156669856238882756347581199)
    ·
      refine ⟨235004784358324134521371799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156669856238882756347581199 235004784358324134521371799)
      ·
        refine ⟨352507176537486201782057699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235004784358324134521371799 352507176537486201782057699)
        ·
          refine ⟨528760764806229302673086549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352507176537486201782057699 528760764806229302673086549)
          ·
            refine ⟨6196415212572999640700233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 528760764806229302673086549 6196415212572999640700233)
            ·
              refine ⟨4647311409429749730525175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6196415212572999640700233 4647311409429749730525175)
              ·
                refine ⟨6970967114144624595787763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647311409429749730525175 6970967114144624595787763)
                ·
                  refine ⟨10456450671216936893681645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6970967114144624595787763 10456450671216936893681645)
                  ·
                    refine ⟨3921169001706351335130617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10456450671216936893681645 3921169001706351335130617)
                    ·
                      refine ⟨2940876751279763501347963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921169001706351335130617 2940876751279763501347963)
                      ·
                        rfl

theorem cell23_5727337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 1, 3, 2].length) (baseStart_5727337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727337 prefixEnd_5727337 := by exact prefixLift 5727337
  have htrace : WordTrace (prefixWord ++ tailWord_5727337) baseStart_5727337 baseEnd_5727337 := by
    simpa [prefixWord, tailWord_5727337, baseEnd_5727337] using wordTrace_append hprefix tailTrace_5727337
  have hstable : (prefixWord ++ tailWord_5727337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727337).length < 2 ^ (prefixWord ++ tailWord_5727337).sum := by decide
  have hdescent : baseEnd_5727337 < baseStart_5727337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727346 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_5727346 : Nat := 118140960795 + 5727346 * 2 ^ 59
def prefixEnd_5727346 : Nat := 4983230072969 + 3 ^ 40 * 5727346 * 2
def baseEnd_5727346 : Nat := 2940881372605653966135421

theorem tailTrace_5727346 : CollatzResearch.WordTrace tailWord_5727346 prefixEnd_5727346 2940881372605653966135421 := by
  unfold tailWord_5727346
  simp only [CollatzResearch.WordTrace]
  refine ⟨52223367477202767416796473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139262313272540713111457261 52223367477202767416796473)
  ·
    refine ⟨39167525607902075562597355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52223367477202767416796473 39167525607902075562597355)
    ·
      refine ⟨58751288411853113343896033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39167525607902075562597355 58751288411853113343896033)
      ·
        refine ⟨44063466308889835007922025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58751288411853113343896033 44063466308889835007922025)
        ·
          refine ⟨33047599731667376255941519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44063466308889835007922025 33047599731667376255941519)
          ·
            refine ⟨49571399597501064383912279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33047599731667376255941519 49571399597501064383912279)
            ·
              refine ⟨74357099396251596575868419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49571399597501064383912279 74357099396251596575868419)
              ·
                refine ⟨111535649094377394863802629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74357099396251596575868419 111535649094377394863802629)
                ·
                  refine ⟨20912934205195761536962993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111535649094377394863802629 20912934205195761536962993)
                  ·
                    refine ⟨15684700653896821152722245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20912934205195761536962993 15684700653896821152722245)
                    ·
                      refine ⟨2940881372605653966135421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15684700653896821152722245 2940881372605653966135421)
                      ·
                        rfl

theorem cell23_5727346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_5727346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727346 prefixEnd_5727346 := by exact prefixLift 5727346
  have htrace : WordTrace (prefixWord ++ tailWord_5727346) baseStart_5727346 baseEnd_5727346 := by
    simpa [prefixWord, tailWord_5727346, baseEnd_5727346] using wordTrace_append hprefix tailTrace_5727346
  have hstable : (prefixWord ++ tailWord_5727346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727346).length < 2 ^ (prefixWord ++ tailWord_5727346).sum := by decide
  have hdescent : baseEnd_5727346 < baseStart_5727346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727356 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 7]
def baseStart_5727356 : Nat := 118140960795 + 5727356 * 2 ^ 59
def prefixEnd_5727356 : Nat := 4983230072969 + 3 ^ 40 * 5727356 * 2
def baseEnd_5727356 : Nat := 326765167490244325223375

theorem tailTrace_5727356 : CollatzResearch.WordTrace tailWord_5727356 prefixEnd_5727356 326765167490244325223375 := by
  unfold tailWord_5727356
  simp only [CollatzResearch.WordTrace]
  refine ⟨104446917319387420687524961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139262556425849894250033281 104446917319387420687524961)
  ·
    refine ⟨78335187989540565515643721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104446917319387420687524961 78335187989540565515643721)
    ·
      refine ⟨58751390992155424136732791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78335187989540565515643721 58751390992155424136732791)
      ·
        refine ⟨88127086488233136205099187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58751390992155424136732791 88127086488233136205099187)
        ·
          refine ⟨132190629732349704307648781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88127086488233136205099187 132190629732349704307648781)
          ·
            refine ⟨49571486149631139115368293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132190629732349704307648781 49571486149631139115368293)
            ·
              refine ⟨9294653653055838584131555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49571486149631139115368293 9294653653055838584131555)
              ·
                refine ⟨13941980479583757876197333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9294653653055838584131555 13941980479583757876197333)
                ·
                  refine ⟨326765167490244325223375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13941980479583757876197333 326765167490244325223375)
                  ·
                    rfl

theorem cell23_5727356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_5727356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727356 prefixEnd_5727356 := by exact prefixLift 5727356
  have htrace : WordTrace (prefixWord ++ tailWord_5727356) baseStart_5727356 baseEnd_5727356 := by
    simpa [prefixWord, tailWord_5727356, baseEnd_5727356] using wordTrace_append hprefix tailTrace_5727356
  have hstable : (prefixWord ++ tailWord_5727356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727356).length < 2 ^ (prefixWord ++ tailWord_5727356).sum := by decide
  have hdescent : baseEnd_5727356 < baseStart_5727356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727423 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 2, 4, 2]
def baseStart_5727423 : Nat := 118140960795 + 5727423 * 2 ^ 59
def prefixEnd_5727423 : Nat := 4983230072969 + 3 ^ 40 * 5727423 * 2
def baseEnd_5727423 : Nat := 2940920910616050164872567

theorem tailTrace_5727423 : CollatzResearch.WordTrace tailWord_5727423 prefixEnd_5727423 2940920910616050164872567 := by
  unfold tailWord_5727423
  simp only [CollatzResearch.WordTrace]
  refine ⟨208896278329532111817738923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139264185553021407878492615 208896278329532111817738923)
  ·
    refine ⟨313344417494298167726608385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208896278329532111817738923 313344417494298167726608385)
    ·
      refine ⟨235008313120723625794956289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313344417494298167726608385 235008313120723625794956289)
      ·
        refine ⟨176256234840542719346217217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235008313120723625794956289 176256234840542719346217217)
        ·
          refine ⟨132192176130407039509662913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176256234840542719346217217 132192176130407039509662913)
          ·
            refine ⟨99144132097805279632247185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132192176130407039509662913 99144132097805279632247185)
            ·
              refine ⟨74358099073353959724185389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99144132097805279632247185 74358099073353959724185389)
              ·
                refine ⟨27884287152507734896569521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74358099073353959724185389 27884287152507734896569521)
                ·
                  refine ⟨20913215364380801172427141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27884287152507734896569521 20913215364380801172427141)
                  ·
                    refine ⟨3921227880821400219830089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20913215364380801172427141 3921227880821400219830089)
                    ·
                      refine ⟨2940920910616050164872567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921227880821400219830089 2940920910616050164872567)
                      ·
                        rfl

theorem cell23_5727423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 4, 2].length) (baseStart_5727423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727423 prefixEnd_5727423 := by exact prefixLift 5727423
  have htrace : WordTrace (prefixWord ++ tailWord_5727423) baseStart_5727423 baseEnd_5727423 := by
    simpa [prefixWord, tailWord_5727423, baseEnd_5727423] using wordTrace_append hprefix tailTrace_5727423
  have hstable : (prefixWord ++ tailWord_5727423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727423).length < 2 ^ (prefixWord ++ tailWord_5727423).sum := by decide
  have hdescent : baseEnd_5727423 < baseStart_5727423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727450 : List Nat := [3, 1, 1, 2, 2, 1, 1, 7, 1, 4]
def baseStart_5727450 : Nat := 118140960795 + 5727450 * 2 ^ 59
def prefixEnd_5727450 : Nat := 4983230072969 + 3 ^ 40 * 5727450 * 2
def baseEnd_5727450 : Nat := 980311591531240519744981

theorem tailTrace_5727450 : CollatzResearch.WordTrace tailWord_5727450 prefixEnd_5727450 980311591531240519744981 := by
  unfold tailWord_5727450
  simp only [CollatzResearch.WordTrace]
  refine ⟨52224315775108573857242951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139264842066956196952647869 52224315775108573857242951)
  ·
    refine ⟨78336473662662860785864427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52224315775108573857242951 78336473662662860785864427)
    ·
      refine ⟨117504710493994291178796641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78336473662662860785864427 117504710493994291178796641)
      ·
        refine ⟨88128532870495718384097481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117504710493994291178796641 88128532870495718384097481)
        ·
          refine ⟨66096399652871788788073111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88128532870495718384097481 66096399652871788788073111)
          ·
            refine ⟨99144599479307683182109667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66096399652871788788073111 99144599479307683182109667)
            ·
              refine ⟨148716899218961524773164501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99144599479307683182109667 148716899218961524773164501)
              ·
                refine ⟨3485552325444410736871043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 148716899218961524773164501 3485552325444410736871043)
                ·
                  refine ⟨5228328488166616105306565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485552325444410736871043 5228328488166616105306565)
                  ·
                    refine ⟨980311591531240519744981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5228328488166616105306565 980311591531240519744981)
                    ·
                      rfl

theorem cell23_5727450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_5727450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727450 prefixEnd_5727450 := by exact prefixLift 5727450
  have htrace : WordTrace (prefixWord ++ tailWord_5727450) baseStart_5727450 baseEnd_5727450 := by
    simpa [prefixWord, tailWord_5727450, baseEnd_5727450] using wordTrace_append hprefix tailTrace_5727450
  have hstable : (prefixWord ++ tailWord_5727450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727450).length < 2 ^ (prefixWord ++ tailWord_5727450).sum := by decide
  have hdescent : baseEnd_5727450 < baseStart_5727450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727467 : List Nat := [1, 1, 1, 1, 2, 6, 4, 2, 1, 4]
def baseStart_5727467 : Nat := 118140960795 + 5727467 * 2 ^ 59
def prefixEnd_5727467 : Nat := 4983230072969 + 3 ^ 40 * 5727467 * 2
def baseEnd_5727467 : Nat := 980314501254949330907455

theorem tailTrace_5727467 : CollatzResearch.WordTrace tailWord_5727467 prefixEnd_5727467 980314501254949330907455 := by
  unfold tailWord_5727467
  simp only [CollatzResearch.WordTrace]
  refine ⟨208897883141372707332340655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139265255427581804888227103 208897883141372707332340655)
  ·
    refine ⟨313346824712059060998510983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208897883141372707332340655 313346824712059060998510983)
    ·
      refine ⟨470020237068088591497766475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313346824712059060998510983 470020237068088591497766475)
      ·
        refine ⟨705030355602132887246649713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470020237068088591497766475 705030355602132887246649713)
        ·
          refine ⟨528772766701599665434987285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705030355602132887246649713 528772766701599665434987285)
          ·
            refine ⟨24786223439137484317265029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 528772766701599665434987285 24786223439137484317265029)
            ·
              refine ⟨4647416894838278309487193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24786223439137484317265029 4647416894838278309487193)
              ·
                refine ⟨3485562671128708732115395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4647416894838278309487193 3485562671128708732115395)
                ·
                  refine ⟨5228344006693063098173093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485562671128708732115395 5228344006693063098173093)
                  ·
                    refine ⟨980314501254949330907455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5228344006693063098173093 980314501254949330907455)
                    ·
                      rfl

theorem cell23_5727467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 1, 4].length) (baseStart_5727467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727467 prefixEnd_5727467 := by exact prefixLift 5727467
  have htrace : WordTrace (prefixWord ++ tailWord_5727467) baseStart_5727467 baseEnd_5727467 := by
    simpa [prefixWord, tailWord_5727467, baseEnd_5727467] using wordTrace_append hprefix tailTrace_5727467
  have hstable : (prefixWord ++ tailWord_5727467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727467).length < 2 ^ (prefixWord ++ tailWord_5727467).sum := by decide
  have hdescent : baseEnd_5727467 < baseStart_5727467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727493 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 1, 5]
def baseStart_5727493 : Nat := 118140960795 + 5727493 * 2 ^ 59
def prefixEnd_5727493 : Nat := 4983230072969 + 3 ^ 40 * 5727493 * 2
def baseEnd_5727493 : Nat := 980318951420621630332415

theorem tailTrace_5727493 : CollatzResearch.WordTrace tailWord_5727493 prefixEnd_5727493 980318951420621630332415 := by
  unfold tailWord_5727493
  simp only [CollatzResearch.WordTrace]
  refine ⟨208898831439278513772787133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139265887626185675848524755 208898831439278513772787133)
  ·
    refine ⟨78337061789729442664795175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208898831439278513772787133 78337061789729442664795175)
    ·
      refine ⟨117505592684594163997192763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78337061789729442664795175 117505592684594163997192763)
      ·
        refine ⟨176258389026891245995789145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117505592684594163997192763 176258389026891245995789145)
        ·
          refine ⟨132193791770168434496841859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176258389026891245995789145 132193791770168434496841859)
          ·
            refine ⟨198290687655252651745262789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132193791770168434496841859 198290687655252651745262789)
            ·
              refine ⟨37179503935359872202236773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198290687655252651745262789 37179503935359872202236773)
              ·
                refine ⟨6971156987879976037919395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37179503935359872202236773 6971156987879976037919395)
                ·
                  refine ⟨10456735481819964056879093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6971156987879976037919395 10456735481819964056879093)
                  ·
                    refine ⟨980318951420621630332415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10456735481819964056879093 980318951420621630332415)
                    ·
                      rfl

theorem cell23_5727493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_5727493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727493 prefixEnd_5727493 := by exact prefixLift 5727493
  have htrace : WordTrace (prefixWord ++ tailWord_5727493) baseStart_5727493 baseEnd_5727493 := by
    simpa [prefixWord, tailWord_5727493, baseEnd_5727493] using wordTrace_append hprefix tailTrace_5727493
  have hstable : (prefixWord ++ tailWord_5727493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727493).length < 2 ^ (prefixWord ++ tailWord_5727493).sum := by decide
  have hdescent : baseEnd_5727493 < baseStart_5727493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727500 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 1, 5, 2]
def baseStart_5727500 : Nat := 118140960795 + 5727500 * 2 ^ 59
def prefixEnd_5727500 : Nat := 4983230072969 + 3 ^ 40 * 5727500 * 2
def baseEnd_5727500 : Nat := 2940960448626446363609713

theorem tailTrace_5727500 : CollatzResearch.WordTrace tailWord_5727500 prefixEnd_5727500 2940960448626446363609713 := by
  unfold tailWord_5727500
  simp only [CollatzResearch.WordTrace]
  refine ⟨104449543375126576984145977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139266057833502102645527969 104449543375126576984145977)
  ·
    refine ⟨78337157531344932738109483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104449543375126576984145977 78337157531344932738109483)
    ·
      refine ⟨117505736297017399107164225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78337157531344932738109483 117505736297017399107164225)
      ·
        refine ⟨88129302222763049330373169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117505736297017399107164225 88129302222763049330373169)
        ·
          refine ⟨66096976667072286997779877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88129302222763049330373169 66096976667072286997779877)
          ·
            refine ⟨12393183125076053812083727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66096976667072286997779877 12393183125076053812083727)
            ·
              refine ⟨18589774687614080718125591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12393183125076053812083727 18589774687614080718125591)
              ·
                refine ⟨27884662031421121077188387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18589774687614080718125591 27884662031421121077188387)
                ·
                  refine ⟨41826993047131681615782581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27884662031421121077188387 41826993047131681615782581)
                  ·
                    refine ⟨3921280598168595151479617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41826993047131681615782581 3921280598168595151479617)
                    ·
                      refine ⟨2940960448626446363609713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921280598168595151479617 2940960448626446363609713)
                      ·
                        rfl

theorem cell23_5727500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_5727500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727500 prefixEnd_5727500 := by exact prefixLift 5727500
  have htrace : WordTrace (prefixWord ++ tailWord_5727500) baseStart_5727500 baseEnd_5727500 := by
    simpa [prefixWord, tailWord_5727500, baseEnd_5727500] using wordTrace_append hprefix tailTrace_5727500
  have hstable : (prefixWord ++ tailWord_5727500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727500).length < 2 ^ (prefixWord ++ tailWord_5727500).sum := by decide
  have hdescent : baseEnd_5727500 < baseStart_5727500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727513 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 3, 8, 2]
def baseStart_5727513 : Nat := 118140960795 + 5727513 * 2 ^ 59
def prefixEnd_5727513 : Nat := 4983230072969 + 3 ^ 40 * 5727513 * 2
def baseEnd_5727513 : Nat := 2940967123874954812747153

theorem tailTrace_5727513 : CollatzResearch.WordTrace tailWord_5727513 prefixEnd_5727513 2940967123874954812747153 := by
  unfold tailWord_5727513
  simp only [CollatzResearch.WordTrace]
  refine ⟨208899560899206057188515193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139266373932804038125676795 208899560899206057188515193)
  ·
    refine ⟨156674670674404542891386395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208899560899206057188515193 156674670674404542891386395)
    ·
      refine ⟨235012006011606814337079593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156674670674404542891386395 235012006011606814337079593)
      ·
        refine ⟨176259004508705110752809695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235012006011606814337079593 176259004508705110752809695)
        ·
          refine ⟨264388506763057666129214543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176259004508705110752809695 264388506763057666129214543)
          ·
            refine ⟨396582760144586499193821815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264388506763057666129214543 396582760144586499193821815)
            ·
              refine ⟨594874140216879748790732723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396582760144586499193821815 594874140216879748790732723)
              ·
                refine ⟨892311210325319623186099085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594874140216879748790732723 892311210325319623186099085)
                ·
                  refine ⟨334616703871994858694787157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892311210325319623186099085 334616703871994858694787157)
                  ·
                    refine ⟨3921289498499939750329537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 334616703871994858694787157 3921289498499939750329537)
                    ·
                      refine ⟨2940967123874954812747153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921289498499939750329537 2940967123874954812747153)
                      ·
                        rfl

theorem cell23_5727513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 8, 2].length) (baseStart_5727513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727513 prefixEnd_5727513 := by exact prefixLift 5727513
  have htrace : WordTrace (prefixWord ++ tailWord_5727513) baseStart_5727513 baseEnd_5727513 := by
    simpa [prefixWord, tailWord_5727513, baseEnd_5727513] using wordTrace_append hprefix tailTrace_5727513
  have hstable : (prefixWord ++ tailWord_5727513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727513).length < 2 ^ (prefixWord ++ tailWord_5727513).sum := by decide
  have hdescent : baseEnd_5727513 < baseStart_5727513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727536 : List Nat := [2, 1, 1, 1, 2, 2, 4, 10]
def baseStart_5727536 : Nat := 118140960795 + 5727536 * 2 ^ 59
def prefixEnd_5727536 : Nat := 4983230072969 + 3 ^ 40 * 5727536 * 2
def baseEnd_5727536 : Nat := 108925145701111415657761

theorem tailTrace_5727536 : CollatzResearch.WordTrace tailWord_5727536 prefixEnd_5727536 108925145701111415657761 := by
  unfold tailWord_5727536
  simp only [CollatzResearch.WordTrace]
  refine ⟨104450199889061366058301231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139266933185415154744401641 104450199889061366058301231)
  ·
    refine ⟨156675299833592049087451847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104450199889061366058301231 156675299833592049087451847)
    ·
      refine ⟨235012949750388073631177771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156675299833592049087451847 235012949750388073631177771)
      ·
        refine ⟨352519424625582110446766657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235012949750388073631177771 352519424625582110446766657)
        ·
          refine ⟨264389568469186582835074993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352519424625582110446766657 264389568469186582835074993)
          ·
            refine ⟨198292176351889937126306245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264389568469186582835074993 198292176351889937126306245)
            ·
              refine ⟨37179783065979363211182421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198292176351889937126306245 37179783065979363211182421)
              ·
                refine ⟨108925145701111415657761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37179783065979363211182421 108925145701111415657761)
                ·
                  rfl

theorem cell23_5727536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 10].length) (baseStart_5727536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727536 prefixEnd_5727536 := by exact prefixLift 5727536
  have htrace : WordTrace (prefixWord ++ tailWord_5727536) baseStart_5727536 baseEnd_5727536 := by
    simpa [prefixWord, tailWord_5727536, baseEnd_5727536] using wordTrace_append hprefix tailTrace_5727536
  have hstable : (prefixWord ++ tailWord_5727536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727536).length < 2 ^ (prefixWord ++ tailWord_5727536).sum := by decide
  have hdescent : baseEnd_5727536 < baseStart_5727536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727591 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 2, 4]
def baseStart_5727591 : Nat := 118140960795 + 5727591 * 2 ^ 59
def prefixEnd_5727591 : Nat := 4983230072969 + 3 ^ 40 * 5727591 * 2
def baseEnd_5727591 : Nat := 980335725122001835857265

theorem tailTrace_5727591 : CollatzResearch.WordTrace tailWord_5727591 prefixEnd_5727591 980335725122001835857265 := by
  unfold tailWord_5727591
  simp only [CollatzResearch.WordTrace]
  refine ⟨208902405792923476509854627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139268270528615651006569751 208902405792923476509854627)
  ·
    refine ⟨313353608689385214764781941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208902405792923476509854627 313353608689385214764781941)
    ·
      refine ⟨29376900814629863884198307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 313353608689385214764781941 29376900814629863884198307)
      ·
        refine ⟨44065351221944795826297461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29376900814629863884198307 44065351221944795826297461)
        ·
          refine ⟨4131126677057324608715387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44065351221944795826297461 4131126677057324608715387)
          ·
            refine ⟨6196690015585986913073081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4131126677057324608715387 6196690015585986913073081)
            ·
              refine ⟨4647517511689490184804811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6196690015585986913073081 4647517511689490184804811)
              ·
                refine ⟨6971276267534235277207217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647517511689490184804811 6971276267534235277207217)
                ·
                  refine ⟨5228457200650676457905413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6971276267534235277207217 5228457200650676457905413)
                  ·
                    refine ⟨980335725122001835857265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5228457200650676457905413 980335725122001835857265)
                    ·
                      rfl

theorem cell23_5727591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_5727591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727591 prefixEnd_5727591 := by exact prefixLift 5727591
  have htrace : WordTrace (prefixWord ++ tailWord_5727591) baseStart_5727591 baseEnd_5727591 := by
    simpa [prefixWord, tailWord_5727591, baseEnd_5727591] using wordTrace_append hprefix tailTrace_5727591
  have hstable : (prefixWord ++ tailWord_5727591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727591).length < 2 ^ (prefixWord ++ tailWord_5727591).sum := by decide
  have hdescent : baseEnd_5727591 < baseStart_5727591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727633 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_5727633 : Nat := 118140960795 + 5727633 * 2 ^ 59
def prefixEnd_5727633 : Nat := 4983230072969 + 3 ^ 40 * 5727633 * 2
def baseEnd_5727633 : Nat := 2941028741553494343246601

theorem tailTrace_5727633 : CollatzResearch.WordTrace tailWord_5727633 prefixEnd_5727633 2941028741553494343246601 := by
  unfold tailWord_5727633
  simp only [CollatzResearch.WordTrace]
  refine ⟨208903937658771317682883553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139269291772514211788589035 208903937658771317682883553)
  ·
    refine ⟨156677953244078488262162665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208903937658771317682883553 156677953244078488262162665)
    ·
      refine ⟨117508464933058866196621999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156677953244078488262162665 117508464933058866196621999)
      ·
        refine ⟨176262697399588299294932999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117508464933058866196621999 176262697399588299294932999)
        ·
          refine ⟨264394046099382448942399499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176262697399588299294932999 264394046099382448942399499)
          ·
            refine ⟨396591069149073673413599249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264394046099382448942399499 396591069149073673413599249)
            ·
              refine ⟨297443301861805255060199437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396591069149073673413599249 297443301861805255060199437)
              ·
                refine ⟨111541238198176970647574789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297443301861805255060199437 111541238198176970647574789)
                ·
                  refine ⟨20913982162158181996420273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111541238198176970647574789 20913982162158181996420273)
                  ·
                    refine ⟨15685486621618636497315205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20913982162158181996420273 15685486621618636497315205)
                    ·
                      refine ⟨2941028741553494343246601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15685486621618636497315205 2941028741553494343246601)
                      ·
                        rfl

theorem cell23_5727633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_5727633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727633 prefixEnd_5727633 := by exact prefixLift 5727633
  have htrace : WordTrace (prefixWord ++ tailWord_5727633) baseStart_5727633 baseEnd_5727633 := by
    simpa [prefixWord, tailWord_5727633, baseEnd_5727633] using wordTrace_append hprefix tailTrace_5727633
  have hstable : (prefixWord ++ tailWord_5727633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727633).length < 2 ^ (prefixWord ++ tailWord_5727633).sum := by decide
  have hdescent : baseEnd_5727633 < baseStart_5727633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727637 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 4, 2, 2]
def baseStart_5727637 : Nat := 118140960795 + 5727637 * 2 ^ 59
def prefixEnd_5727637 : Nat := 4983230072969 + 3 ^ 40 * 5727637 * 2
def baseEnd_5727637 : Nat := 2941030795476112327596583

theorem tailTrace_5727637 : CollatzResearch.WordTrace tailWord_5727637 prefixEnd_5727637 2941030795476112327596583 := by
  unfold tailWord_5727637
  simp only [CollatzResearch.WordTrace]
  refine ⟨208904083550756826366029165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139269389033837884244019443 208904083550756826366029165)
  ·
    refine ⟨78339031331533809887260937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208904083550756826366029165 78339031331533809887260937)
    ·
      refine ⟨58754273498650357415445703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78339031331533809887260937 58754273498650357415445703)
      ·
        refine ⟨88131410247975536123168555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58754273498650357415445703 88131410247975536123168555)
        ·
          refine ⟨132197115371963304184752833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88131410247975536123168555 132197115371963304184752833)
          ·
            refine ⟨99147836528972478138564625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132197115371963304184752833 99147836528972478138564625)
            ·
              refine ⟨74360877396729358603923469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99147836528972478138564625 74360877396729358603923469)
              ·
                refine ⟨27885329023773509476471301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74360877396729358603923469 27885329023773509476471301)
                ·
                  refine ⟨5228499191957533026838369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27885329023773509476471301 5228499191957533026838369)
                  ·
                    refine ⟨3921374393968149770128777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5228499191957533026838369 3921374393968149770128777)
                    ·
                      refine ⟨2941030795476112327596583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921374393968149770128777 2941030795476112327596583)
                      ·
                        rfl

theorem cell23_5727637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_5727637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727637 prefixEnd_5727637 := by exact prefixLift 5727637
  have htrace : WordTrace (prefixWord ++ tailWord_5727637) baseStart_5727637 baseEnd_5727637 := by
    simpa [prefixWord, tailWord_5727637, baseEnd_5727637] using wordTrace_append hprefix tailTrace_5727637
  have hstable : (prefixWord ++ tailWord_5727637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727637).length < 2 ^ (prefixWord ++ tailWord_5727637).sum := by decide
  have hdescent : baseEnd_5727637 < baseStart_5727637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727650 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_5727650 : Nat := 118140960795 + 5727650 * 2 ^ 59
def prefixEnd_5727650 : Nat := 4983230072969 + 3 ^ 40 * 5727650 * 2
def baseEnd_5727650 : Nat := 2941037470724620776734023

theorem tailTrace_5727650 : CollatzResearch.WordTrace tailWord_5727650 prefixEnd_5727650 2941037470724620776734023 := by
  unfold tailWord_5727650
  simp only [CollatzResearch.WordTrace]
  refine ⟨52226139424927432396563101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139269705133139819724168269 52226139424927432396563101)
  ·
    refine ⟨19584802284347787148711163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52226139424927432396563101 19584802284347787148711163)
    ·
      refine ⟨29377203426521680723066745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19584802284347787148711163 29377203426521680723066745)
      ·
        refine ⟨22032902569891260542300059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29377203426521680723066745 22032902569891260542300059)
        ·
          refine ⟨33049353854836890813450089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22032902569891260542300059 33049353854836890813450089)
          ·
            refine ⟨24787015391127668110087567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33049353854836890813450089 24787015391127668110087567)
            ·
              refine ⟨37180523086691502165131351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24787015391127668110087567 37180523086691502165131351)
              ·
                refine ⟨55770784630037253247697027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37180523086691502165131351 55770784630037253247697027)
                ·
                  refine ⟨83656176945055879871545541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55770784630037253247697027 83656176945055879871545541)
                  ·
                    refine ⟨15685533177197977475914789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83656176945055879871545541 15685533177197977475914789)
                    ·
                      refine ⟨2941037470724620776734023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15685533177197977475914789 2941037470724620776734023)
                      ·
                        rfl

theorem cell23_5727650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_5727650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727650 prefixEnd_5727650 := by exact prefixLift 5727650
  have htrace : WordTrace (prefixWord ++ tailWord_5727650) baseStart_5727650 baseEnd_5727650 := by
    simpa [prefixWord, tailWord_5727650, baseEnd_5727650] using wordTrace_append hprefix tailTrace_5727650
  have hstable : (prefixWord ++ tailWord_5727650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727650).length < 2 ^ (prefixWord ++ tailWord_5727650).sum := by decide
  have hdescent : baseEnd_5727650 < baseStart_5727650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727677 : List Nat := [1, 4, 1, 2, 2, 1, 4, 3, 5]
def baseStart_5727677 : Nat := 118140960795 + 5727677 * 2 ^ 59
def prefixEnd_5727677 : Nat := 4983230072969 + 3 ^ 40 * 5727677 * 2
def baseEnd_5727677 : Nat := 326783481633588019010711

theorem tailTrace_5727677 : CollatzResearch.WordTrace tailWord_5727677 prefixEnd_5727677 326783481633588019010711 := by
  unfold tailWord_5727677
  simp only [CollatzResearch.WordTrace]
  refine ⟨208905542470611913197485285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139270361647074608798323523 208905542470611913197485285)
  ·
    refine ⟨39169789213239733724528491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208905542470611913197485285 39169789213239733724528491)
    ·
      refine ⟨58754683819859600586792737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39169789213239733724528491 58754683819859600586792737)
      ·
        refine ⟨44066012864894700440094553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58754683819859600586792737 44066012864894700440094553)
        ·
          refine ⟨33049509648671025330070915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44066012864894700440094553 33049509648671025330070915)
          ·
            refine ⟨49574264473006537995106373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33049509648671025330070915 49574264473006537995106373)
            ·
              refine ⟨9295174588688725874082445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49574264473006537995106373 9295174588688725874082445)
              ·
                refine ⟨3485690470758272202780917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9295174588688725874082445 3485690470758272202780917)
                ·
                  refine ⟨326783481633588019010711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3485690470758272202780917 326783481633588019010711)
                  ·
                    rfl

theorem cell23_5727677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_5727677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727677 prefixEnd_5727677 := by exact prefixLift 5727677
  have htrace : WordTrace (prefixWord ++ tailWord_5727677) baseStart_5727677 baseEnd_5727677 := by
    simpa [prefixWord, tailWord_5727677, baseEnd_5727677] using wordTrace_append hprefix tailTrace_5727677
  have hstable : (prefixWord ++ tailWord_5727677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727677).length < 2 ^ (prefixWord ++ tailWord_5727677).sum := by decide
  have hdescent : baseEnd_5727677 < baseStart_5727677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727682 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_5727682 : Nat := 118140960795 + 5727682 * 2 ^ 59
def prefixEnd_5727682 : Nat := 4983230072969 + 3 ^ 40 * 5727682 * 2
def baseEnd_5727682 : Nat := 2941053902105564651533877

theorem tailTrace_5727682 : CollatzResearch.WordTrace tailWord_5727682 prefixEnd_5727682 2941053902105564651533877 := by
  unfold tailWord_5727682
  simp only [CollatzResearch.WordTrace]
  refine ⟨52226431208898449762854325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139270483223729199367611533 52226431208898449762854325)
  ·
    refine ⟨4896227925834229665267593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52226431208898449762854325 4896227925834229665267593)
    ·
      refine ⟨3672170944375672248950695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4896227925834229665267593 3672170944375672248950695)
      ·
        refine ⟨5508256416563508373426043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3672170944375672248950695 5508256416563508373426043)
        ·
          refine ⟨8262384624845262560139065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5508256416563508373426043 8262384624845262560139065)
          ·
            refine ⟨6196788468633946920104299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8262384624845262560139065 6196788468633946920104299)
            ·
              refine ⟨9295182702950920380156449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6196788468633946920104299 9295182702950920380156449)
              ·
                refine ⟨6971387027213190285117337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9295182702950920380156449 6971387027213190285117337)
                ·
                  refine ⟨5228540270409892713838003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6971387027213190285117337 5228540270409892713838003)
                  ·
                    refine ⟨7842810405614839070757005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5228540270409892713838003 7842810405614839070757005)
                    ·
                      refine ⟨2941053902105564651533877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7842810405614839070757005 2941053902105564651533877)
                      ·
                        rfl

theorem cell23_5727682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_5727682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727682 prefixEnd_5727682 := by exact prefixLift 5727682
  have htrace : WordTrace (prefixWord ++ tailWord_5727682) baseStart_5727682 baseEnd_5727682 := by
    simpa [prefixWord, tailWord_5727682, baseEnd_5727682] using wordTrace_append hprefix tailTrace_5727682
  have hstable : (prefixWord ++ tailWord_5727682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727682).length < 2 ^ (prefixWord ++ tailWord_5727682).sum := by decide
  have hdescent : baseEnd_5727682 < baseStart_5727682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727683 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 5]
def baseStart_5727683 : Nat := 118140960795 + 5727683 * 2 ^ 59
def prefixEnd_5727683 : Nat := 4983230072969 + 3 ^ 40 * 5727683 * 2
def baseEnd_5727683 : Nat := 2941054415586219147621371

theorem tailTrace_5727683 : CollatzResearch.WordTrace tailWord_5727683 prefixEnd_5727683 2941054415586219147621371 := by
  unfold tailWord_5727683
  simp only [CollatzResearch.WordTrace]
  refine ⟨208905761308590176222203703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139270507539060117481469135 208905761308590176222203703)
  ·
    refine ⟨313358641962885264333305555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208905761308590176222203703 313358641962885264333305555)
    ·
      refine ⟨470037962944327896499958333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313358641962885264333305555 470037962944327896499958333)
      ·
        refine ⟨176264236104122961187484375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 470037962944327896499958333 176264236104122961187484375)
        ·
          refine ⟨264396354156184441781226563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176264236104122961187484375 264396354156184441781226563)
          ·
            refine ⟨396594531234276662671839845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264396354156184441781226563 396594531234276662671839845)
            ·
              refine ⟨74361474606426874250969971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 396594531234276662671839845 74361474606426874250969971)
              ·
                refine ⟨111542211909640311376454957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74361474606426874250969971 111542211909640311376454957)
                ·
                  refine ⟨41828329466115116766170609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111542211909640311376454957 41828329466115116766170609)
                  ·
                    refine ⟨31371247099586337574627957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41828329466115116766170609 31371247099586337574627957)
                    ·
                      refine ⟨2941054415586219147621371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31371247099586337574627957 2941054415586219147621371)
                      ·
                        rfl

theorem cell23_5727683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_5727683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727683 prefixEnd_5727683 := by exact prefixLift 5727683
  have htrace : WordTrace (prefixWord ++ tailWord_5727683) baseStart_5727683 baseEnd_5727683 := by
    simpa [prefixWord, tailWord_5727683, baseEnd_5727683] using wordTrace_append hprefix tailTrace_5727683
  have hstable : (prefixWord ++ tailWord_5727683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727683).length < 2 ^ (prefixWord ++ tailWord_5727683).sum := by decide
  have hdescent : baseEnd_5727683 < baseStart_5727683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727723 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 6]
def baseStart_5727723 : Nat := 118140960795 + 5727723 * 2 ^ 59
def prefixEnd_5727723 : Nat := 4983230072969 + 3 ^ 40 * 5727723 * 2
def baseEnd_5727723 : Nat := 2941074954812398991121187

theorem tailTrace_5727723 : CollatzResearch.WordTrace tailWord_5727723 prefixEnd_5727723 2941074954812398991121187 := by
  unfold tailWord_5727723
  simp only [CollatzResearch.WordTrace]
  refine ⟨208907220228445263053659823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139271480152296842035773215 208907220228445263053659823)
  ·
    refine ⟨313360830342667894580489735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208907220228445263053659823 313360830342667894580489735)
    ·
      refine ⟨470041245514001841870734603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313360830342667894580489735 470041245514001841870734603)
      ·
        refine ⟨705061868271002762806101905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470041245514001841870734603 705061868271002762806101905)
        ·
          refine ⟨528796401203252072104576429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705061868271002762806101905 528796401203252072104576429)
          ·
            refine ⟨198298650451219527039216161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 528796401203252072104576429 198298650451219527039216161)
            ·
              refine ⟨148723987838414645279412121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198298650451219527039216161 148723987838414645279412121)
              ·
                refine ⟨111542990878810983959559091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148723987838414645279412121 111542990878810983959559091)
                ·
                  refine ⟨167314486318216475939338637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111542990878810983959559091 167314486318216475939338637)
                  ·
                    refine ⟨62742932369331178477251989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167314486318216475939338637 62742932369331178477251989)
                    ·
                      refine ⟨2941074954812398991121187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62742932369331178477251989 2941074954812398991121187)
                      ·
                        rfl

theorem cell23_5727723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_5727723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727723 prefixEnd_5727723 := by exact prefixLift 5727723
  have htrace : WordTrace (prefixWord ++ tailWord_5727723) baseStart_5727723 baseEnd_5727723 := by
    simpa [prefixWord, tailWord_5727723, baseEnd_5727723] using wordTrace_append hprefix tailTrace_5727723
  have hstable : (prefixWord ++ tailWord_5727723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727723).length < 2 ^ (prefixWord ++ tailWord_5727723).sum := by decide
  have hdescent : baseEnd_5727723 < baseStart_5727723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727754 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 3, 4]
def baseStart_5727754 : Nat := 118140960795 + 5727754 * 2 ^ 59
def prefixEnd_5727754 : Nat := 4983230072969 + 3 ^ 40 * 5727754 * 2
def baseEnd_5727754 : Nat := 980363624237562789944515

theorem tailTrace_5727754 : CollatzResearch.WordTrace tailWord_5727754 prefixEnd_5727754 980363624237562789944515 := by
  unfold tailWord_5727754
  simp only [CollatzResearch.WordTrace]
  refine ⟨52227087722833238837009579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139272233927555303565358877 52227087722833238837009579)
  ·
    refine ⟨78340631584249858255514369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52227087722833238837009579 78340631584249858255514369)
    ·
      refine ⟨58755473688187393691635777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78340631584249858255514369 58755473688187393691635777)
      ·
        refine ⟨44066605266140545268726833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58755473688187393691635777 44066605266140545268726833)
        ·
          refine ⟨33049953949605408951545125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44066605266140545268726833 33049953949605408951545125)
          ·
            refine ⟨6196866365551014178414711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33049953949605408951545125 6196866365551014178414711)
            ·
              refine ⟨9295299548326521267622067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6196866365551014178414711 9295299548326521267622067)
              ·
                refine ⟨13942949322489781901433101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9295299548326521267622067 13942949322489781901433101)
                ·
                  refine ⟨5228605995933668213037413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13942949322489781901433101 5228605995933668213037413)
                  ·
                    refine ⟨980363624237562789944515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5228605995933668213037413 980363624237562789944515)
                    ·
                      rfl

theorem cell23_5727754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_5727754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727754 prefixEnd_5727754 := by exact prefixLift 5727754
  have htrace : WordTrace (prefixWord ++ tailWord_5727754) baseStart_5727754 baseEnd_5727754 := by
    simpa [prefixWord, tailWord_5727754, baseEnd_5727754] using wordTrace_append hprefix tailTrace_5727754
  have hstable : (prefixWord ++ tailWord_5727754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727754).length < 2 ^ (prefixWord ++ tailWord_5727754).sum := by decide
  have hdescent : baseEnd_5727754 < baseStart_5727754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727805 : List Nat := [1, 4, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_5727805 : Nat := 118140960795 + 5727805 * 2 ^ 59
def prefixEnd_5727805 : Nat := 4983230072969 + 3 ^ 40 * 5727805 * 2
def baseEnd_5727805 : Nat := 980372353408689223431937

theorem tailTrace_5727805 : CollatzResearch.WordTrace tailWord_5727805 prefixEnd_5727805 980372353408689223431937 := by
  unfold tailWord_5727805
  simp only [CollatzResearch.WordTrace]
  refine ⟨208910211014148191058144869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139273474009432127372096579 208910211014148191058144869)
  ·
    refine ⟨39170664565152785823402163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208910211014148191058144869 39170664565152785823402163)
    ·
      refine ⟨58755996847729178735103245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39170664565152785823402163 58755996847729178735103245)
      ·
        refine ⟨22033498817898442025663717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58755996847729178735103245 22033498817898442025663717)
        ·
          refine ⟨4131281028355957879811947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22033498817898442025663717 4131281028355957879811947)
          ·
            refine ⟨6196921542533936819717921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4131281028355957879811947 6196921542533936819717921)
            ·
              refine ⟨4647691156900452614788441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6196921542533936819717921 4647691156900452614788441)
              ·
                refine ⟨3485768367675339461091331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4647691156900452614788441 3485768367675339461091331)
                ·
                  refine ⟨5228652551513009191636997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485768367675339461091331 5228652551513009191636997)
                  ·
                    refine ⟨980372353408689223431937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5228652551513009191636997 980372353408689223431937)
                    ·
                      rfl

theorem cell23_5727805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_5727805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727805 prefixEnd_5727805 := by exact prefixLift 5727805
  have htrace : WordTrace (prefixWord ++ tailWord_5727805) baseStart_5727805 baseEnd_5727805 := by
    simpa [prefixWord, tailWord_5727805, baseEnd_5727805] using wordTrace_append hprefix tailTrace_5727805
  have hstable : (prefixWord ++ tailWord_5727805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727805).length < 2 ^ (prefixWord ++ tailWord_5727805).sum := by decide
  have hdescent : baseEnd_5727805 < baseStart_5727805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727847 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_5727847 : Nat := 118140960795 + 5727847 * 2 ^ 59
def prefixEnd_5727847 : Nat := 4983230072969 + 3 ^ 40 * 5727847 * 2
def baseEnd_5727847 : Nat := 2941138626413556505970617

theorem tailTrace_5727847 : CollatzResearch.WordTrace tailWord_5727847 prefixEnd_5727847 2941138626413556505970617 := by
  unfold tailWord_5727847
  simp only [CollatzResearch.WordTrace]
  refine ⟨208911742879996032231173795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139274495253330688154115863 208911742879996032231173795)
  ·
    refine ⟨313367614319994048346760693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208911742879996032231173795 313367614319994048346760693)
    ·
      refine ⟨29378213842499442032508815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 313367614319994048346760693 29378213842499442032508815)
      ·
        refine ⟨44067320763749163048763223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29378213842499442032508815 44067320763749163048763223)
        ·
          refine ⟨66100981145623744573144835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44067320763749163048763223 66100981145623744573144835)
          ·
            refine ⟨99151471718435616859717253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66100981145623744573144835 99151471718435616859717253)
            ·
              refine ⟨18590900947206678161196985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99151471718435616859717253 18590900947206678161196985)
              ·
                refine ⟨13943175710405008620897739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18590900947206678161196985 13943175710405008620897739)
                ·
                  refine ⟨20914763565607512931346609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13943175710405008620897739 20914763565607512931346609)
                  ·
                    refine ⟨15686072674205634698509957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20914763565607512931346609 15686072674205634698509957)
                    ·
                      refine ⟨2941138626413556505970617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15686072674205634698509957 2941138626413556505970617)
                      ·
                        rfl

theorem cell23_5727847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_5727847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727847 prefixEnd_5727847 := by exact prefixLift 5727847
  have htrace : WordTrace (prefixWord ++ tailWord_5727847) baseStart_5727847 baseEnd_5727847 := by
    simpa [prefixWord, tailWord_5727847, baseEnd_5727847] using wordTrace_append hprefix tailTrace_5727847
  have hstable : (prefixWord ++ tailWord_5727847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727847).length < 2 ^ (prefixWord ++ tailWord_5727847).sum := by decide
  have hdescent : baseEnd_5727847 < baseStart_5727847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727861 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 2, 4]
def baseStart_5727861 : Nat := 118140960795 + 5727861 * 2 ^ 59
def prefixEnd_5727861 : Nat := 4983230072969 + 3 ^ 40 * 5727861 * 2
def baseEnd_5727861 : Nat := 980381938380906483731851

theorem tailTrace_5727861 : CollatzResearch.WordTrace tailWord_5727861 prefixEnd_5727861 980381938380906483731851 := by
  unfold tailWord_5727861
  simp only [CollatzResearch.WordTrace]
  refine ⟨208912253501945312622183437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139274835667963541748122291 208912253501945312622183437)
  ·
    refine ⟨78342095063229492233318789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208912253501945312622183437 78342095063229492233318789)
    ·
      refine ⟨14689142824355529793747273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78342095063229492233318789 14689142824355529793747273)
      ·
        refine ⟨11016857118266647345310455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14689142824355529793747273 11016857118266647345310455)
        ·
          refine ⟨16525285677399971017965683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11016857118266647345310455 16525285677399971017965683)
          ·
            refine ⟨24787928516099956526948525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16525285677399971017965683 24787928516099956526948525)
            ·
              refine ⟨9295473193537483697605697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24787928516099956526948525 9295473193537483697605697)
              ·
                refine ⟨6971604895153112773204273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9295473193537483697605697 6971604895153112773204273)
                ·
                  refine ⟨5228703671364834579903205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6971604895153112773204273 5228703671364834579903205)
                  ·
                    refine ⟨980381938380906483731851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5228703671364834579903205 980381938380906483731851)
                    ·
                      rfl

theorem cell23_5727861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_5727861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727861 prefixEnd_5727861 := by exact prefixLift 5727861
  have htrace : WordTrace (prefixWord ++ tailWord_5727861) baseStart_5727861 baseEnd_5727861 := by
    simpa [prefixWord, tailWord_5727861, baseEnd_5727861] using wordTrace_append hprefix tailTrace_5727861
  have hstable : (prefixWord ++ tailWord_5727861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727861).length < 2 ^ (prefixWord ++ tailWord_5727861).sum := by decide
  have hdescent : baseEnd_5727861 < baseStart_5727861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727902 : List Nat := [4, 3, 1, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_5727902 : Nat := 118140960795 + 5727902 * 2 ^ 59
def prefixEnd_5727902 : Nat := 4983230072969 + 3 ^ 40 * 5727902 * 2
def baseEnd_5727902 : Nat := 2941166867849553790782865

theorem tailTrace_5727902 : CollatzResearch.WordTrace tailWord_5727902 prefixEnd_5727902 2941166867849553790782865 := by
  unfold tailWord_5727902
  simp only [CollatzResearch.WordTrace]
  refine ⟨26114218611849597078053245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139275832596531184416283973 26114218611849597078053245)
  ·
    refine ⟨9792831979443598904269967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26114218611849597078053245 9792831979443598904269967)
    ·
      refine ⟨14689247969165398356404951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9792831979443598904269967 14689247969165398356404951)
      ·
        refine ⟨22033871953748097534607427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14689247969165398356404951 22033871953748097534607427)
        ·
          refine ⟨33050807930622146301911141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22033871953748097534607427 33050807930622146301911141)
          ·
            refine ⟨6197026486991652431608339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33050807930622146301911141 6197026486991652431608339)
            ·
              refine ⟨9295539730487478647412509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6197026486991652431608339 9295539730487478647412509)
              ·
                refine ⟨3485827398932804492779691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9295539730487478647412509 3485827398932804492779691)
                ·
                  refine ⟨5228741098399206739169537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485827398932804492779691 5228741098399206739169537)
                  ·
                    refine ⟨3921555823799405054377153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5228741098399206739169537 3921555823799405054377153)
                    ·
                      refine ⟨2941166867849553790782865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921555823799405054377153 2941166867849553790782865)
                      ·
                        rfl

theorem cell23_5727902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_5727902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727902 prefixEnd_5727902 := by exact prefixLift 5727902
  have htrace : WordTrace (prefixWord ++ tailWord_5727902) baseStart_5727902 baseEnd_5727902 := by
    simpa [prefixWord, tailWord_5727902, baseEnd_5727902] using wordTrace_append hprefix tailTrace_5727902
  have hstable : (prefixWord ++ tailWord_5727902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727902).length < 2 ^ (prefixWord ++ tailWord_5727902).sum := by decide
  have hdescent : baseEnd_5727902 < baseStart_5727902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727941 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 2, 2, 2]
def baseStart_5727941 : Nat := 118140960795 + 5727941 * 2 ^ 59
def prefixEnd_5727941 : Nat := 4983230072969 + 3 ^ 40 * 5727941 * 2
def baseEnd_5727941 : Nat := 2941186893595079138195185

theorem tailTrace_5727941 : CollatzResearch.WordTrace tailWord_5727941 prefixEnd_5727941 2941186893595079138195185 := by
  unfold tailWord_5727941
  simp only [CollatzResearch.WordTrace]
  refine ⟨208915171341655486285095677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139276780894436990856730451 208915171341655486285095677)
  ·
    refine ⟨78343189253120807356910879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208915171341655486285095677 78343189253120807356910879)
    ·
      refine ⟨117514783879681211035366319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78343189253120807356910879 117514783879681211035366319)
      ·
        refine ⟨176272175819521816553049479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117514783879681211035366319 176272175819521816553049479)
        ·
          refine ⟨264408263729282724829574219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176272175819521816553049479 264408263729282724829574219)
          ·
            refine ⟨396612395593924087244361329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264408263729282724829574219 396612395593924087244361329)
            ·
              refine ⟨297459296695443065433270997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396612395593924087244361329 297459296695443065433270997)
              ·
                refine ⟨6971702266299446846092289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 297459296695443065433270997 6971702266299446846092289)
                ·
                  refine ⟨5228776699724585134569217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6971702266299446846092289 5228776699724585134569217)
                  ·
                    refine ⟨3921582524793438850926913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5228776699724585134569217 3921582524793438850926913)
                    ·
                      refine ⟨2941186893595079138195185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921582524793438850926913 2941186893595079138195185)
                      ·
                        rfl

theorem cell23_5727941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 2, 2].length) (baseStart_5727941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727941 prefixEnd_5727941 := by exact prefixLift 5727941
  have htrace : WordTrace (prefixWord ++ tailWord_5727941) baseStart_5727941 baseEnd_5727941 := by
    simpa [prefixWord, tailWord_5727941, baseEnd_5727941] using wordTrace_append hprefix tailTrace_5727941
  have hstable : (prefixWord ++ tailWord_5727941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727941).length < 2 ^ (prefixWord ++ tailWord_5727941).sum := by decide
  have hdescent : baseEnd_5727941 < baseStart_5727941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727981 : List Nat := [1, 5, 1, 2, 1, 3, 1, 4, 5]
def baseStart_5727981 : Nat := 118140960795 + 5727981 * 2 ^ 59
def prefixEnd_5727981 : Nat := 4983230072969 + 3 ^ 40 * 5727981 * 2
def baseEnd_5727981 : Nat := 326800825869028775743889

theorem tailTrace_5727981 : CollatzResearch.WordTrace tailWord_5727981 prefixEnd_5727981 326800825869028775743889 := by
  unfold tailWord_5727981
  simp only [CollatzResearch.WordTrace]
  refine ⟨208916630261510573116551797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139277753507673715411034531 208916630261510573116551797)
  ·
    refine ⟨19585934087016616229676731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208916630261510573116551797 19585934087016616229676731)
    ·
      refine ⟨29378901130524924344515097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19585934087016616229676731 29378901130524924344515097)
      ·
        refine ⟨22034175847893693258386323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29378901130524924344515097 22034175847893693258386323)
        ·
          refine ⟨33051263771840539887579485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22034175847893693258386323 33051263771840539887579485)
          ·
            refine ⟨12394223914440202457842307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33051263771840539887579485 12394223914440202457842307)
            ·
              refine ⟨18591335871660303686763461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12394223914440202457842307 18591335871660303686763461)
              ·
                refine ⟨3485875475936306941268149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18591335871660303686763461 3485875475936306941268149)
                ·
                  refine ⟨326800825869028775743889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3485875475936306941268149 326800825869028775743889)
                  ·
                    rfl

theorem cell23_5727981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_5727981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727981 prefixEnd_5727981 := by exact prefixLift 5727981
  have htrace : WordTrace (prefixWord ++ tailWord_5727981) baseStart_5727981 baseEnd_5727981 := by
    simpa [prefixWord, tailWord_5727981, baseEnd_5727981] using wordTrace_append hprefix tailTrace_5727981
  have hstable : (prefixWord ++ tailWord_5727981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727981).length < 2 ^ (prefixWord ++ tailWord_5727981).sum := by decide
  have hdescent : baseEnd_5727981 < baseStart_5727981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727987 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 5]
def baseStart_5727987 : Nat := 118140960795 + 5727987 * 2 ^ 59
def prefixEnd_5727987 : Nat := 4983230072969 + 3 ^ 40 * 5727987 * 2
def baseEnd_5727987 : Nat := 2941210513705185958219973

theorem tailTrace_5727987 : CollatzResearch.WordTrace tailWord_5727987 prefixEnd_5727987 2941210513705185958219973 := by
  unfold tailWord_5727987
  simp only [CollatzResearch.WordTrace]
  refine ⟨208916849099488836141270215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139277899399659224094180143 208916849099488836141270215)
  ·
    refine ⟨313375273649233254211905323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208916849099488836141270215 313375273649233254211905323)
    ·
      refine ⟨470062910473849881317857985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313375273649233254211905323 470062910473849881317857985)
      ·
        refine ⟨352547182855387410988393489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470062910473849881317857985 352547182855387410988393489)
        ·
          refine ⟨264410387141540558241295117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352547182855387410988393489 264410387141540558241295117)
          ·
            refine ⟨99153895178077709340485669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264410387141540558241295117 99153895178077709340485669)
            ·
              refine ⟨18591355345889570501341063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99153895178077709340485669 18591355345889570501341063)
              ·
                refine ⟨27887033018834355752011595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18591355345889570501341063 27887033018834355752011595)
                ·
                  refine ⟨41830549528251533628017393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27887033018834355752011595 41830549528251533628017393)
                  ·
                    refine ⟨31372912146188650221013045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41830549528251533628017393 31372912146188650221013045)
                    ·
                      refine ⟨2941210513705185958219973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31372912146188650221013045 2941210513705185958219973)
                      ·
                        rfl

theorem cell23_5727987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_5727987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727987 prefixEnd_5727987 := by exact prefixLift 5727987
  have htrace : WordTrace (prefixWord ++ tailWord_5727987) baseStart_5727987 baseEnd_5727987 := by
    simpa [prefixWord, tailWord_5727987, baseEnd_5727987] using wordTrace_append hprefix tailTrace_5727987
  have hstable : (prefixWord ++ tailWord_5727987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727987).length < 2 ^ (prefixWord ++ tailWord_5727987).sum := by decide
  have hdescent : baseEnd_5727987 < baseStart_5727987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5727988 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5727988 : Nat := 118140960795 + 5727988 * 2 ^ 59
def prefixEnd_5727988 : Nat := 4983230072969 + 3 ^ 40 * 5727988 * 2
def baseEnd_5727988 : Nat := 2941211027185840454307469

theorem tailTrace_5727988 : CollatzResearch.WordTrace tailWord_5727988 prefixEnd_5727988 2941211027185840454307469 := by
  unfold tailWord_5727988
  simp only [CollatzResearch.WordTrace]
  refine ⟨104458442786242606656028309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139277923714990142208037745 104458442786242606656028309)
  ·
    refine ⟨4896489505605122187001327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104458442786242606656028309 4896489505605122187001327)
    ·
      refine ⟨7344734258407683280501991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4896489505605122187001327 7344734258407683280501991)
      ·
        refine ⟨11017101387611524920752987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7344734258407683280501991 11017101387611524920752987)
        ·
          refine ⟨16525652081417287381129481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11017101387611524920752987 16525652081417287381129481)
          ·
            refine ⟨12394239061062965535847111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16525652081417287381129481 12394239061062965535847111)
            ·
              refine ⟨18591358591594448303770667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12394239061062965535847111 18591358591594448303770667)
              ·
                refine ⟨27887037887391672455656001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18591358591594448303770667 27887037887391672455656001)
                ·
                  refine ⟨20915278415543754341742001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27887037887391672455656001 20915278415543754341742001)
                  ·
                    refine ⟨15686458811657815756306501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20915278415543754341742001 15686458811657815756306501)
                    ·
                      refine ⟨2941211027185840454307469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15686458811657815756306501 2941211027185840454307469)
                      ·
                        rfl

theorem cell23_5727988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5727988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5727988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5727988 prefixEnd_5727988 := by exact prefixLift 5727988
  have htrace : WordTrace (prefixWord ++ tailWord_5727988) baseStart_5727988 baseEnd_5727988 := by
    simpa [prefixWord, tailWord_5727988, baseEnd_5727988] using wordTrace_append hprefix tailTrace_5727988
  have hstable : (prefixWord ++ tailWord_5727988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5727988).length < 2 ^ (prefixWord ++ tailWord_5727988).sum := by decide
  have hdescent : baseEnd_5727988 < baseStart_5727988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5727988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728013 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_5728013 : Nat := 118140960795 + 5728013 * 2 ^ 59
def prefixEnd_5728013 : Nat := 4983230072969 + 3 ^ 40 * 5728013 * 2
def baseEnd_5728013 : Nat := 2941223864202202856494855

theorem tailTrace_5728013 : CollatzResearch.WordTrace tailWord_5728013 prefixEnd_5728013 2941223864202202856494855 := by
  unfold tailWord_5728013
  simp only [CollatzResearch.WordTrace]
  refine ⟨208917797397394642581716693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139278531598263095054477795 208917797397394642581716693)
  ·
    refine ⟨4896510876501436935508985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 208917797397394642581716693 4896510876501436935508985)
    ·
      refine ⟨3672383157376077701631739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4896510876501436935508985 3672383157376077701631739)
      ·
        refine ⟨5508574736064116552447609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3672383157376077701631739 5508574736064116552447609)
        ·
          refine ⟨4131431052048087414335707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5508574736064116552447609 4131431052048087414335707)
          ·
            refine ⟨6197146578072131121503561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4131431052048087414335707 6197146578072131121503561)
            ·
              refine ⟨4647859933554098341127671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6197146578072131121503561 4647859933554098341127671)
              ·
                refine ⟨6971789900331147511691507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647859933554098341127671 6971789900331147511691507)
                ·
                  refine ⟨10457684850496721267537261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6971789900331147511691507 10457684850496721267537261)
                  ·
                    refine ⟨3921631818936270475326473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10457684850496721267537261 3921631818936270475326473)
                    ·
                      refine ⟨2941223864202202856494855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921631818936270475326473 2941223864202202856494855)
                      ·
                        rfl

theorem cell23_5728013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_5728013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728013 prefixEnd_5728013 := by exact prefixLift 5728013
  have htrace : WordTrace (prefixWord ++ tailWord_5728013) baseStart_5728013 baseEnd_5728013 := by
    simpa [prefixWord, tailWord_5728013, baseEnd_5728013] using wordTrace_append hprefix tailTrace_5728013
  have hstable : (prefixWord ++ tailWord_5728013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728013).length < 2 ^ (prefixWord ++ tailWord_5728013).sum := by decide
  have hdescent : baseEnd_5728013 < baseStart_5728013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728092 : List Nat := [2, 2, 4, 2, 2, 1, 3, 2, 1, 4]
def baseStart_5728092 : Nat := 118140960795 + 5728092 * 2 ^ 59
def prefixEnd_5728092 : Nat := 4983230072969 + 3 ^ 40 * 5728092 * 2
def baseEnd_5728092 : Nat := 980421476391302682468997

theorem tailTrace_5728092 : CollatzResearch.WordTrace tailWord_5728092 prefixEnd_5728092 980421476391302682468997 := by
  unfold tailWord_5728092
  simp only [CollatzResearch.WordTrace]
  refine ⟨104460339382054219536921265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139280452509405626049228353 104460339382054219536921265)
  ·
    refine ⟨78345254536540664652690949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104460339382054219536921265 78345254536540664652690949)
    ·
      refine ⟨14689735225601374622379553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78345254536540664652690949 14689735225601374622379553)
      ·
        refine ⟨11017301419201030966784665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14689735225601374622379553 11017301419201030966784665)
        ·
          refine ⟨8262976064400773225088499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11017301419201030966784665 8262976064400773225088499)
          ·
            refine ⟨12394464096601159837632749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8262976064400773225088499 12394464096601159837632749)
            ·
              refine ⟨4647924036225434939112281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12394464096601159837632749 4647924036225434939112281)
              ·
                refine ⟨3485943027169076204334211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4647924036225434939112281 3485943027169076204334211)
                ·
                  refine ⟨5228914540753614306501317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3485943027169076204334211 5228914540753614306501317)
                  ·
                    refine ⟨980421476391302682468997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5228914540753614306501317 980421476391302682468997)
                    ·
                      rfl

theorem cell23_5728092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_5728092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728092 prefixEnd_5728092 := by exact prefixLift 5728092
  have htrace : WordTrace (prefixWord ++ tailWord_5728092) baseStart_5728092 baseEnd_5728092 := by
    simpa [prefixWord, tailWord_5728092, baseEnd_5728092] using wordTrace_append hprefix tailTrace_5728092
  have hstable : (prefixWord ++ tailWord_5728092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728092).length < 2 ^ (prefixWord ++ tailWord_5728092).sum := by decide
  have hdescent : baseEnd_5728092 < baseStart_5728092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728114 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_5728114 : Nat := 118140960795 + 5728114 * 2 ^ 59
def prefixEnd_5728114 : Nat := 4983230072969 + 3 ^ 40 * 5728114 * 2
def baseEnd_5728114 : Nat := 980425241916102320443963

theorem tailTrace_5728114 : CollatzResearch.WordTrace tailWord_5728114 prefixEnd_5728114 980425241916102320443963 := by
  unfold tailWord_5728114
  simp only [CollatzResearch.WordTrace]
  refine ⟨52230370292507184207785849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139280987446685824554095597 52230370292507184207785849)
  ·
    refine ⟨39172777719380388155839387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52230370292507184207785849 39172777719380388155839387)
    ·
      refine ⟨58759166579070582233759081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39172777719380388155839387 58759166579070582233759081)
      ·
        refine ⟨44069374934302936675319311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58759166579070582233759081 44069374934302936675319311)
        ·
          refine ⟨66104062401454405012978967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44069374934302936675319311 66104062401454405012978967)
          ·
            refine ⟨99156093602181607519468451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66104062401454405012978967 99156093602181607519468451)
            ·
              refine ⟨148734140403272411279202677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99156093602181607519468451 148734140403272411279202677)
              ·
                refine ⟨13943825662806788557425251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148734140403272411279202677 13943825662806788557425251)
                ·
                  refine ⟨20915738494210182836137877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13943825662806788557425251 20915738494210182836137877)
                  ·
                    refine ⟨980425241916102320443963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20915738494210182836137877 980425241916102320443963)
                    ·
                      rfl

theorem cell23_5728114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_5728114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728114 prefixEnd_5728114 := by exact prefixLift 5728114
  have htrace : WordTrace (prefixWord ++ tailWord_5728114) baseStart_5728114 baseEnd_5728114 := by
    simpa [prefixWord, tailWord_5728114, baseEnd_5728114] using wordTrace_append hprefix tailTrace_5728114
  have hstable : (prefixWord ++ tailWord_5728114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728114).length < 2 ^ (prefixWord ++ tailWord_5728114).sum := by decide
  have hdescent : baseEnd_5728114 < baseStart_5728114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728118 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_5728118 : Nat := 118140960795 + 5728118 * 2 ^ 59
def prefixEnd_5728118 : Nat := 4983230072969 + 3 ^ 40 * 5728118 * 2
def baseEnd_5728118 : Nat := 980425926556974981893957

theorem tailTrace_5728118 : CollatzResearch.WordTrace tailWord_5728118 prefixEnd_5728118 980425926556974981893957 := by
  unfold tailWord_5728118
  simp only [CollatzResearch.WordTrace]
  refine ⟨13057601691375890344643063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139281084708009497009526005 13057601691375890344643063)
  ·
    refine ⟨19586402537063835516964595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13057601691375890344643063 19586402537063835516964595)
    ·
      refine ⟨29379603805595753275446893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19586402537063835516964595 29379603805595753275446893)
      ·
        refine ⟨11017351427098407478292585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29379603805595753275446893 11017351427098407478292585)
        ·
          refine ⟨8263013570323805608719439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11017351427098407478292585 8263013570323805608719439)
          ·
            refine ⟨12394520355485708413079159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8263013570323805608719439 12394520355485708413079159)
            ·
              refine ⟨18591780533228562619618739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12394520355485708413079159 18591780533228562619618739)
              ·
                refine ⟨27887670799842843929428109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18591780533228562619618739 27887670799842843929428109)
                ·
                  refine ⟨10457876549941066473535541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27887670799842843929428109 10457876549941066473535541)
                  ·
                    refine ⟨980425926556974981893957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10457876549941066473535541 980425926556974981893957)
                    ·
                      rfl

theorem cell23_5728118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_5728118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728118 prefixEnd_5728118 := by exact prefixLift 5728118
  have htrace : WordTrace (prefixWord ++ tailWord_5728118) baseStart_5728118 baseEnd_5728118 := by
    simpa [prefixWord, tailWord_5728118, baseEnd_5728118] using wordTrace_append hprefix tailTrace_5728118
  have hstable : (prefixWord ++ tailWord_5728118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728118).length < 2 ^ (prefixWord ++ tailWord_5728118).sum := by decide
  have hdescent : baseEnd_5728118 < baseStart_5728118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728148 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_5728148 : Nat := 118140960795 + 5728148 * 2 ^ 59
def prefixEnd_5728148 : Nat := 4983230072969 + 3 ^ 40 * 5728148 * 2
def baseEnd_5728148 : Nat := 980431061363519942768911

theorem tailTrace_5728148 : CollatzResearch.WordTrace tailWord_5728148 prefixEnd_5728148 980431061363519942768911 := by
  unfold tailWord_5728148
  simp only [CollatzResearch.WordTrace]
  refine ⟨104461360625952780318940549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139281814167937040425254065 104461360625952780318940549)
  ·
    refine ⟨19586505117366146309801353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104461360625952780318940549 19586505117366146309801353)
    ·
      refine ⟨14689878838024609732351015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19586505117366146309801353 14689878838024609732351015)
      ·
        refine ⟨22034818257036914598526523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14689878838024609732351015 22034818257036914598526523)
        ·
          refine ⟨33052227385555371897789785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22034818257036914598526523 33052227385555371897789785)
          ·
            refine ⟨24789170539166528923342339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33052227385555371897789785 24789170539166528923342339)
            ·
              refine ⟨37183755808749793385013509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24789170539166528923342339 37183755808749793385013509)
              ·
                refine ⟨6971954214140586259690033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37183755808749793385013509 6971954214140586259690033)
                ·
                  refine ⟨5228965660605439694767525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6971954214140586259690033 5228965660605439694767525)
                  ·
                    refine ⟨980431061363519942768911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5228965660605439694767525 980431061363519942768911)
                    ·
                      rfl

theorem cell23_5728148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_5728148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728148 prefixEnd_5728148 := by exact prefixLift 5728148
  have htrace : WordTrace (prefixWord ++ tailWord_5728148) baseStart_5728148 baseEnd_5728148 := by
    simpa [prefixWord, tailWord_5728148, baseEnd_5728148] using wordTrace_append hprefix tailTrace_5728148
  have hstable : (prefixWord ++ tailWord_5728148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728148).length < 2 ^ (prefixWord ++ tailWord_5728148).sum := by decide
  have hdescent : baseEnd_5728148 < baseStart_5728148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728184 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_5728184 : Nat := 118140960795 + 5728184 * 2 ^ 59
def prefixEnd_5728184 : Nat := 4983230072969 + 3 ^ 40 * 5728184 * 2
def baseEnd_5728184 : Nat := 2941311669394121687456567

theorem tailTrace_5728184 : CollatzResearch.WordTrace tailWord_5728184 prefixEnd_5728184 2941311669394121687456567 := by
  unfold tailWord_5728184
  simp only [CollatzResearch.WordTrace]
  refine ⟨104462017139887569393095803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139282689519850092524127737 104462017139887569393095803)
  ·
    refine ⟨156693025709831354089643705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104462017139887569393095803 156693025709831354089643705)
    ·
      refine ⟨117519769282373515567232779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156693025709831354089643705 117519769282373515567232779)
      ·
        refine ⟨176279653923560273350849169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117519769282373515567232779 176279653923560273350849169)
        ·
          refine ⟨132209740442670205013136877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176279653923560273350849169 132209740442670205013136877)
          ·
            refine ⟨49578652666001326879926329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132209740442670205013136877 49578652666001326879926329)
            ·
              refine ⟨37183989499500995159944747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49578652666001326879926329 37183989499500995159944747)
              ·
                refine ⟨55775984249251492739917121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37183989499500995159944747 55775984249251492739917121)
                ·
                  refine ⟨41831988186938619554937841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55775984249251492739917121 41831988186938619554937841)
                  ·
                    refine ⟨31373991140203964666203381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41831988186938619554937841 31373991140203964666203381)
                    ·
                      refine ⟨2941311669394121687456567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31373991140203964666203381 2941311669394121687456567)
                      ·
                        rfl

theorem cell23_5728184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_5728184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728184 prefixEnd_5728184 := by exact prefixLift 5728184
  have htrace : WordTrace (prefixWord ++ tailWord_5728184) baseStart_5728184 baseEnd_5728184 := by
    simpa [prefixWord, tailWord_5728184, baseEnd_5728184] using wordTrace_append hprefix tailTrace_5728184
  have hstable : (prefixWord ++ tailWord_5728184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728184).length < 2 ^ (prefixWord ++ tailWord_5728184).sum := by decide
  have hdescent : baseEnd_5728184 < baseStart_5728184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728298 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_5728298 : Nat := 118140960795 + 5728298 * 2 ^ 59
def prefixEnd_5728298 : Nat := 4983230072969 + 3 ^ 40 * 5728298 * 2
def baseEnd_5728298 : Nat := 980456735396244747143681

theorem tailTrace_5728298 : CollatzResearch.WordTrace tailWord_5728298 prefixEnd_5728298 980456735396244747143681 := by
  unfold tailWord_5728298
  simp only [CollatzResearch.WordTrace]
  refine ⟨52232048050340534063960387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139285461467574757503894365 52232048050340534063960387)
  ·
    refine ⟨78348072075510801095940581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52232048050340534063960387 78348072075510801095940581)
    ·
      refine ⟨14690263514158275205488859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78348072075510801095940581 14690263514158275205488859)
      ·
        refine ⟨22035395271237412808233289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14690263514158275205488859 22035395271237412808233289)
        ·
          refine ⟨16526546453428059606174967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22035395271237412808233289 16526546453428059606174967)
          ·
            refine ⟨24789819680142089409262451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16526546453428059606174967 24789819680142089409262451)
            ·
              refine ⟨37184729520213134113893677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24789819680142089409262451 37184729520213134113893677)
              ·
                refine ⟨13944273570079925292710129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37184729520213134113893677 13944273570079925292710129)
                ·
                  refine ⟨10458205177559943969532597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13944273570079925292710129 10458205177559943969532597)
                  ·
                    refine ⟨980456735396244747143681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10458205177559943969532597 980456735396244747143681)
                    ·
                      rfl

theorem cell23_5728298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_5728298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728298 prefixEnd_5728298 := by exact prefixLift 5728298
  have htrace : WordTrace (prefixWord ++ tailWord_5728298) baseStart_5728298 baseEnd_5728298 := by
    simpa [prefixWord, tailWord_5728298, baseEnd_5728298] using wordTrace_append hprefix tailTrace_5728298
  have hstable : (prefixWord ++ tailWord_5728298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728298).length < 2 ^ (prefixWord ++ tailWord_5728298).sum := by decide
  have hdescent : baseEnd_5728298 < baseStart_5728298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728351 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 3]
def baseStart_5728351 : Nat := 118140960795 + 5728351 * 2 ^ 59
def prefixEnd_5728351 : Nat := 4983230072969 + 3 ^ 40 * 5728351 * 2
def baseEnd_5728351 : Nat := 2941397420663422534068299

theorem tailTrace_5728351 : CollatzResearch.WordTrace tailWord_5728351 prefixEnd_5728351 2941397420663422534068299 := by
  unfold tailWord_5728351
  simp only [CollatzResearch.WordTrace]
  refine ⟨208930125270170126307520907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139286750180113417538347271 208930125270170126307520907)
  ·
    refine ⟨313395187905255189461281361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208930125270170126307520907 313395187905255189461281361)
    ·
      refine ⟨235046390928941392095961021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313395187905255189461281361 235046390928941392095961021)
      ·
        refine ⟨88142396598353022035985383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235046390928941392095961021 88142396598353022035985383)
        ·
          refine ⟨132213594897529533053978075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88142396598353022035985383 132213594897529533053978075)
          ·
            refine ⟨198320392346294299580967113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132213594897529533053978075 198320392346294299580967113)
            ·
              refine ⟨148740294259720724685725335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198320392346294299580967113 148740294259720724685725335)
              ·
                refine ⟨223110441389581087028588003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148740294259720724685725335 223110441389581087028588003)
                ·
                  refine ⟨334665662084371630542882005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223110441389581087028588003 334665662084371630542882005)
                  ·
                    refine ⟨7843726455102460090848797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 334665662084371630542882005 7843726455102460090848797)
                    ·
                      refine ⟨2941397420663422534068299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7843726455102460090848797 2941397420663422534068299)
                      ·
                        rfl

theorem cell23_5728351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_5728351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728351 prefixEnd_5728351 := by exact prefixLift 5728351
  have htrace : WordTrace (prefixWord ++ tailWord_5728351) baseStart_5728351 baseEnd_5728351 := by
    simpa [prefixWord, tailWord_5728351, baseEnd_5728351] using wordTrace_append hprefix tailTrace_5728351
  have hstable : (prefixWord ++ tailWord_5728351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728351).length < 2 ^ (prefixWord ++ tailWord_5728351).sum := by decide
  have hdescent : baseEnd_5728351 < baseStart_5728351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728411 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 5]
def baseStart_5728411 : Nat := 118140960795 + 5728411 * 2 ^ 59
def prefixEnd_5728411 : Nat := 4983230072969 + 3 ^ 40 * 5728411 * 2
def baseEnd_5728411 : Nat := 2941428229502692299318023

theorem tailTrace_5728411 : CollatzResearch.WordTrace tailWord_5728411 prefixEnd_5728411 2941428229502692299318023 := by
  unfold tailWord_5728411
  simp only [CollatzResearch.WordTrace]
  refine ⟨208932313649952756554705087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139288209099968504369803391 208932313649952756554705087)
  ·
    refine ⟨313398470474929134832057631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208932313649952756554705087 313398470474929134832057631)
    ·
      refine ⟨470097705712393702248086447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313398470474929134832057631 470097705712393702248086447)
      ·
        refine ⟨705146558568590553372129671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470097705712393702248086447 705146558568590553372129671)
        ·
          refine ⟨1057719837852885830058194507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705146558568590553372129671 1057719837852885830058194507)
          ·
            refine ⟨1586579756779328745087291761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057719837852885830058194507 1586579756779328745087291761)
            ·
              refine ⟨1189934817584496558815468821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586579756779328745087291761 1189934817584496558815468821)
              ·
                refine ⟨55778194574273276194475101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1189934817584496558815468821 55778194574273276194475101)
                ·
                  refine ⟨20916822965352478572928163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55778194574273276194475101 20916822965352478572928163)
                  ·
                    refine ⟨31375234448028717859392245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20916822965352478572928163 31375234448028717859392245)
                    ·
                      refine ⟨2941428229502692299318023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31375234448028717859392245 2941428229502692299318023)
                      ·
                        rfl

theorem cell23_5728411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 5].length) (baseStart_5728411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728411 prefixEnd_5728411 := by exact prefixLift 5728411
  have htrace : WordTrace (prefixWord ++ tailWord_5728411) baseStart_5728411 baseEnd_5728411 := by
    simpa [prefixWord, tailWord_5728411, baseEnd_5728411] using wordTrace_append hprefix tailTrace_5728411
  have hstable : (prefixWord ++ tailWord_5728411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728411).length < 2 ^ (prefixWord ++ tailWord_5728411).sum := by decide
  have hdescent : baseEnd_5728411 < baseStart_5728411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728442 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2]
def baseStart_5728442 : Nat := 118140960795 + 5728442 * 2 ^ 59
def prefixEnd_5728442 : Nat := 4983230072969 + 3 ^ 40 * 5728442 * 2
def baseEnd_5728442 : Nat := 2941444147402981678030381

theorem tailTrace_5728442 : CollatzResearch.WordTrace tailWord_5728442 prefixEnd_5728442 2941444147402981678030381 := by
  unfold tailWord_5728442
  simp only [CollatzResearch.WordTrace]
  refine ⟨52233361078210112212270895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139288962875226965899389053 52233361078210112212270895)
  ·
    refine ⟨78350041617315168318406343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52233361078210112212270895 78350041617315168318406343)
    ·
      refine ⟨117525062425972752477609515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78350041617315168318406343 117525062425972752477609515)
      ·
        refine ⟨176287593638959128716414273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117525062425972752477609515 176287593638959128716414273)
        ·
          refine ⟨132215695229219346537310705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176287593638959128716414273 132215695229219346537310705)
          ·
            refine ⟨99161771421914509902983029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132215695229219346537310705 99161771421914509902983029)
            ·
              refine ⟨9296416070804485303404659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99161771421914509902983029 9296416070804485303404659)
              ·
                refine ⟨13944624106206727955106989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9296416070804485303404659 13944624106206727955106989)
                ·
                  refine ⟨5229234039827522983165121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13944624106206727955106989 5229234039827522983165121)
                  ·
                    refine ⟨3921925529870642237373841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5229234039827522983165121 3921925529870642237373841)
                    ·
                      refine ⟨2941444147402981678030381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921925529870642237373841 2941444147402981678030381)
                      ·
                        rfl

theorem cell23_5728442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2].length) (baseStart_5728442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728442 prefixEnd_5728442 := by exact prefixLift 5728442
  have htrace : WordTrace (prefixWord ++ tailWord_5728442) baseStart_5728442 baseEnd_5728442 := by
    simpa [prefixWord, tailWord_5728442, baseEnd_5728442] using wordTrace_append hprefix tailTrace_5728442
  have hstable : (prefixWord ++ tailWord_5728442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728442).length < 2 ^ (prefixWord ++ tailWord_5728442).sum := by decide
  have hdescent : baseEnd_5728442 < baseStart_5728442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728448 : List Nat := [2, 1, 1, 2, 5, 2, 2, 8]
def baseStart_5728448 : Nat := 118140960795 + 5728448 * 2 ^ 59
def prefixEnd_5728448 : Nat := 4983230072969 + 3 ^ 40 * 5728448 * 2
def baseEnd_5728448 : Nat := 108942489936552172390939

theorem tailTrace_5728448 : CollatzResearch.WordTrace tailWord_5728448 prefixEnd_5728448 108942489936552172390939 := by
  unfold tailWord_5728448
  simp only [CollatzResearch.WordTrace]
  refine ⟨104466831575409355936900999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139289108767212474582534665 104466831575409355936900999)
  ·
    refine ⟨156700247363114033905351499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104466831575409355936900999 156700247363114033905351499)
    ·
      refine ⟨235050371044671050858027249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156700247363114033905351499 235050371044671050858027249)
      ·
        refine ⟨176287778283503288143520437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235050371044671050858027249 176287778283503288143520437)
        ·
          refine ⟨16526979214078433263455041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176287778283503288143520437 16526979214078433263455041)
          ·
            refine ⟨12395234410558824947591281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16526979214078433263455041 12395234410558824947591281)
            ·
              refine ⟨9296425807919118710693461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12395234410558824947591281 9296425807919118710693461)
              ·
                refine ⟨108942489936552172390939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9296425807919118710693461 108942489936552172390939)
                ·
                  rfl

theorem cell23_5728448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 8].length) (baseStart_5728448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728448 prefixEnd_5728448 := by exact prefixLift 5728448
  have htrace : WordTrace (prefixWord ++ tailWord_5728448) baseStart_5728448 baseEnd_5728448 := by
    simpa [prefixWord, tailWord_5728448, baseEnd_5728448] using wordTrace_append hprefix tailTrace_5728448
  have hstable : (prefixWord ++ tailWord_5728448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728448).length < 2 ^ (prefixWord ++ tailWord_5728448).sum := by decide
  have hdescent : baseEnd_5728448 < baseStart_5728448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728452 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_5728452 : Nat := 118140960795 + 5728452 * 2 ^ 59
def prefixEnd_5728452 : Nat := 4983230072969 + 3 ^ 40 * 5728452 * 2
def baseEnd_5728452 : Nat := 980483094069842212968445

theorem tailTrace_5728452 : CollatzResearch.WordTrace tailWord_5728452 prefixEnd_5728452 980483094069842212968445 := by
  unfold tailWord_5728452
  simp only [CollatzResearch.WordTrace]
  refine ⟨104466904521402110278473805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139289206028536147037965073 104466904521402110278473805)
  ·
    refine ⟨39175089195525791354427677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104466904521402110278473805 39175089195525791354427677)
    ·
      refine ⟨14690658448322171757910379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39175089195525791354427677 14690658448322171757910379)
      ·
        refine ⟨22035987672483257636865569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14690658448322171757910379 22035987672483257636865569)
        ·
          refine ⟨16526990754362443227649177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22035987672483257636865569 16526990754362443227649177)
          ·
            refine ⟨12395243065771832420736883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16526990754362443227649177 12395243065771832420736883)
            ·
              refine ⟨18592864598657748631105325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12395243065771832420736883 18592864598657748631105325)
              ·
                refine ⟨6972324224496655736664497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18592864598657748631105325 6972324224496655736664497)
                ·
                  refine ⟨5229243168372491802498373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6972324224496655736664497 5229243168372491802498373)
                  ·
                    refine ⟨980483094069842212968445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5229243168372491802498373 980483094069842212968445)
                    ·
                      rfl

theorem cell23_5728452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_5728452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728452 prefixEnd_5728452 := by exact prefixLift 5728452
  have htrace : WordTrace (prefixWord ++ tailWord_5728452) baseStart_5728452 baseEnd_5728452 := by
    simpa [prefixWord, tailWord_5728452, baseEnd_5728452] using wordTrace_append hprefix tailTrace_5728452
  have hstable : (prefixWord ++ tailWord_5728452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728452).length < 2 ^ (prefixWord ++ tailWord_5728452).sum := by decide
  have hdescent : baseEnd_5728452 < baseStart_5728452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728462 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_5728462 : Nat := 118140960795 + 5728462 * 2 ^ 59
def prefixEnd_5728462 : Nat := 4983230072969 + 3 ^ 40 * 5728462 * 2
def baseEnd_5728462 : Nat := 2941454417016071599780289

theorem tailTrace_5728462 : CollatzResearch.WordTrace tailWord_5728462 prefixEnd_5728462 2941454417016071599780289 := by
  unfold tailWord_5728462
  simp only [CollatzResearch.WordTrace]
  refine ⟨26116771721595999033101455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139289449181845328176541093 26116771721595999033101455)
  ·
    refine ⟨39175157582393998549652183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26116771721595999033101455 39175157582393998549652183)
    ·
      refine ⟨58762736373590997824478275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39175157582393998549652183 58762736373590997824478275)
      ·
        refine ⟨88144104560386496736717413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58762736373590997824478275 88144104560386496736717413)
        ·
          refine ⟨16527019605072468138134515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88144104560386496736717413 16527019605072468138134515)
          ·
            refine ⟨24790529407608702207201773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16527019605072468138134515 24790529407608702207201773)
            ·
              refine ⟨9296448527853263327700665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24790529407608702207201773 9296448527853263327700665)
              ·
                refine ⟨6972336395889947495775499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9296448527853263327700665 6972336395889947495775499)
                ·
                  refine ⟨10458504593834921243663249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6972336395889947495775499 10458504593834921243663249)
                  ·
                    refine ⟨7843878445376190932747437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10458504593834921243663249 7843878445376190932747437)
                    ·
                      refine ⟨2941454417016071599780289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7843878445376190932747437 2941454417016071599780289)
                      ·
                        rfl

theorem cell23_5728462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_5728462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728462 prefixEnd_5728462 := by exact prefixLift 5728462
  have htrace : WordTrace (prefixWord ++ tailWord_5728462) baseStart_5728462 baseEnd_5728462 := by
    simpa [prefixWord, tailWord_5728462, baseEnd_5728462] using wordTrace_append hprefix tailTrace_5728462
  have hstable : (prefixWord ++ tailWord_5728462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728462).length < 2 ^ (prefixWord ++ tailWord_5728462).sum := by decide
  have hdescent : baseEnd_5728462 < baseStart_5728462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728476 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5728476 : Nat := 118140960795 + 5728476 * 2 ^ 59
def prefixEnd_5728476 : Nat := 4983230072969 + 3 ^ 40 * 5728476 * 2
def baseEnd_5728476 : Nat := 2941461605745234545005225

theorem tailTrace_5728476 : CollatzResearch.WordTrace tailWord_5728476 prefixEnd_5728476 2941461605745234545005225 := by
  unfold tailWord_5728476
  simp only [CollatzResearch.WordTrace]
  refine ⟨104467342197358636327910641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139289789596478181770547521 104467342197358636327910641)
  ·
    refine ⟨78350506648018977245932981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104467342197358636327910641 78350506648018977245932981)
    ·
      refine ⟨7345359998251779116806217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78350506648018977245932981 7345359998251779116806217)
      ·
        refine ⟨5509019998688834337604663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7345359998251779116806217 5509019998688834337604663)
        ·
          refine ⟨8263529998033251506406995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5509019998688834337604663 8263529998033251506406995)
          ·
            refine ⟨12395294997049877259610493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8263529998033251506406995 12395294997049877259610493)
            ·
              refine ⟨4648235623893703972353935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12395294997049877259610493 4648235623893703972353935)
              ·
                refine ⟨6972353435840555958530903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4648235623893703972353935 6972353435840555958530903)
                ·
                  refine ⟨10458530153760833937796355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6972353435840555958530903 10458530153760833937796355)
                  ·
                    refine ⟨15687795230641250906694533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10458530153760833937796355 15687795230641250906694533)
                    ·
                      refine ⟨2941461605745234545005225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15687795230641250906694533 2941461605745234545005225)
                      ·
                        rfl

theorem cell23_5728476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5728476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728476 prefixEnd_5728476 := by exact prefixLift 5728476
  have htrace : WordTrace (prefixWord ++ tailWord_5728476) baseStart_5728476 baseEnd_5728476 := by
    simpa [prefixWord, tailWord_5728476, baseEnd_5728476] using wordTrace_append hprefix tailTrace_5728476
  have hstable : (prefixWord ++ tailWord_5728476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728476).length < 2 ^ (prefixWord ++ tailWord_5728476).sum := by decide
  have hdescent : baseEnd_5728476 < baseStart_5728476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728482 : List Nat := [3, 3, 4, 1, 1, 11]
def baseStart_5728482 : Nat := 118140960795 + 5728482 * 2 ^ 59
def prefixEnd_5728482 : Nat := 4983230072969 + 3 ^ 40 * 5728482 * 2
def baseEnd_5728482 : Nat := 12104792949091199677079

theorem tailTrace_5728482 : CollatzResearch.WordTrace tailWord_5728482 prefixEnd_5728482 12104792949091199677079 := by
  unfold tailWord_5728482
  simp only [CollatzResearch.WordTrace]
  refine ⟨52233725808173883920134925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139289935488463690453693133 52233725808173883920134925)
  ·
    refine ⟨19587647178065206470050597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52233725808173883920134925 19587647178065206470050597)
    ·
      refine ⟨3672683845887226213134487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19587647178065206470050597 3672683845887226213134487)
      ·
        refine ⟨5509025768830839319701731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3672683845887226213134487 5509025768830839319701731)
        ·
          refine ⟨8263538653246258979552597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5509025768830839319701731 8263538653246258979552597)
          ·
            refine ⟨12104792949091199677079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8263538653246258979552597 12104792949091199677079)
            ·
              rfl

theorem cell23_5728482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 11].length) (baseStart_5728482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728482 prefixEnd_5728482 := by exact prefixLift 5728482
  have htrace : WordTrace (prefixWord ++ tailWord_5728482) baseStart_5728482 baseEnd_5728482 := by
    simpa [prefixWord, tailWord_5728482, baseEnd_5728482] using wordTrace_append hprefix tailTrace_5728482
  have hstable : (prefixWord ++ tailWord_5728482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728482).length < 2 ^ (prefixWord ++ tailWord_5728482).sum := by decide
  have hdescent : baseEnd_5728482 < baseStart_5728482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728492 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 3]
def baseStart_5728492 : Nat := 118140960795 + 5728492 * 2 ^ 59
def prefixEnd_5728492 : Nat := 4983230072969 + 3 ^ 40 * 5728492 * 2
def baseEnd_5728492 : Nat := 2941469821435706482405151

theorem tailTrace_5728492 : CollatzResearch.WordTrace tailWord_5728492 prefixEnd_5728492 2941469821435706482405151 := by
  unfold tailWord_5728492
  simp only [CollatzResearch.WordTrace]
  refine ⟨104467633981329653694201865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139290178641772871592269153 104467633981329653694201865)
  ·
    refine ⟨78350725485997240270651399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104467633981329653694201865 78350725485997240270651399)
    ·
      refine ⟨117526088228995860405977099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78350725485997240270651399 117526088228995860405977099)
      ·
        refine ⟨176289132343493790608965649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117526088228995860405977099 176289132343493790608965649)
        ·
          refine ⟨132216849257620342956724237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176289132343493790608965649 132216849257620342956724237)
          ·
            refine ⟨49581318471607628608771589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132216849257620342956724237 49581318471607628608771589)
            ·
              refine ⟨9296497213426430364144673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49581318471607628608771589 9296497213426430364144673)
              ·
                refine ⟨6972372910069822773108505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9296497213426430364144673 6972372910069822773108505)
                ·
                  refine ⟨5229279682552367079831379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6972372910069822773108505 5229279682552367079831379)
                  ·
                    refine ⟨7843919523828550619747069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229279682552367079831379 7843919523828550619747069)
                    ·
                      refine ⟨2941469821435706482405151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7843919523828550619747069 2941469821435706482405151)
                      ·
                        rfl

theorem cell23_5728492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_5728492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728492 prefixEnd_5728492 := by exact prefixLift 5728492
  have htrace : WordTrace (prefixWord ++ tailWord_5728492) baseStart_5728492 baseEnd_5728492 := by
    simpa [prefixWord, tailWord_5728492, baseEnd_5728492] using wordTrace_append hprefix tailTrace_5728492
  have hstable : (prefixWord ++ tailWord_5728492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728492).length < 2 ^ (prefixWord ++ tailWord_5728492).sum := by decide
  have hdescent : baseEnd_5728492 < baseStart_5728492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728502 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_5728502 : Nat := 118140960795 + 5728502 * 2 ^ 59
def prefixEnd_5728502 : Nat := 4983230072969 + 3 ^ 40 * 5728502 * 2
def baseEnd_5728502 : Nat := 2941474956242251443280105

theorem tailTrace_5728502 : CollatzResearch.WordTrace tailWord_5728502 prefixEnd_5728502 2941474956242251443280105 := by
  unfold tailWord_5728502
  simp only [CollatzResearch.WordTrace]
  refine ⟨13058477043288942443516735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139290421795082052730845173 13058477043288942443516735)
  ·
    refine ⟨19587715564933413665275103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13058477043288942443516735 19587715564933413665275103)
    ·
      refine ⟨29381573347400120497912655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19587715564933413665275103 29381573347400120497912655)
      ·
        refine ⟨44072360021100180746868983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29381573347400120497912655 44072360021100180746868983)
        ·
          refine ⟨66108540031650271120303475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44072360021100180746868983 66108540031650271120303475)
          ·
            refine ⟨99162810047475406680455213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66108540031650271120303475 99162810047475406680455213)
            ·
              refine ⟨37186053767803277505170705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99162810047475406680455213 37186053767803277505170705)
              ·
                refine ⟨27889540325852458128878029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37186053767803277505170705 27889540325852458128878029)
                ·
                  refine ⟨10458577622194671798329261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27889540325852458128878029 10458577622194671798329261)
                  ·
                    refine ⟨3921966608323001924373473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10458577622194671798329261 3921966608323001924373473)
                    ·
                      refine ⟨2941474956242251443280105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921966608323001924373473 2941474956242251443280105)
                      ·
                        rfl

theorem cell23_5728502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_5728502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728502 prefixEnd_5728502 := by exact prefixLift 5728502
  have htrace : WordTrace (prefixWord ++ tailWord_5728502) baseStart_5728502 baseEnd_5728502 := by
    simpa [prefixWord, tailWord_5728502, baseEnd_5728502] using wordTrace_append hprefix tailTrace_5728502
  have hstable : (prefixWord ++ tailWord_5728502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728502).length < 2 ^ (prefixWord ++ tailWord_5728502).sum := by decide
  have hdescent : baseEnd_5728502 < baseStart_5728502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728508 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_5728508 : Nat := 118140960795 + 5728508 * 2 ^ 59
def prefixEnd_5728508 : Nat := 4983230072969 + 3 ^ 40 * 5728508 * 2
def baseEnd_5728508 : Nat := 980492679042059473268359

theorem tailTrace_5728508 : CollatzResearch.WordTrace tailWord_5728508 prefixEnd_5728508 980492679042059473268359 := by
  unfold tailWord_5728508
  simp only [CollatzResearch.WordTrace]
  refine ⟨104467925765300671060493089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139290567687067561413990785 104467925765300671060493089)
  ·
    refine ⟨78350944323975503295369817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104467925765300671060493089 78350944323975503295369817)
    ·
      refine ⟨58763208242981627471527363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78350944323975503295369817 58763208242981627471527363)
      ·
        refine ⟨88144812364472441207291045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58763208242981627471527363 88144812364472441207291045)
        ·
          refine ⟨16527152318338582726367071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88144812364472441207291045 16527152318338582726367071)
          ·
            refine ⟨24790728477507874089550607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16527152318338582726367071 24790728477507874089550607)
            ·
              refine ⟨37186092716261811134325911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24790728477507874089550607 37186092716261811134325911)
              ·
                refine ⟨55779139074392716701488867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37186092716261811134325911 55779139074392716701488867)
                ·
                  refine ⟨83668708611589075052233301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55779139074392716701488867 83668708611589075052233301)
                  ·
                    refine ⟨980492679042059473268359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83668708611589075052233301 980492679042059473268359)
                    ·
                      rfl

theorem cell23_5728508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_5728508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728508 prefixEnd_5728508 := by exact prefixLift 5728508
  have htrace : WordTrace (prefixWord ++ tailWord_5728508) baseStart_5728508 baseEnd_5728508 := by
    simpa [prefixWord, tailWord_5728508, baseEnd_5728508] using wordTrace_append hprefix tailTrace_5728508
  have hstable : (prefixWord ++ tailWord_5728508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728508).length < 2 ^ (prefixWord ++ tailWord_5728508).sum := by decide
  have hdescent : baseEnd_5728508 < baseStart_5728508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728542 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5728542 : Nat := 118140960795 + 5728542 * 2 ^ 59
def prefixEnd_5728542 : Nat := 4983230072969 + 3 ^ 40 * 5728542 * 2
def baseEnd_5728542 : Nat := 980498498489477095593307

theorem tailTrace_5728542 : CollatzResearch.WordTrace tailWord_5728542 prefixEnd_5728542 980498498489477095593307 := by
  unfold tailWord_5728542
  simp only [CollatzResearch.WordTrace]
  refine ⟨26117136451559770740965485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139291394408318777285149253 26117136451559770740965485)
  ·
    refine ⟨9793926169334914027862057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26117136451559770740965485 9793926169334914027862057)
    ·
      refine ⟨7345444627001185520896543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9793926169334914027862057 7345444627001185520896543)
      ·
        refine ⟨11018166940501778281344815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7345444627001185520896543 11018166940501778281344815)
        ·
          refine ⟨16527250410752667422017223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11018166940501778281344815 16527250410752667422017223)
          ·
            refine ⟨24790875616129001133025835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16527250410752667422017223 24790875616129001133025835)
            ·
              refine ⟨37186313424193501699538753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24790875616129001133025835 37186313424193501699538753)
              ·
                refine ⟨27889735068145126274654065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37186313424193501699538753 27889735068145126274654065)
                ·
                  refine ⟨20917301301108844705990549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27889735068145126274654065 20917301301108844705990549)
                  ·
                    refine ⟨980498498489477095593307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20917301301108844705990549 980498498489477095593307)
                    ·
                      rfl

theorem cell23_5728542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5728542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728542 prefixEnd_5728542 := by exact prefixLift 5728542
  have htrace : WordTrace (prefixWord ++ tailWord_5728542) baseStart_5728542 baseEnd_5728542 := by
    simpa [prefixWord, tailWord_5728542, baseEnd_5728542] using wordTrace_append hprefix tailTrace_5728542
  have hstable : (prefixWord ++ tailWord_5728542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728542).length < 2 ^ (prefixWord ++ tailWord_5728542).sum := by decide
  have hdescent : baseEnd_5728542 < baseStart_5728542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728549 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 4, 2, 2]
def baseStart_5728549 : Nat := 118140960795 + 5728549 * 2 ^ 59
def prefixEnd_5728549 : Nat := 4983230072969 + 3 ^ 40 * 5728549 * 2
def baseEnd_5728549 : Nat := 2941499089833012759392389

theorem tailTrace_5728549 : CollatzResearch.WordTrace tailWord_5728549 prefixEnd_5728549 2941499089833012759392389 := by
  unfold tailWord_5728549
  simp only [CollatzResearch.WordTrace]
  refine ⟨208937346923452806123228701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139291564615635204082152467 208937346923452806123228701)
  ·
    refine ⟨78351505096294802296210763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208937346923452806123228701 78351505096294802296210763)
    ·
      refine ⟨117527257644442203444316145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78351505096294802296210763 117527257644442203444316145)
      ·
        refine ⟨88145443233331652583237109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117527257644442203444316145 88145443233331652583237109)
        ·
          refine ⟨8263635303124842429678479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88145443233331652583237109 8263635303124842429678479)
          ·
            refine ⟨12395452954687263644517719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8263635303124842429678479 12395452954687263644517719)
            ·
              refine ⟨18593179432030895466776579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12395452954687263644517719 18593179432030895466776579)
              ·
                refine ⟨27889769148046343200164869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18593179432030895466776579 27889769148046343200164869)
                ·
                  refine ⟨5229331715258689350030913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27889769148046343200164869 5229331715258689350030913)
                  ·
                    refine ⟨3921998786444017012523185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5229331715258689350030913 3921998786444017012523185)
                    ·
                      refine ⟨2941499089833012759392389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3921998786444017012523185 2941499089833012759392389)
                      ·
                        rfl

theorem cell23_5728549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_5728549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728549 prefixEnd_5728549 := by exact prefixLift 5728549
  have htrace : WordTrace (prefixWord ++ tailWord_5728549) baseStart_5728549 baseEnd_5728549 := by
    simpa [prefixWord, tailWord_5728549, baseEnd_5728549] using wordTrace_append hprefix tailTrace_5728549
  have hstable : (prefixWord ++ tailWord_5728549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728549).length < 2 ^ (prefixWord ++ tailWord_5728549).sum := by decide
  have hdescent : baseEnd_5728549 < baseStart_5728549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728565 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_5728565 : Nat := 118140960795 + 5728565 * 2 ^ 59
def prefixEnd_5728565 : Nat := 4983230072969 + 3 ^ 40 * 5728565 * 2
def baseEnd_5728565 : Nat := 2941507305523484696792315

theorem tailTrace_5728565 : CollatzResearch.WordTrace tailWord_5728565 prefixEnd_5728565 2941507305523484696792315 := by
  unfold tailWord_5728565
  simp only [CollatzResearch.WordTrace]
  refine ⟨208937930491394840855811149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139291953660929893903874099 208937930491394840855811149)
  ·
    refine ⟨78351723934273065320929181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208937930491394840855811149 78351723934273065320929181)
    ·
      refine ⟨29381896475352399495348443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78351723934273065320929181 29381896475352399495348443)
      ·
        refine ⟨44072844713028599243022665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29381896475352399495348443 44072844713028599243022665)
        ·
          refine ⟨33054633534771449432266999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44072844713028599243022665 33054633534771449432266999)
          ·
            refine ⟨49581950302157174148400499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33054633534771449432266999 49581950302157174148400499)
            ·
              refine ⟨74372925453235761222600749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49581950302157174148400499 74372925453235761222600749)
              ·
                refine ⟨27889847044963410458475281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74372925453235761222600749 27889847044963410458475281)
                ·
                  refine ⟨20917385283722557843856461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27889847044963410458475281 20917385283722557843856461)
                  ·
                    refine ⟨7844019481395959191446173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20917385283722557843856461 7844019481395959191446173)
                    ·
                      refine ⟨2941507305523484696792315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844019481395959191446173 2941507305523484696792315)
                      ·
                        rfl

theorem cell23_5728565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_5728565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728565 prefixEnd_5728565 := by exact prefixLift 5728565
  have htrace : WordTrace (prefixWord ++ tailWord_5728565) baseStart_5728565 baseEnd_5728565 := by
    simpa [prefixWord, tailWord_5728565, baseEnd_5728565] using wordTrace_append hprefix tailTrace_5728565
  have hstable : (prefixWord ++ tailWord_5728565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728565).length < 2 ^ (prefixWord ++ tailWord_5728565).sum := by decide
  have hdescent : baseEnd_5728565 < baseStart_5728565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728568 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 1, 7]
def baseStart_5728568 : Nat := 118140960795 + 5728568 * 2 ^ 59
def prefixEnd_5728568 : Nat := 4983230072969 + 3 ^ 40 * 5728568 * 2
def baseEnd_5728568 : Nat := 980502948655149395018267

theorem tailTrace_5728568 : CollatzResearch.WordTrace tailWord_5728568 prefixEnd_5728568 980502948655149395018267 := by
  unfold tailWord_5728568
  simp only [CollatzResearch.WordTrace]
  refine ⟨104469019955191986184085179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139292026606922648245446905 104469019955191986184085179)
  ·
    refine ⟨156703529932787979276127769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104469019955191986184085179 156703529932787979276127769)
    ·
      refine ⟨117527647449590984457095827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156703529932787979276127769 117527647449590984457095827)
      ·
        refine ⟨176291471174386476685643741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117527647449590984457095827 176291471174386476685643741)
        ·
          refine ⟨66109301690394928757116403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176291471174386476685643741 66109301690394928757116403)
          ·
            refine ⟨99163952535592393135674605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66109301690394928757116403 99163952535592393135674605)
            ·
              refine ⟨37186482200847147425877977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99163952535592393135674605 37186482200847147425877977)
              ·
                refine ⟨27889861650635360569408483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37186482200847147425877977 27889861650635360569408483)
                ·
                  refine ⟨41834792475953040854112725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27889861650635360569408483 41834792475953040854112725)
                  ·
                    refine ⟨980502948655149395018267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41834792475953040854112725 980502948655149395018267)
                    ·
                      rfl

theorem cell23_5728568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_5728568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728568 prefixEnd_5728568 := by exact prefixLift 5728568
  have htrace : WordTrace (prefixWord ++ tailWord_5728568) baseStart_5728568 baseEnd_5728568 := by
    simpa [prefixWord, tailWord_5728568, baseEnd_5728568] using wordTrace_append hprefix tailTrace_5728568
  have hstable : (prefixWord ++ tailWord_5728568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728568).length < 2 ^ (prefixWord ++ tailWord_5728568).sum := by decide
  have hdescent : baseEnd_5728568 < baseStart_5728568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728625 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 6, 2, 3]
def baseStart_5728625 : Nat := 118140960795 + 5728625 * 2 ^ 59
def prefixEnd_5728625 : Nat := 4983230072969 + 3 ^ 40 * 5728625 * 2
def baseEnd_5728625 : Nat := 2941538114362754462042039

theorem tailTrace_5728625 : CollatzResearch.WordTrace tailWord_5728625 prefixEnd_5728625 2941538114362754462042039 := by
  unfold tailWord_5728625
  simp only [CollatzResearch.WordTrace]
  refine ⟨208940118871177471102995329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139293412580784980735330219 208940118871177471102995329)
  ·
    refine ⟨156705089153383103327246497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208940118871177471102995329 156705089153383103327246497)
    ·
      refine ⟨117528816865037327495434873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156705089153383103327246497 117528816865037327495434873)
      ·
        refine ⟨88146612648777995621576155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117528816865037327495434873 88146612648777995621576155)
        ·
          refine ⟨132219918973166993432364233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88146612648777995621576155 132219918973166993432364233)
          ·
            refine ⟨99164939229875245074273175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132219918973166993432364233 99164939229875245074273175)
            ·
              refine ⟨148747408844812867611409763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99164939229875245074273175 148747408844812867611409763)
              ·
                refine ⟨223121113267219301417114645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148747408844812867611409763 223121113267219301417114645)
                ·
                  refine ⟨10458802184400904753927249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 223121113267219301417114645 10458802184400904753927249)
                  ·
                    refine ⟨7844101638300678565445437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10458802184400904753927249 7844101638300678565445437)
                    ·
                      refine ⟨2941538114362754462042039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844101638300678565445437 2941538114362754462042039)
                      ·
                        rfl

theorem cell23_5728625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_5728625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728625 prefixEnd_5728625 := by exact prefixLift 5728625
  have htrace : WordTrace (prefixWord ++ tailWord_5728625) baseStart_5728625 baseEnd_5728625 := by
    simpa [prefixWord, tailWord_5728625, baseEnd_5728625] using wordTrace_append hprefix tailTrace_5728625
  have hstable : (prefixWord ++ tailWord_5728625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728625).length < 2 ^ (prefixWord ++ tailWord_5728625).sum := by decide
  have hdescent : baseEnd_5728625 < baseStart_5728625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728666 : List Nat := [3, 1, 1, 4, 1, 2, 4, 2, 1, 4]
def baseStart_5728666 : Nat := 118140960795 + 5728666 * 2 ^ 59
def prefixEnd_5728666 : Nat := 4983230072969 + 3 ^ 40 * 5728666 * 2
def baseEnd_5728666 : Nat := 980519722356529600543117

theorem tailTrace_5728666 : CollatzResearch.WordTrace tailWord_5728666 prefixEnd_5728666 980519722356529600543117 := by
  unfold tailWord_5728666
  simp only [CollatzResearch.WordTrace]
  refine ⟨52235403566007233776309463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139294409509352623403491901 52235403566007233776309463)
  ·
    refine ⟨78353105349010850664464195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52235403566007233776309463 78353105349010850664464195)
    ·
      refine ⟨117529658023516275996696293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78353105349010850664464195 117529658023516275996696293)
      ·
        refine ⟨22036810879409301749380555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117529658023516275996696293 22036810879409301749380555)
        ·
          refine ⟨33055216319113952624070833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22036810879409301749380555 33055216319113952624070833)
          ·
            refine ⟨24791412239335464468053125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33055216319113952624070833 24791412239335464468053125)
            ·
              refine ⟨4648389794875399587759961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24791412239335464468053125 4648389794875399587759961)
              ·
                refine ⟨3486292346156549690819971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4648389794875399587759961 3486292346156549690819971)
                ·
                  refine ⟨5229438519234824536229957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486292346156549690819971 5229438519234824536229957)
                  ·
                    refine ⟨980519722356529600543117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5229438519234824536229957 980519722356529600543117)
                    ·
                      rfl

theorem cell23_5728666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_5728666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728666 prefixEnd_5728666 := by exact prefixLift 5728666
  have htrace : WordTrace (prefixWord ++ tailWord_5728666) baseStart_5728666 baseEnd_5728666 := by
    simpa [prefixWord, tailWord_5728666, baseEnd_5728666] using wordTrace_append hprefix tailTrace_5728666
  have hstable : (prefixWord ++ tailWord_5728666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728666).length < 2 ^ (prefixWord ++ tailWord_5728666).sum := by decide
  have hdescent : baseEnd_5728666 < baseStart_5728666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728675 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 3, 5]
def baseStart_5728675 : Nat := 118140960795 + 5728675 * 2 ^ 59
def prefixEnd_5728675 : Nat := 4983230072969 + 3 ^ 40 * 5728675 * 2
def baseEnd_5728675 : Nat := 980521262798493088805603

theorem tailTrace_5728675 : CollatzResearch.WordTrace tailWord_5728675 prefixEnd_5728675 980521262798493088805603 := by
  unfold tailWord_5728675
  simp only [CollatzResearch.WordTrace]
  refine ⟨208941942520996329642315479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139294628347330886428210319 208941942520996329642315479)
  ·
    refine ⟨313412913781494494463473219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208941942520996329642315479 313412913781494494463473219)
    ·
      refine ⟨470119370672241741695209829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313412913781494494463473219 470119370672241741695209829)
      ·
        refine ⟨88147382001045326567851843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 470119370672241741695209829 88147382001045326567851843)
        ·
          refine ⟨132221073001567989851777765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88147382001045326567851843 132221073001567989851777765)
          ·
            refine ⟨24791451187793998097208331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132221073001567989851777765 24791451187793998097208331)
            ·
              refine ⟨37187176781690997145812497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24791451187793998097208331 37187176781690997145812497)
              ·
                refine ⟨27890382586268247859359373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37187176781690997145812497 27890382586268247859359373)
                ·
                  refine ⟨10458893469850592947259765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27890382586268247859359373 10458893469850592947259765)
                  ·
                    refine ⟨980521262798493088805603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10458893469850592947259765 980521262798493088805603)
                    ·
                      rfl

theorem cell23_5728675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 5].length) (baseStart_5728675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728675 prefixEnd_5728675 := by exact prefixLift 5728675
  have htrace : WordTrace (prefixWord ++ tailWord_5728675) baseStart_5728675 baseEnd_5728675 := by
    simpa [prefixWord, tailWord_5728675, baseEnd_5728675] using wordTrace_append hprefix tailTrace_5728675
  have hstable : (prefixWord ++ tailWord_5728675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728675).length < 2 ^ (prefixWord ++ tailWord_5728675).sum := by decide
  have hdescent : baseEnd_5728675 < baseStart_5728675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728689 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 3, 1, 3]
def baseStart_5728689 : Nat := 118140960795 + 5728689 * 2 ^ 59
def prefixEnd_5728689 : Nat := 4983230072969 + 3 ^ 40 * 5728689 * 2
def baseEnd_5728689 : Nat := 2941570977124642211641745

theorem tailTrace_5728689 : CollatzResearch.WordTrace tailWord_5728689 prefixEnd_5728689 2941570977124642211641745 := by
  unfold tailWord_5728689
  simp only [CollatzResearch.WordTrace]
  refine ⟨208942453142945610033325121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139294968761963740022216747 208942453142945610033325121)
  ·
    refine ⟨156706839857209207524993841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208942453142945610033325121 156706839857209207524993841)
    ·
      refine ⟨117530129892906905643745381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156706839857209207524993841 117530129892906905643745381)
      ·
        refine ⟨22036899354920044808202259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117530129892906905643745381 22036899354920044808202259)
        ·
          refine ⟨33055349032380067212303389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22036899354920044808202259 33055349032380067212303389)
          ·
            refine ⟨12395755887142525204613771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33055349032380067212303389 12395755887142525204613771)
            ·
              refine ⟨18593633830713787806920657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12395755887142525204613771 18593633830713787806920657)
              ·
                refine ⟨13945225373035340855190493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18593633830713787806920657 13945225373035340855190493)
                ·
                  refine ⟨5229459514888252820696435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13945225373035340855190493 5229459514888252820696435)
                  ·
                    refine ⟨7844189272332379231044653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229459514888252820696435 7844189272332379231044653)
                    ·
                      refine ⟨2941570977124642211641745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844189272332379231044653 2941570977124642211641745)
                      ·
                        rfl

theorem cell23_5728689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_5728689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728689 prefixEnd_5728689 := by exact prefixLift 5728689
  have htrace : WordTrace (prefixWord ++ tailWord_5728689) baseStart_5728689 baseEnd_5728689 := by
    simpa [prefixWord, tailWord_5728689, baseEnd_5728689] using wordTrace_append hprefix tailTrace_5728689
  have hstable : (prefixWord ++ tailWord_5728689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728689).length < 2 ^ (prefixWord ++ tailWord_5728689).sum := by decide
  have hdescent : baseEnd_5728689 < baseStart_5728689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728715 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 5]
def baseStart_5728715 : Nat := 118140960795 + 5728715 * 2 ^ 59
def prefixEnd_5728715 : Nat := 4983230072969 + 3 ^ 40 * 5728715 * 2
def baseEnd_5728715 : Nat := 2941584327621659109916625

theorem tailTrace_5728715 : CollatzResearch.WordTrace tailWord_5728715 prefixEnd_5728715 2941584327621659109916625 := by
  unfold tailWord_5728715
  simp only [CollatzResearch.WordTrace]
  refine ⟨208943401440851416473771599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139295600960567610982514399 208943401440851416473771599)
  ·
    refine ⟨313415102161277124710657399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208943401440851416473771599 313415102161277124710657399)
    ·
      refine ⟨470122653241915687065986099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313415102161277124710657399 470122653241915687065986099)
      ·
        refine ⟨705183979862873530598979149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470122653241915687065986099 705183979862873530598979149)
        ·
          refine ⟨264443992448577573974617181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 705183979862873530598979149 264443992448577573974617181)
          ·
            refine ⟨99166497168216590240481443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264443992448577573974617181 99166497168216590240481443)
            ·
              refine ⟨148749745752324885360722165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99166497168216590240481443 148749745752324885360722165)
              ·
                refine ⟨13945288664280458002567703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148749745752324885360722165 13945288664280458002567703)
                ·
                  refine ⟨20917932996420687003851555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13945288664280458002567703 20917932996420687003851555)
                  ·
                    refine ⟨31376899494631030505777333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20917932996420687003851555 31376899494631030505777333)
                    ·
                      refine ⟨2941584327621659109916625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31376899494631030505777333 2941584327621659109916625)
                      ·
                        rfl

theorem cell23_5728715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 5].length) (baseStart_5728715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728715 prefixEnd_5728715 := by exact prefixLift 5728715
  have htrace : WordTrace (prefixWord ++ tailWord_5728715) baseStart_5728715 baseEnd_5728715 := by
    simpa [prefixWord, tailWord_5728715, baseEnd_5728715] using wordTrace_append hprefix tailTrace_5728715
  have hstable : (prefixWord ++ tailWord_5728715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728715).length < 2 ^ (prefixWord ++ tailWord_5728715).sum := by decide
  have hdescent : baseEnd_5728715 < baseStart_5728715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728739 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 1, 6]
def baseStart_5728739 : Nat := 118140960795 + 5728739 * 2 ^ 59
def prefixEnd_5728739 : Nat := 4983230072969 + 3 ^ 40 * 5728739 * 2
def baseEnd_5728739 : Nat := 980532217052455672005505

theorem tailTrace_5728739 : CollatzResearch.WordTrace tailWord_5728739 prefixEnd_5728739 980532217052455672005505 := by
  unfold tailWord_5728739
  simp only [CollatzResearch.WordTrace]
  refine ⟨208944276792764468572645271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139296184528509645715096847 208944276792764468572645271)
  ·
    refine ⟨313416415189146702858967907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208944276792764468572645271 313416415189146702858967907)
    ·
      refine ⟨470124622783720054288451861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313416415189146702858967907 470124622783720054288451861)
      ·
        refine ⟨22037091692986877544771181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 470124622783720054288451861 22037091692986877544771181)
        ·
          refine ⟨8263909384870079079289193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22037091692986877544771181 8263909384870079079289193)
          ·
            refine ⟨6197932038652559309466895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8263909384870079079289193 6197932038652559309466895)
            ·
              refine ⟨9296898057978838964200343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6197932038652559309466895 9296898057978838964200343)
              ·
                refine ⟨13945347086968258446300515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9296898057978838964200343 13945347086968258446300515)
                ·
                  refine ⟨20918020630452387669450773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13945347086968258446300515 20918020630452387669450773)
                  ·
                    refine ⟨980532217052455672005505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20918020630452387669450773 980532217052455672005505)
                    ·
                      rfl

theorem cell23_5728739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 6].length) (baseStart_5728739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728739 prefixEnd_5728739 := by exact prefixLift 5728739
  have htrace : WordTrace (prefixWord ++ tailWord_5728739) baseStart_5728739 baseEnd_5728739 := by
    simpa [prefixWord, tailWord_5728739, baseEnd_5728739] using wordTrace_append hprefix tailTrace_5728739
  have hstable : (prefixWord ++ tailWord_5728739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728739).length < 2 ^ (prefixWord ++ tailWord_5728739).sum := by decide
  have hdescent : baseEnd_5728739 < baseStart_5728739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728746 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_5728746 : Nat := 118140960795 + 5728746 * 2 ^ 59
def prefixEnd_5728746 : Nat := 4983230072969 + 3 ^ 40 * 5728746 * 2
def baseEnd_5728746 : Nat := 2941600245521948488628983

theorem tailTrace_5728746 : CollatzResearch.WordTrace tailWord_5728746 prefixEnd_5728746 2941600245521948488628983 := by
  unfold tailWord_5728746
  simp only [CollatzResearch.WordTrace]
  refine ⟨52236133025934777192037523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139296354735826072512100061 52236133025934777192037523)
  ·
    refine ⟨78354199538902165788056285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52236133025934777192037523 78354199538902165788056285)
    ·
      refine ⟨29382824827088312170521107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78354199538902165788056285 29382824827088312170521107)
      ·
        refine ⟨44074237240632468255781661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29382824827088312170521107 44074237240632468255781661)
        ·
          refine ⟨16527838965237175595918123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44074237240632468255781661 16527838965237175595918123)
          ·
            refine ⟨24791758447855763393877185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16527838965237175595918123 24791758447855763393877185)
            ·
              refine ⟨18593818835891822545407889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24791758447855763393877185 18593818835891822545407889)
              ·
                refine ⟨13945364126918866909055917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18593818835891822545407889 13945364126918866909055917)
                ·
                  refine ⟨5229511547594575090895969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13945364126918866909055917 5229511547594575090895969)
                  ·
                    refine ⟨3922133660695931318171977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5229511547594575090895969 3922133660695931318171977)
                    ·
                      refine ⟨2941600245521948488628983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922133660695931318171977 2941600245521948488628983)
                      ·
                        rfl

theorem cell23_5728746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_5728746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728746 prefixEnd_5728746 := by exact prefixLift 5728746
  have htrace : WordTrace (prefixWord ++ tailWord_5728746) baseStart_5728746 baseEnd_5728746 := by
    simpa [prefixWord, tailWord_5728746, baseEnd_5728746] using wordTrace_append hprefix tailTrace_5728746
  have hstable : (prefixWord ++ tailWord_5728746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728746).length < 2 ^ (prefixWord ++ tailWord_5728746).sum := by decide
  have hdescent : baseEnd_5728746 < baseStart_5728746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728757 : List Nat := [1, 3, 5, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_5728757 : Nat := 118140960795 + 5728757 * 2 ^ 59
def prefixEnd_5728757 : Nat := 4983230072969 + 3 ^ 40 * 5728757 * 2
def baseEnd_5728757 : Nat := 2941605893809147945591433

theorem tailTrace_5728757 : CollatzResearch.WordTrace tailWord_5728757 prefixEnd_5728757 2941605893809147945591433 := by
  unfold tailWord_5728757
  simp only [CollatzResearch.WordTrace]
  refine ⟨208944933306699257646800525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139296622204466171764533683 208944933306699257646800525)
  ·
    refine ⟨78354349990012221617550197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208944933306699257646800525 78354349990012221617550197)
    ·
      refine ⟨7345720311563645776645331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78354349990012221617550197 7345720311563645776645331)
      ·
        refine ⟨11018580467345468664967997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7345720311563645776645331 11018580467345468664967997)
        ·
          refine ⟨4131967675254550749362999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11018580467345468664967997 4131967675254550749362999)
          ·
            refine ⟨6197951512881826124044499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4131967675254550749362999 6197951512881826124044499)
            ·
              refine ⟨9296927269322739186066749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6197951512881826124044499 9296927269322739186066749)
              ·
                refine ⟨3486347725996027194775031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9296927269322739186066749 3486347725996027194775031)
                ·
                  refine ⟨5229521588994040792162547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486347725996027194775031 5229521588994040792162547)
                  ·
                    refine ⟨7844282383491061188243821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229521588994040792162547 7844282383491061188243821)
                    ·
                      refine ⟨2941605893809147945591433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844282383491061188243821 2941605893809147945591433)
                      ·
                        rfl

theorem cell23_5728757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_5728757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728757 prefixEnd_5728757 := by exact prefixLift 5728757
  have htrace : WordTrace (prefixWord ++ tailWord_5728757) baseStart_5728757 baseEnd_5728757 := by
    simpa [prefixWord, tailWord_5728757, baseEnd_5728757] using wordTrace_append hprefix tailTrace_5728757
  have hstable : (prefixWord ++ tailWord_5728757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728757).length < 2 ^ (prefixWord ++ tailWord_5728757).sum := by decide
  have hdescent : baseEnd_5728757 < baseStart_5728757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728774 : List Nat := [6, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_5728774 : Nat := 118140960795 + 5728774 * 2 ^ 59
def prefixEnd_5728774 : Nat := 4983230072969 + 3 ^ 40 * 5728774 * 2
def baseEnd_5728774 : Nat := 2941614622980274379078855

theorem tailTrace_5728774 : CollatzResearch.WordTrace tailWord_5728774 prefixEnd_5728774 2941614622980274379078855 := by
  unfold tailWord_5728774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6529548542113677173442793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139297035565091779700112917 6529548542113677173442793)
  ·
    refine ⟨4897161406585257880082095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6529548542113677173442793 4897161406585257880082095)
    ·
      refine ⟨7345742109877886820123143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4897161406585257880082095 7345742109877886820123143)
      ·
        refine ⟨11018613164816830230184715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7345742109877886820123143 11018613164816830230184715)
        ·
          refine ⟨16527919747225245345277073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11018613164816830230184715 16527919747225245345277073)
          ·
            refine ⟨12395939810418934008957805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16527919747225245345277073 12395939810418934008957805)
            ·
              refine ⟨4648477428907100253359177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12395939810418934008957805 4648477428907100253359177)
              ·
                refine ⟨3486358071680325190019383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4648477428907100253359177 3486358071680325190019383)
                ·
                  refine ⟨5229537107520487785029075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486358071680325190019383 5229537107520487785029075)
                  ·
                    refine ⟨7844305661280731677543613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229537107520487785029075 7844305661280731677543613)
                    ·
                      refine ⟨2941614622980274379078855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844305661280731677543613 2941614622980274379078855)
                      ·
                        rfl

theorem cell23_5728774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_5728774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728774 prefixEnd_5728774 := by exact prefixLift 5728774
  have htrace : WordTrace (prefixWord ++ tailWord_5728774) baseStart_5728774 baseEnd_5728774 := by
    simpa [prefixWord, tailWord_5728774, baseEnd_5728774] using wordTrace_append hprefix tailTrace_5728774
  have hstable : (prefixWord ++ tailWord_5728774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728774).length < 2 ^ (prefixWord ++ tailWord_5728774).sum := by decide
  have hdescent : baseEnd_5728774 < baseStart_5728774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728779 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 4, 1, 3]
def baseStart_5728779 : Nat := 118140960795 + 5728779 * 2 ^ 59
def prefixEnd_5728779 : Nat := 4983230072969 + 3 ^ 40 * 5728779 * 2
def baseEnd_5728779 : Nat := 2941617190383546859516331

theorem tailTrace_5728779 : CollatzResearch.WordTrace tailWord_5728779 prefixEnd_5728779 2941617190383546859516331 := by
  unfold tailWord_5728779
  simp only [CollatzResearch.WordTrace]
  refine ⟨208945735712619555404101391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139297157141746370269400927 208945735712619555404101391)
  ·
    refine ⟨313418603568929333106152087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208945735712619555404101391 313418603568929333106152087)
    ·
      refine ⟨470127905353393999659228131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313418603568929333106152087 470127905353393999659228131)
      ·
        refine ⟨705191858030090999488842197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470127905353393999659228131 705191858030090999488842197)
        ·
          refine ⟨16527934172580257800519739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 705191858030090999488842197 16527934172580257800519739)
          ·
            refine ⟨24791901258870386700779609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16527934172580257800519739 24791901258870386700779609)
            ·
              refine ⟨18593925944152790025584707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24791901258870386700779609 18593925944152790025584707)
              ·
                refine ⟨27890888916229185038377061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18593925944152790025584707 27890888916229185038377061)
                ·
                  refine ⟨5229541671792972194695699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27890888916229185038377061 5229541671792972194695699)
                  ·
                    refine ⟨7844312507689458292043549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229541671792972194695699 7844312507689458292043549)
                    ·
                      refine ⟨2941617190383546859516331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844312507689458292043549 2941617190383546859516331)
                      ·
                        rfl

theorem cell23_5728779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 1, 3].length) (baseStart_5728779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728779 prefixEnd_5728779 := by exact prefixLift 5728779
  have htrace : WordTrace (prefixWord ++ tailWord_5728779) baseStart_5728779 baseEnd_5728779 := by
    simpa [prefixWord, tailWord_5728779, baseEnd_5728779] using wordTrace_append hprefix tailTrace_5728779
  have hstable : (prefixWord ++ tailWord_5728779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728779).length < 2 ^ (prefixWord ++ tailWord_5728779).sum := by decide
  have hdescent : baseEnd_5728779 < baseStart_5728779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728780 : List Nat := [2, 2, 1, 2, 4, 2, 3, 2, 1, 2, 2]
def baseStart_5728780 : Nat := 118140960795 + 5728780 * 2 ^ 59
def prefixEnd_5728780 : Nat := 4983230072969 + 3 ^ 40 * 5728780 * 2
def baseEnd_5728780 : Nat := 2941617703864201355603827

theorem tailTrace_5728780 : CollatzResearch.WordTrace tailWord_5728780 prefixEnd_5728780 2941617703864201355603827 := by
  unfold tailWord_5728780
  simp only [CollatzResearch.WordTrace]
  refine ⟨104472886092807966287443897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139297181457077288383258529 104472886092807966287443897)
  ·
    refine ⟨78354664569605974715582923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104472886092807966287443897 78354664569605974715582923)
    ·
      refine ⟨117531996854408962073374385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78354664569605974715582923 117531996854408962073374385)
      ·
        refine ⟨88148997640806721555030789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117531996854408962073374385 88148997640806721555030789)
        ·
          refine ⟨16527937057651260291568273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88148997640806721555030789 16527937057651260291568273)
          ·
            refine ⟨12395952793238445218676205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16527937057651260291568273 12395952793238445218676205)
            ·
              refine ⟨4648482297464416957003577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12395952793238445218676205 4648482297464416957003577)
              ·
                refine ⟨3486361723098312717752683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4648482297464416957003577 3486361723098312717752683)
                ·
                  refine ⟨5229542584647469076629025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486361723098312717752683 5229542584647469076629025)
                  ·
                    refine ⟨3922156938485601807471769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5229542584647469076629025 3922156938485601807471769)
                    ·
                      refine ⟨2941617703864201355603827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922156938485601807471769 2941617703864201355603827)
                      ·
                        rfl

theorem cell23_5728780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_5728780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728780 prefixEnd_5728780 := by exact prefixLift 5728780
  have htrace : WordTrace (prefixWord ++ tailWord_5728780) baseStart_5728780 baseEnd_5728780 := by
    simpa [prefixWord, tailWord_5728780, baseEnd_5728780] using wordTrace_append hprefix tailTrace_5728780
  have hstable : (prefixWord ++ tailWord_5728780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728780).length < 2 ^ (prefixWord ++ tailWord_5728780).sum := by decide
  have hdescent : baseEnd_5728780 < baseStart_5728780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728789 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 3, 3, 2]
def baseStart_5728789 : Nat := 118140960795 + 5728789 * 2 ^ 59
def prefixEnd_5728789 : Nat := 4983230072969 + 3 ^ 40 * 5728789 * 2
def baseEnd_5728789 : Nat := 2941622325190091820391285

theorem tailTrace_5728789 : CollatzResearch.WordTrace tailWord_5728789 prefixEnd_5728789 2941622325190091820391285 := by
  unfold tailWord_5728789
  simp only [CollatzResearch.WordTrace]
  refine ⟨208946100442583327111965421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139297400295055551407976947 208946100442583327111965421)
  ·
    refine ⟨78354787665968747666987033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208946100442583327111965421 78354787665968747666987033)
    ·
      refine ⟨58766090749476560750240275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78354787665968747666987033 58766090749476560750240275)
      ·
        refine ⟨88149136124214841125360413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58766090749476560750240275 88149136124214841125360413)
        ·
          refine ⟨33055926046580565422010155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88149136124214841125360413 33055926046580565422010155)
          ·
            refine ⟨49583889069870848133015233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33055926046580565422010155 49583889069870848133015233)
            ·
              refine ⟨37187916802403136099761425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49583889069870848133015233 37187916802403136099761425)
              ·
                refine ⟨27890937601802352074821069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37187916802403136099761425 27890937601802352074821069)
                ·
                  refine ⟨10459101600675882028057901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27890937601802352074821069 10459101600675882028057901)
                  ·
                    refine ⟨3922163100253455760521713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10459101600675882028057901 3922163100253455760521713)
                    ·
                      refine ⟨2941622325190091820391285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922163100253455760521713 2941622325190091820391285)
                      ·
                        rfl

theorem cell23_5728789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_5728789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728789 prefixEnd_5728789 := by exact prefixLift 5728789
  have htrace : WordTrace (prefixWord ++ tailWord_5728789) baseStart_5728789 baseEnd_5728789 := by
    simpa [prefixWord, tailWord_5728789, baseEnd_5728789] using wordTrace_append hprefix tailTrace_5728789
  have hstable : (prefixWord ++ tailWord_5728789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728789).length < 2 ^ (prefixWord ++ tailWord_5728789).sum := by decide
  have hdescent : baseEnd_5728789 < baseStart_5728789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728796 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_5728796 : Nat := 118140960795 + 5728796 * 2 ^ 59
def prefixEnd_5728796 : Nat := 4983230072969 + 3 ^ 40 * 5728796 * 2
def baseEnd_5728796 : Nat := 2941625919554673293003753

theorem tailTrace_5728796 : CollatzResearch.WordTrace tailWord_5728796 prefixEnd_5728796 2941625919554673293003753 := by
  unfold tailWord_5728796
  simp only [CollatzResearch.WordTrace]
  refine ⟨104473177876778983653735121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139297570502371978204980161 104473177876778983653735121)
  ·
    refine ⟨78354883407584237740301341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104473177876778983653735121 78354883407584237740301341)
    ·
      refine ⟨29383081277844089152613003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78354883407584237740301341 29383081277844089152613003)
      ·
        refine ⟨44074621916766133728919505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29383081277844089152613003 44074621916766133728919505)
        ·
          refine ⟨33055966437574600296689629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44074621916766133728919505 33055966437574600296689629)
          ·
            refine ⟨12395987414090475111258611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33055966437574600296689629 12395987414090475111258611)
            ·
              refine ⟨18593981121135712666887917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12395987414090475111258611 18593981121135712666887917)
              ·
                refine ⟨6972742920425892250082969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18593981121135712666887917 6972742920425892250082969)
                ·
                  refine ⟨5229557190319419187562227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6972742920425892250082969 5229557190319419187562227)
                  ·
                    refine ⟨7844335785479128781343341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229557190319419187562227 7844335785479128781343341)
                    ·
                      refine ⟨2941625919554673293003753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844335785479128781343341 2941625919554673293003753)
                      ·
                        rfl

theorem cell23_5728796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_5728796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728796 prefixEnd_5728796 := by exact prefixLift 5728796
  have htrace : WordTrace (prefixWord ++ tailWord_5728796) baseStart_5728796 baseEnd_5728796 := by
    simpa [prefixWord, tailWord_5728796, baseEnd_5728796] using wordTrace_append hprefix tailTrace_5728796
  have hstable : (prefixWord ++ tailWord_5728796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728796).length < 2 ^ (prefixWord ++ tailWord_5728796).sum := by decide
  have hdescent : baseEnd_5728796 < baseStart_5728796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728819 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 1, 4, 2]
def baseStart_5728819 : Nat := 118140960795 + 5728819 * 2 ^ 59
def prefixEnd_5728819 : Nat := 4983230072969 + 3 ^ 40 * 5728819 * 2
def baseEnd_5728819 : Nat := 2941637729609726703016147

theorem tailTrace_5728819 : CollatzResearch.WordTrace tailWord_5728819 prefixEnd_5728819 2941637729609726703016147 := by
  unfold tailWord_5728819
  simp only [CollatzResearch.WordTrace]
  refine ⟨208947194632474642235557511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139298129754983094823705007 208947194632474642235557511)
  ·
    refine ⟨313420791948711963353336267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208947194632474642235557511 313420791948711963353336267)
    ·
      refine ⟨470131187923067945030004401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313420791948711963353336267 470131187923067945030004401)
      ·
        refine ⟨352598390942300958772503301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470131187923067945030004401 352598390942300958772503301)
        ·
          refine ⟨66112198301681429769844369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 352598390942300958772503301 66112198301681429769844369)
          ·
            refine ⟨49584148726261072327383277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66112198301681429769844369 49584148726261072327383277)
            ·
              refine ⟨18594055772347902122768729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49584148726261072327383277 18594055772347902122768729)
              ·
                refine ⟨13945541829260926592076547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18594055772347902122768729 13945541829260926592076547)
                ·
                  refine ⟨20918312743891389888114821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13945541829260926592076547 20918312743891389888114821)
                  ·
                    refine ⟨3922183639479635604021529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20918312743891389888114821 3922183639479635604021529)
                    ·
                      refine ⟨2941637729609726703016147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922183639479635604021529 2941637729609726703016147)
                      ·
                        rfl

theorem cell23_5728819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 4, 2].length) (baseStart_5728819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728819 prefixEnd_5728819 := by exact prefixLift 5728819
  have htrace : WordTrace (prefixWord ++ tailWord_5728819) baseStart_5728819 baseEnd_5728819 := by
    simpa [prefixWord, tailWord_5728819, baseEnd_5728819] using wordTrace_append hprefix tailTrace_5728819
  have hstable : (prefixWord ++ tailWord_5728819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728819).length < 2 ^ (prefixWord ++ tailWord_5728819).sum := by decide
  have hdescent : baseEnd_5728819 < baseStart_5728819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728830 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_5728830 : Nat := 118140960795 + 5728830 * 2 ^ 59
def prefixEnd_5728830 : Nat := 4983230072969 + 3 ^ 40 * 5728830 * 2
def baseEnd_5728830 : Nat := 2941643377896926159978597

theorem tailTrace_5728830 : CollatzResearch.WordTrace tailWord_5728830 prefixEnd_5728830 2941643377896926159978597 := by
  unfold tailWord_5728830
  simp only [CollatzResearch.WordTrace]
  refine ⟨26118449479429348889275993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139298397223623194076138629 26118449479429348889275993)
  ·
    refine ⟨19588837109572011666956995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26118449479429348889275993 19588837109572011666956995)
    ·
      refine ⟨29383255664358017500435493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19588837109572011666956995 29383255664358017500435493)
      ·
        refine ⟨5509360437067128281331655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29383255664358017500435493 5509360437067128281331655)
        ·
          refine ⟨8264040655600692421997483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5509360437067128281331655 8264040655600692421997483)
          ·
            refine ⟨12396060983401038632996225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8264040655600692421997483 12396060983401038632996225)
            ·
              refine ⟨9297045737550778974747169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12396060983401038632996225 9297045737550778974747169)
              ·
                refine ⟨6972784303163084231060377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9297045737550778974747169 6972784303163084231060377)
                ·
                  refine ⟨5229588227372313173295283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6972784303163084231060377 5229588227372313173295283)
                  ·
                    refine ⟨7844382341058469759942925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229588227372313173295283 7844382341058469759942925)
                    ·
                      refine ⟨2941643377896926159978597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844382341058469759942925 2941643377896926159978597)
                      ·
                        rfl

theorem cell23_5728830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_5728830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728830 prefixEnd_5728830 := by exact prefixLift 5728830
  have htrace : WordTrace (prefixWord ++ tailWord_5728830) baseStart_5728830 baseEnd_5728830 := by
    simpa [prefixWord, tailWord_5728830, baseEnd_5728830] using wordTrace_append hprefix tailTrace_5728830
  have hstable : (prefixWord ++ tailWord_5728830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728830).length < 2 ^ (prefixWord ++ tailWord_5728830).sum := by decide
  have hdescent : baseEnd_5728830 < baseStart_5728830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728835 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 7]
def baseStart_5728835 : Nat := 118140960795 + 5728835 * 2 ^ 59
def prefixEnd_5728835 : Nat := 4983230072969 + 3 ^ 40 * 5728835 * 2
def baseEnd_5728835 : Nat := 2941645945300198640416073

theorem tailTrace_5728835 : CollatzResearch.WordTrace tailWord_5728835 prefixEnd_5728835 2941645945300198640416073 := by
  unfold tailWord_5728835
  simp only [CollatzResearch.WordTrace]
  refine ⟨208947778200416676968139959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139298518800277784645426639 208947778200416676968139959)
  ·
    refine ⟨313421667300625015452209939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208947778200416676968139959 313421667300625015452209939)
    ·
      refine ⟨470132500950937523178314909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313421667300625015452209939 470132500950937523178314909)
      ·
        refine ⟨176299687856601571191868091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 470132500950937523178314909 176299687856601571191868091)
        ·
          refine ⟨264449531784902356787802137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176299687856601571191868091 264449531784902356787802137)
          ·
            refine ⟨198337148838676767590851603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264449531784902356787802137 198337148838676767590851603)
            ·
              refine ⟨297505723258015151386277405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198337148838676767590851603 297505723258015151386277405)
              ·
                refine ⟨111564646221755681769854027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297505723258015151386277405 111564646221755681769854027)
                ·
                  refine ⟨167346969332633522654781041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111564646221755681769854027 167346969332633522654781041)
                  ·
                    refine ⟨125510226999475141991085781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167346969332633522654781041 125510226999475141991085781)
                    ·
                      refine ⟨2941645945300198640416073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125510226999475141991085781 2941645945300198640416073)
                      ·
                        rfl

theorem cell23_5728835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_5728835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728835 prefixEnd_5728835 := by exact prefixLift 5728835
  have htrace : WordTrace (prefixWord ++ tailWord_5728835) baseStart_5728835 baseEnd_5728835 := by
    simpa [prefixWord, tailWord_5728835, baseEnd_5728835] using wordTrace_append hprefix tailTrace_5728835
  have hstable : (prefixWord ++ tailWord_5728835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728835).length < 2 ^ (prefixWord ++ tailWord_5728835).sum := by decide
  have hdescent : baseEnd_5728835 < baseStart_5728835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728919 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 3, 4]
def baseStart_5728919 : Nat := 118140960795 + 5728919 * 2 ^ 59
def prefixEnd_5728919 : Nat := 4983230072969 + 3 ^ 40 * 5728919 * 2
def baseEnd_5728919 : Nat := 980563025891725437255229

theorem tailTrace_5728919 : CollatzResearch.WordTrace tailWord_5728919 prefixEnd_5728919 980563025891725437255229 := by
  unfold tailWord_5728919
  simp only [CollatzResearch.WordTrace]
  refine ⟨208950841932112359314197811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139300561288074906209465207 208950841932112359314197811)
  ·
    refine ⟨313426262898168538971296717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208950841932112359314197811 313426262898168538971296717)
    ·
      refine ⟨117534848586813202114236269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313426262898168538971296717 117534848586813202114236269)
      ·
        refine ⟨44075568220054950792838601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117534848586813202114236269 44075568220054950792838601)
        ·
          refine ⟨33056676165041213094628951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44075568220054950792838601 33056676165041213094628951)
          ·
            refine ⟨49585014247561819641943427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33056676165041213094628951 49585014247561819641943427)
            ·
              refine ⟨74377521371342729462915141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49585014247561819641943427 74377521371342729462915141)
              ·
                refine ⟨13945785257126761774296589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74377521371342729462915141 13945785257126761774296589)
                ·
                  refine ⟨5229669471422535665361221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13945785257126761774296589 5229669471422535665361221)
                  ·
                    refine ⟨980563025891725437255229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5229669471422535665361221 980563025891725437255229)
                    ·
                      rfl

theorem cell23_5728919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_5728919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728919 prefixEnd_5728919 := by exact prefixLift 5728919
  have htrace : WordTrace (prefixWord ++ tailWord_5728919) baseStart_5728919 baseEnd_5728919 := by
    simpa [prefixWord, tailWord_5728919, baseEnd_5728919] using wordTrace_append hprefix tailTrace_5728919
  have hstable : (prefixWord ++ tailWord_5728919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728919).length < 2 ^ (prefixWord ++ tailWord_5728919).sum := by decide
  have hdescent : baseEnd_5728919 < baseStart_5728919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728926 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_5728926 : Nat := 118140960795 + 5728926 * 2 ^ 59
def prefixEnd_5728926 : Nat := 4983230072969 + 3 ^ 40 * 5728926 * 2
def baseEnd_5728926 : Nat := 2941692672039757784378155

theorem tailTrace_5728926 : CollatzResearch.WordTrace tailWord_5728926 prefixEnd_5728926 2941692672039757784378155 := by
  unfold tailWord_5728926
  simp only [CollatzResearch.WordTrace]
  refine ⟨26118887155385874938712829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139300731495391333006468421 26118887155385874938712829)
  ·
    refine ⟨9794582683269703102017311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26118887155385874938712829 9794582683269703102017311)
    ·
      refine ⟨14691874024904554653025967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9794582683269703102017311 14691874024904554653025967)
      ·
        refine ⟨22037811037356831979538951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14691874024904554653025967 22037811037356831979538951)
        ·
          refine ⟨33056716556035247969308427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22037811037356831979538951 33056716556035247969308427)
          ·
            refine ⟨49585074834052871953962641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33056716556035247969308427 49585074834052871953962641)
            ·
              refine ⟨37188806125539653965471981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49585074834052871953962641 37188806125539653965471981)
              ·
                refine ⟨13945802297077370237051993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37188806125539653965471981 13945802297077370237051993)
                ·
                  refine ⟨10459351722808027677788995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13945802297077370237051993 10459351722808027677788995)
                  ·
                    refine ⟨15689027584212041516683493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10459351722808027677788995 15689027584212041516683493)
                    ·
                      refine ⟨2941692672039757784378155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15689027584212041516683493 2941692672039757784378155)
                      ·
                        rfl

theorem cell23_5728926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_5728926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728926 prefixEnd_5728926 := by exact prefixLift 5728926
  have htrace : WordTrace (prefixWord ++ tailWord_5728926) baseStart_5728926 baseEnd_5728926 := by
    simpa [prefixWord, tailWord_5728926, baseEnd_5728926] using wordTrace_append hprefix tailTrace_5728926
  have hstable : (prefixWord ++ tailWord_5728926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728926).length < 2 ^ (prefixWord ++ tailWord_5728926).sum := by decide
  have hdescent : baseEnd_5728926 < baseStart_5728926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728932 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 10]
def baseStart_5728932 : Nat := 118140960795 + 5728932 * 2 ^ 59
def prefixEnd_5728932 : Nat := 4983230072969 + 3 ^ 40 * 5728932 * 2
def baseEnd_5728932 : Nat := 326855083658187195655903

theorem tailTrace_5728932 : CollatzResearch.WordTrace tailWord_5728932 prefixEnd_5728932 326855083658187195655903 := by
  unfold tailWord_5728932
  simp only [CollatzResearch.WordTrace]
  refine ⟨104475658040532631267210525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139300877387376841689614033 104475658040532631267210525)
  ·
    refine ⟨39178371765199736725203947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104475658040532631267210525 39178371765199736725203947)
    ·
      refine ⟨58767557647799605087805921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39178371765199736725203947 58767557647799605087805921)
      ·
        refine ⟨44075668235849703815854441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58767557647799605087805921 44075668235849703815854441)
        ·
          refine ⟨33056751176887277861890831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44075668235849703815854441 33056751176887277861890831)
          ·
            refine ⟨49585126765330916792836247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33056751176887277861890831 49585126765330916792836247)
            ·
              refine ⟨74377690147996375189254371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49585126765330916792836247 74377690147996375189254371)
              ·
                refine ⟨111566535221994562783881557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74377690147996375189254371 111566535221994562783881557)
                ·
                  refine ⟨326855083658187195655903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 111566535221994562783881557 326855083658187195655903)
                  ·
                    rfl

theorem cell23_5728932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_5728932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728932 prefixEnd_5728932 := by exact prefixLift 5728932
  have htrace : WordTrace (prefixWord ++ tailWord_5728932) baseStart_5728932 baseEnd_5728932 := by
    simpa [prefixWord, tailWord_5728932, baseEnd_5728932] using wordTrace_append hprefix tailTrace_5728932
  have hstable : (prefixWord ++ tailWord_5728932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728932).length < 2 ^ (prefixWord ++ tailWord_5728932).sum := by decide
  have hdescent : baseEnd_5728932 < baseStart_5728932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5728949 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 8]
def baseStart_5728949 : Nat := 118140960795 + 5728949 * 2 ^ 59
def prefixEnd_5728949 : Nat := 4983230072969 + 3 ^ 40 * 5728949 * 2
def baseEnd_5728949 : Nat := 326856053566090132710061

theorem tailTrace_5728949 : CollatzResearch.WordTrace tailWord_5728949 prefixEnd_5728949 326856053566090132710061 := by
  unfold tailWord_5728949
  simp only [CollatzResearch.WordTrace]
  refine ⟨208951936122003674437789901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139301290748002449625193267 208951936122003674437789901)
  ·
    refine ⟨78356976045751377914171213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208951936122003674437789901 78356976045751377914171213)
    ·
      refine ⟨29383866017156766717814205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78356976045751377914171213 29383866017156766717814205)
      ·
        refine ⟨11018949756433787519180327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29383866017156766717814205 11018949756433787519180327)
        ·
          refine ⟨16528424634650681278770491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11018949756433787519180327 16528424634650681278770491)
          ·
            refine ⟨24792636951976021918155737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16528424634650681278770491 24792636951976021918155737)
            ·
              refine ⟨18594477713982016438616803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24792636951976021918155737 18594477713982016438616803)
              ·
                refine ⟨27891716570973024657925205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18594477713982016438616803 27891716570973024657925205)
                ·
                  refine ⟨326856053566090132710061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27891716570973024657925205 326856053566090132710061)
                  ·
                    rfl

theorem cell23_5728949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_5728949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5728949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5728949 prefixEnd_5728949 := by exact prefixLift 5728949
  have htrace : WordTrace (prefixWord ++ tailWord_5728949) baseStart_5728949 baseEnd_5728949 := by
    simpa [prefixWord, tailWord_5728949, baseEnd_5728949] using wordTrace_append hprefix tailTrace_5728949
  have hstable : (prefixWord ++ tailWord_5728949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5728949).length < 2 ^ (prefixWord ++ tailWord_5728949).sum := by decide
  have hdescent : baseEnd_5728949 < baseStart_5728949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5728949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729010 : List Nat := [3, 2, 1, 3, 1, 3, 1, 4, 1, 1, 3]
def baseStart_5729010 : Nat := 118140960795 + 5729010 * 2 ^ 59
def prefixEnd_5729010 : Nat := 4983230072969 + 3 ^ 40 * 5729010 * 2
def baseEnd_5729010 : Nat := 2941735804414735455727769

theorem tailTrace_5729010 : CollatzResearch.WordTrace tailWord_5729010 prefixEnd_5729010 2941735804414735455727769 := by
  unfold tailWord_5729010
  simp only [CollatzResearch.WordTrace]
  refine ⟨52238540243695670463940121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139302773983188454570506989 52238540243695670463940121)
  ·
    refine ⟨39178905182771752847955091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52238540243695670463940121 39178905182771752847955091)
    ·
      refine ⟨58768357774157629271932637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39178905182771752847955091 58768357774157629271932637)
      ·
        refine ⟨22038134165309110976974739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58768357774157629271932637 22038134165309110976974739)
        ·
          refine ⟨33057201247963666465462109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22038134165309110976974739 33057201247963666465462109)
          ·
            refine ⟨12396450467986374924548291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33057201247963666465462109 12396450467986374924548291)
            ·
              refine ⟨18594675701979562386822437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12396450467986374924548291 18594675701979562386822437)
              ·
                refine ⟨3486501694121167947529207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18594675701979562386822437 3486501694121167947529207)
                ·
                  refine ⟨5229752541181751921293811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486501694121167947529207 5229752541181751921293811)
                  ·
                    refine ⟨7844628811772627881940717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229752541181751921293811 7844628811772627881940717)
                    ·
                      refine ⟨2941735804414735455727769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844628811772627881940717 2941735804414735455727769)
                      ·
                        rfl

theorem cell23_5729010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_5729010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729010 prefixEnd_5729010 := by exact prefixLift 5729010
  have htrace : WordTrace (prefixWord ++ tailWord_5729010) baseStart_5729010 baseEnd_5729010 := by
    simpa [prefixWord, tailWord_5729010, baseEnd_5729010] using wordTrace_append hprefix tailTrace_5729010
  have hstable : (prefixWord ++ tailWord_5729010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729010).length < 2 ^ (prefixWord ++ tailWord_5729010).sum := by decide
  have hdescent : baseEnd_5729010 < baseStart_5729010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729026 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_5729026 : Nat := 118140960795 + 5729026 * 2 ^ 59
def prefixEnd_5729026 : Nat := 4983230072969 + 3 ^ 40 * 5729026 * 2
def baseEnd_5729026 : Nat := 980581340035069131042565

theorem tailTrace_5729026 : CollatzResearch.WordTrace tailWord_5729026 prefixEnd_5729026 980581340035069131042565 := by
  unfold tailWord_5729026
  simp only [CollatzResearch.WordTrace]
  refine ⟨52238686135681179147085733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139303163028483144392228621 52238686135681179147085733)
  ·
    refine ⟨9794753650440221090078575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52238686135681179147085733 9794753650440221090078575)
    ·
      refine ⟨14692130475660331635117863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9794753650440221090078575 14692130475660331635117863)
      ·
        refine ⟨22038195713490497452676795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14692130475660331635117863 22038195713490497452676795)
        ·
          refine ⟨33057293570235746179015193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22038195713490497452676795 33057293570235746179015193)
          ·
            refine ⟨24792970177676809634261395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33057293570235746179015193 24792970177676809634261395)
            ·
              refine ⟨37189455266515214451392093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24792970177676809634261395 37189455266515214451392093)
              ·
                refine ⟨13946045724943205419272035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37189455266515214451392093 13946045724943205419272035)
                ·
                  refine ⟨20919068587414808128908053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13946045724943205419272035 20919068587414808128908053)
                  ·
                    refine ⟨980581340035069131042565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20919068587414808128908053 980581340035069131042565)
                    ·
                      rfl

theorem cell23_5729026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_5729026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729026 prefixEnd_5729026 := by exact prefixLift 5729026
  have htrace : WordTrace (prefixWord ++ tailWord_5729026) baseStart_5729026 baseEnd_5729026 := by
    simpa [prefixWord, tailWord_5729026, baseEnd_5729026] using wordTrace_append hprefix tailTrace_5729026
  have hstable : (prefixWord ++ tailWord_5729026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729026).length < 2 ^ (prefixWord ++ tailWord_5729026).sum := by decide
  have hdescent : baseEnd_5729026 < baseStart_5729026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729036 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 1, 2, 3]
def baseStart_5729036 : Nat := 118140960795 + 5729036 * 2 ^ 59
def prefixEnd_5729036 : Nat := 4983230072969 + 3 ^ 40 * 5729036 * 2
def baseEnd_5729036 : Nat := 2941749154911752354002649

theorem tailTrace_5729036 : CollatzResearch.WordTrace tailWord_5729036 prefixEnd_5729036 2941749154911752354002649 := by
  unfold tailWord_5729036
  simp only [CollatzResearch.WordTrace]
  refine ⟨104477554636344244148103481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139303406181792325530804641 104477554636344244148103481)
  ·
    refine ⟨78358165977258183111077611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104477554636344244148103481 78358165977258183111077611)
    ·
      refine ⟨117537248965887274666616417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78358165977258183111077611 117537248965887274666616417)
      ·
        refine ⟨88152936724415455999962313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117537248965887274666616417 88152936724415455999962313)
        ·
          refine ⟨66114702543311591999971735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88152936724415455999962313 66114702543311591999971735)
          ·
            refine ⟨99172053814967387999957603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66114702543311591999971735 99172053814967387999957603)
            ·
              refine ⟨148758080722451081999936405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99172053814967387999957603 148758080722451081999936405)
              ·
                refine ⟨6973035033864894468747019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148758080722451081999936405 6973035033864894468747019)
                ·
                  refine ⟨10459552550797341703120529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6973035033864894468747019 10459552550797341703120529)
                  ·
                    refine ⟨7844664413098006277340397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10459552550797341703120529 7844664413098006277340397)
                    ·
                      refine ⟨2941749154911752354002649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844664413098006277340397 2941749154911752354002649)
                      ·
                        rfl

theorem cell23_5729036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_5729036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729036 prefixEnd_5729036 := by exact prefixLift 5729036
  have htrace : WordTrace (prefixWord ++ tailWord_5729036) baseStart_5729036 baseEnd_5729036 := by
    simpa [prefixWord, tailWord_5729036, baseEnd_5729036] using wordTrace_append hprefix tailTrace_5729036
  have hstable : (prefixWord ++ tailWord_5729036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729036).length < 2 ^ (prefixWord ++ tailWord_5729036).sum := by decide
  have hdescent : baseEnd_5729036 < baseStart_5729036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729039 : List Nat := [1, 1, 2, 1, 1, 1, 9, 7]
def baseStart_5729039 : Nat := 118140960795 + 5729039 * 2 ^ 59
def prefixEnd_5729039 : Nat := 4983230072969 + 3 ^ 40 * 5729039 * 2
def baseEnd_5729039 : Nat := 108953729457545031195005

theorem tailTrace_5729039 : CollatzResearch.WordTrace tailWord_5729039 prefixEnd_5729039 108953729457545031195005 := by
  unfold tailWord_5729039
  simp only [CollatzResearch.WordTrace]
  refine ⟨208955218691677619808566171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139303479127785079872377447 208955218691677619808566171)
  ·
    refine ⟨313432828037516429712849257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208955218691677619808566171 313432828037516429712849257)
    ·
      refine ⟨235074621028137322284636943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313432828037516429712849257 235074621028137322284636943)
      ·
        refine ⟨352611931542205983426955415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235074621028137322284636943 352611931542205983426955415)
        ·
          refine ⟨528917897313308975140433123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352611931542205983426955415 528917897313308975140433123)
          ·
            refine ⟨793376845969963462710649685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528917897313308975140433123 793376845969963462710649685)
            ·
              refine ⟨4648692456855254664320213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 793376845969963462710649685 4648692456855254664320213)
              ·
                refine ⟨108953729457545031195005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4648692456855254664320213 108953729457545031195005)
                ·
                  rfl

theorem cell23_5729039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 7].length) (baseStart_5729039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729039 prefixEnd_5729039 := by exact prefixLift 5729039
  have htrace : WordTrace (prefixWord ++ tailWord_5729039) baseStart_5729039 baseEnd_5729039 := by
    simpa [prefixWord, tailWord_5729039, baseEnd_5729039] using wordTrace_append hprefix tailTrace_5729039
  have hstable : (prefixWord ++ tailWord_5729039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729039).length < 2 ^ (prefixWord ++ tailWord_5729039).sum := by decide
  have hdescent : baseEnd_5729039 < baseStart_5729039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729049 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 3, 3, 3]
def baseStart_5729049 : Nat := 118140960795 + 5729049 * 2 ^ 59
def prefixEnd_5729049 : Nat := 4983230072969 + 3 ^ 40 * 5729049 * 2
def baseEnd_5729049 : Nat := 2941755830160260803140089

theorem tailTrace_5729049 : CollatzResearch.WordTrace tailWord_5729049 prefixEnd_5729049 2941755830160260803140089 := by
  unfold tailWord_5729049
  simp only [CollatzResearch.WordTrace]
  refine ⟨208955583421641391516430201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139303722281094261010953467 208955583421641391516430201)
  ·
    refine ⟨156716687566231043637322651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208955583421641391516430201 156716687566231043637322651)
    ·
      refine ⟨235075031349346565455983977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156716687566231043637322651 235075031349346565455983977)
      ·
        refine ⟨176306273512009924091987983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235075031349346565455983977 176306273512009924091987983)
        ·
          refine ⟨264459410268014886137981975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176306273512009924091987983 264459410268014886137981975)
          ·
            refine ⟨396689115402022329206972963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264459410268014886137981975 396689115402022329206972963)
            ·
              refine ⟨595033673103033493810459445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396689115402022329206972963 595033673103033493810459445)
              ·
                refine ⟨55784406853409390044730573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 595033673103033493810459445 55784406853409390044730573)
                ·
                  refine ⟨20919152570028521266773965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55784406853409390044730573 20919152570028521266773965)
                  ·
                    refine ⟨7844682213760695475040237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20919152570028521266773965 7844682213760695475040237)
                    ·
                      refine ⟨2941755830160260803140089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844682213760695475040237 2941755830160260803140089)
                      ·
                        rfl

theorem cell23_5729049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_5729049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729049 prefixEnd_5729049 := by exact prefixLift 5729049
  have htrace : WordTrace (prefixWord ++ tailWord_5729049) baseStart_5729049 baseEnd_5729049 := by
    simpa [prefixWord, tailWord_5729049, baseEnd_5729049] using wordTrace_append hprefix tailTrace_5729049
  have hstable : (prefixWord ++ tailWord_5729049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729049).length < 2 ^ (prefixWord ++ tailWord_5729049).sum := by decide
  have hdescent : baseEnd_5729049 < baseStart_5729049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729060 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_5729060 : Nat := 118140960795 + 5729060 * 2 ^ 59
def prefixEnd_5729060 : Nat := 4983230072969 + 3 ^ 40 * 5729060 * 2
def baseEnd_5729060 : Nat := 980587159482486753367513

theorem tailTrace_5729060 : CollatzResearch.WordTrace tailWord_5729060 prefixEnd_5729060 980587159482486753367513 := by
  unfold tailWord_5729060
  simp only [CollatzResearch.WordTrace]
  refine ⟨104477992312300770197540317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139303989749734360263387089 104477992312300770197540317)
  ·
    refine ⟨39179247117112788824077619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104477992312300770197540317 39179247117112788824077619)
    ·
      refine ⟨58768870675669183236116429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39179247117112788824077619 58768870675669183236116429)
      ·
        refine ⟨22038326503375943713543661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58768870675669183236116429 22038326503375943713543661)
        ·
          refine ⟨8264372438765978892578873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22038326503375943713543661 8264372438765978892578873)
          ·
            refine ⟨6198279329074484169434155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8264372438765978892578873 6198279329074484169434155)
            ·
              refine ⟨9297418993611726254151233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6198279329074484169434155 9297418993611726254151233)
              ·
                refine ⟨6973064245208794690613425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9297418993611726254151233 6973064245208794690613425)
                ·
                  refine ⟨5229798183906596017960069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6973064245208794690613425 5229798183906596017960069)
                  ·
                    refine ⟨980587159482486753367513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5229798183906596017960069 980587159482486753367513)
                    ·
                      rfl

theorem cell23_5729060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_5729060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729060 prefixEnd_5729060 := by exact prefixLift 5729060
  have htrace : WordTrace (prefixWord ++ tailWord_5729060) baseStart_5729060 baseEnd_5729060 := by
    simpa [prefixWord, tailWord_5729060, baseEnd_5729060] using wordTrace_append hprefix tailTrace_5729060
  have hstable : (prefixWord ++ tailWord_5729060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729060).length < 2 ^ (prefixWord ++ tailWord_5729060).sum := by decide
  have hdescent : baseEnd_5729060 < baseStart_5729060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729101 : List Nat := [1, 6, 1, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_5729101 : Nat := 118140960795 + 5729101 * 2 ^ 59
def prefixEnd_5729101 : Nat := 4983230072969 + 3 ^ 40 * 5729101 * 2
def baseEnd_5729101 : Nat := 2941782531154294599689851

theorem tailTrace_5729101 : CollatzResearch.WordTrace tailWord_5729101 prefixEnd_5729101 2941782531154294599689851 := by
  unfold tailWord_5729101
  simp only [CollatzResearch.WordTrace]
  refine ⟨208957480017453004397323157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139304986678302002931548771 208957480017453004397323157)
  ·
    refine ⟨9794881875818109581124523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 208957480017453004397323157 9794881875818109581124523)
    ·
      refine ⟨14692322813727164371686785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9794881875818109581124523 14692322813727164371686785)
      ·
        refine ⟨11019242110295373278765089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14692322813727164371686785 11019242110295373278765089)
        ·
          refine ⟨8264431582721529959073817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11019242110295373278765089 8264431582721529959073817)
          ·
            refine ⟨6198323687041147469305363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8264431582721529959073817 6198323687041147469305363)
            ·
              refine ⟨9297485530561721203958045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6198323687041147469305363 9297485530561721203958045)
              ·
                refine ⟨3486557073960645451484267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9297485530561721203958045 3486557073960645451484267)
                ·
                  refine ⟨5229835610940968177226401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486557073960645451484267 5229835610940968177226401)
                  ·
                    refine ⟨3922376708205726132919801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5229835610940968177226401 3922376708205726132919801)
                    ·
                      refine ⟨2941782531154294599689851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922376708205726132919801 2941782531154294599689851)
                      ·
                        rfl

theorem cell23_5729101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_5729101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729101 prefixEnd_5729101 := by exact prefixLift 5729101
  have htrace : WordTrace (prefixWord ++ tailWord_5729101) baseStart_5729101 baseEnd_5729101 := by
    simpa [prefixWord, tailWord_5729101, baseEnd_5729101] using wordTrace_append hprefix tailTrace_5729101
  have hstable : (prefixWord ++ tailWord_5729101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729101).length < 2 ^ (prefixWord ++ tailWord_5729101).sum := by decide
  have hdescent : baseEnd_5729101 < baseStart_5729101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729134 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_5729134 : Nat := 118140960795 + 5729134 * 2 ^ 59
def prefixEnd_5729134 : Nat := 4983230072969 + 3 ^ 40 * 5729134 * 2
def baseEnd_5729134 : Nat := 2941799476015892970577199

theorem tailTrace_5729134 : CollatzResearch.WordTrace tailWord_5729134 prefixEnd_5729134 2941799476015892970577199 := by
  unfold tailWord_5729134
  simp only [CollatzResearch.WordTrace]
  refine ⟨26119835453291681379159307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139305789084222300688849637 26119835453291681379159307)
  ·
    refine ⟨39179753179937522068738961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26119835453291681379159307 39179753179937522068738961)
    ·
      refine ⟨29384814884953141551554221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39179753179937522068738961 29384814884953141551554221)
      ·
        refine ⟨11019305581857428081832833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29384814884953141551554221 11019305581857428081832833)
        ·
          refine ⟨8264479186393071061374625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11019305581857428081832833 8264479186393071061374625)
          ·
            refine ⟨6198359389794803296030969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8264479186393071061374625 6198359389794803296030969)
            ·
              refine ⟨4648769542346102472023227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6198359389794803296030969 4648769542346102472023227)
              ·
                refine ⟨6973154313519153708034841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4648769542346102472023227 6973154313519153708034841)
                ·
                  refine ⟨5229865735139365281026131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6973154313519153708034841 5229865735139365281026131)
                  ·
                    refine ⟨7844798602709047921539197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5229865735139365281026131 7844798602709047921539197)
                    ·
                      refine ⟨2941799476015892970577199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844798602709047921539197 2941799476015892970577199)
                      ·
                        rfl

theorem cell23_5729134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_5729134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729134 prefixEnd_5729134 := by exact prefixLift 5729134
  have htrace : WordTrace (prefixWord ++ tailWord_5729134) baseStart_5729134 baseEnd_5729134 := by
    simpa [prefixWord, tailWord_5729134, baseEnd_5729134] using wordTrace_append hprefix tailTrace_5729134
  have hstable : (prefixWord ++ tailWord_5729134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729134).length < 2 ^ (prefixWord ++ tailWord_5729134).sum := by decide
  have hdescent : baseEnd_5729134 < baseStart_5729134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729156 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_5729156 : Nat := 118140960795 + 5729156 * 2 ^ 59
def prefixEnd_5729156 : Nat := 4983230072969 + 3 ^ 40 * 5729156 * 2
def baseEnd_5729156 : Nat := 2941810772590291884502097

theorem tailTrace_5729156 : CollatzResearch.WordTrace tailWord_5729156 prefixEnd_5729156 2941810772590291884502097 := by
  unfold tailWord_5729156
  simp only [CollatzResearch.WordTrace]
  refine ⟨104479743016126874395287661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139306324021502499193716881 104479743016126874395287661)
  ·
    refine ⟨39179903631047577898232873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104479743016126874395287661 39179903631047577898232873)
    ·
      refine ⟨29384927723285683423674655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39179903631047577898232873 29384927723285683423674655)
      ·
        refine ⟨44077391584928525135511983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29384927723285683423674655 44077391584928525135511983)
        ·
          refine ⟨66116087377392787703267975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44077391584928525135511983 66116087377392787703267975)
          ·
            refine ⟨99174131066089181554901963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66116087377392787703267975 99174131066089181554901963)
            ·
              refine ⟨148761196599133772332352945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99174131066089181554901963 148761196599133772332352945)
              ·
                refine ⟨111570897449350329249264709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148761196599133772332352945 111570897449350329249264709)
                ·
                  refine ⟨20919543271753186734237133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111570897449350329249264709 20919543271753186734237133)
                  ·
                    refine ⟨7844828726907445025338925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20919543271753186734237133 7844828726907445025338925)
                    ·
                      refine ⟨2941810772590291884502097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844828726907445025338925 2941810772590291884502097)
                      ·
                        rfl

theorem cell23_5729156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_5729156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729156 prefixEnd_5729156 := by exact prefixLift 5729156
  have htrace : WordTrace (prefixWord ++ tailWord_5729156) baseStart_5729156 baseEnd_5729156 := by
    simpa [prefixWord, tailWord_5729156, baseEnd_5729156] using wordTrace_append hprefix tailTrace_5729156
  have hstable : (prefixWord ++ tailWord_5729156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729156).length < 2 ^ (prefixWord ++ tailWord_5729156).sum := by decide
  have hdescent : baseEnd_5729156 < baseStart_5729156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729179 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 4]
def baseStart_5729179 : Nat := 118140960795 + 5729179 * 2 ^ 59
def prefixEnd_5729179 : Nat := 4983230072969 + 3 ^ 40 * 5729179 * 2
def baseEnd_5729179 : Nat := 2941822582645345294514491

theorem tailTrace_5729179 : CollatzResearch.WordTrace tailWord_5729179 prefixEnd_5729179 2941822582645345294514491 := by
  unfold tailWord_5729179
  simp only [CollatzResearch.WordTrace]
  refine ⟨208960324911170423718662591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139306883274113615812441727 208960324911170423718662591)
  ·
    refine ⟨313440487366755635577993887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208960324911170423718662591 313440487366755635577993887)
    ·
      refine ⟨470160731050133453366990831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313440487366755635577993887 470160731050133453366990831)
      ·
        refine ⟨705241096575200180050486247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470160731050133453366990831 705241096575200180050486247)
        ·
          refine ⟨1057861644862800270075729371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705241096575200180050486247 1057861644862800270075729371)
          ·
            refine ⟨1586792467294200405113594057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057861644862800270075729371 1586792467294200405113594057)
            ·
              refine ⟨1190094350470650303835195543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586792467294200405113594057 1190094350470650303835195543)
              ·
                refine ⟨1785141525705975455752793315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190094350470650303835195543 1785141525705975455752793315)
                ·
                  refine ⟨2677712288558963183629189973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785141525705975455752793315 2677712288558963183629189973)
                  ·
                    refine ⟨15689720440775174904077285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2677712288558963183629189973 15689720440775174904077285)
                    ·
                      refine ⟨2941822582645345294514491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15689720440775174904077285 2941822582645345294514491)
                      ·
                        rfl

theorem cell23_5729179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 4].length) (baseStart_5729179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729179 prefixEnd_5729179 := by exact prefixLift 5729179
  have htrace : WordTrace (prefixWord ++ tailWord_5729179) baseStart_5729179 baseEnd_5729179 := by
    simpa [prefixWord, tailWord_5729179, baseEnd_5729179] using wordTrace_append hprefix tailTrace_5729179
  have hstable : (prefixWord ++ tailWord_5729179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729179).length < 2 ^ (prefixWord ++ tailWord_5729179).sum := by decide
  have hdescent : baseEnd_5729179 < baseStart_5729179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729180 : List Nat := [2, 2, 3, 3, 2, 1, 1, 4, 5]
def baseStart_5729180 : Nat := 118140960795 + 5729180 * 2 ^ 59
def prefixEnd_5729180 : Nat := 4983230072969 + 3 ^ 40 * 5729180 * 2
def baseEnd_5729180 : Nat := 326869232902888865622443

theorem tailTrace_5729180 : CollatzResearch.WordTrace tailWord_5729180 prefixEnd_5729180 326869232902888865622443 := by
  unfold tailWord_5729180
  simp only [CollatzResearch.WordTrace]
  refine ⟨104480180692083400444724497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139306907589444533926299329 104480180692083400444724497)
  ·
    refine ⟨78360135519062550333543373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104480180692083400444724497 78360135519062550333543373)
    ·
      refine ⟨29385050819648456375078765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78360135519062550333543373 29385050819648456375078765)
      ·
        refine ⟨11019394057368171140654537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29385050819648456375078765 11019394057368171140654537)
        ·
          refine ⟨8264545543026128355490903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11019394057368171140654537 8264545543026128355490903)
          ·
            refine ⟨12396818314539192533236355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8264545543026128355490903 12396818314539192533236355)
            ·
              refine ⟨18595227471808788799854533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12396818314539192533236355 18595227471808788799854533)
              ·
                refine ⟨3486605150964147899972725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18595227471808788799854533 3486605150964147899972725)
                ·
                  refine ⟨326869232902888865622443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3486605150964147899972725 326869232902888865622443)
                  ·
                    rfl

theorem cell23_5729180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_5729180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729180 prefixEnd_5729180 := by exact prefixLift 5729180
  have htrace : WordTrace (prefixWord ++ tailWord_5729180) baseStart_5729180 baseEnd_5729180 := by
    simpa [prefixWord, tailWord_5729180, baseEnd_5729180] using wordTrace_append hprefix tailTrace_5729180
  have hstable : (prefixWord ++ tailWord_5729180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729180).length < 2 ^ (prefixWord ++ tailWord_5729180).sum := by decide
  have hdescent : baseEnd_5729180 < baseStart_5729180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729183 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 2, 5, 2]
def baseStart_5729183 : Nat := 118140960795 + 5729183 * 2 ^ 59
def prefixEnd_5729183 : Nat := 4983230072969 + 3 ^ 40 * 5729183 * 2
def baseEnd_5729183 : Nat := 2941824636567963278864473

theorem tailTrace_5729183 : CollatzResearch.WordTrace tailWord_5729183 prefixEnd_5729183 2941824636567963278864473 := by
  unfold tailWord_5729183
  simp only [CollatzResearch.WordTrace]
  refine ⟨208960470803155932401808203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139306980535437288267872135 208960470803155932401808203)
  ·
    refine ⟨313440706204733898602712305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208960470803155932401808203 313440706204733898602712305)
    ·
      refine ⟨235080529653550423952034229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313440706204733898602712305 235080529653550423952034229)
      ·
        refine ⟨22038799655020352245503209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235080529653550423952034229 22038799655020352245503209)
        ·
          refine ⟨16529099741265264184127407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22038799655020352245503209 16529099741265264184127407)
          ·
            refine ⟨24793649611897896276191111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16529099741265264184127407 24793649611897896276191111)
            ·
              refine ⟨37190474417846844414286667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24793649611897896276191111 37190474417846844414286667)
              ·
                refine ⟨55785711626770266621430001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37190474417846844414286667 55785711626770266621430001)
                ·
                  refine ⟨41839283720077699966072501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55785711626770266621430001 41839283720077699966072501)
                  ·
                    refine ⟨3922432848757284371819297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41839283720077699966072501 3922432848757284371819297)
                    ·
                      refine ⟨2941824636567963278864473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922432848757284371819297 2941824636567963278864473)
                      ·
                        rfl

theorem cell23_5729183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_5729183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729183 prefixEnd_5729183 := by exact prefixLift 5729183
  have htrace : WordTrace (prefixWord ++ tailWord_5729183) baseStart_5729183 baseEnd_5729183 := by
    simpa [prefixWord, tailWord_5729183, baseEnd_5729183] using wordTrace_append hprefix tailTrace_5729183
  have hstable : (prefixWord ++ tailWord_5729183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729183).length < 2 ^ (prefixWord ++ tailWord_5729183).sum := by decide
  have hdescent : baseEnd_5729183 < baseStart_5729183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729189 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_5729189 : Nat := 118140960795 + 5729189 * 2 ^ 59
def prefixEnd_5729189 : Nat := 4983230072969 + 3 ^ 40 * 5729189 * 2
def baseEnd_5729189 : Nat := 980609239150630085129815

theorem tailTrace_5729189 : CollatzResearch.WordTrace tailWord_5729189 prefixEnd_5729189 980609239150630085129815 := by
  unfold tailWord_5729189
  simp only [CollatzResearch.WordTrace]
  refine ⟨208960689641134195426526621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139307126427422796951017747 208960689641134195426526621)
  ·
    refine ⟨78360258615425323284947483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208960689641134195426526621 78360258615425323284947483)
    ·
      refine ⟨117540387923137984927421225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78360258615425323284947483 117540387923137984927421225)
      ·
        refine ⟨88155290942353488695565919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117540387923137984927421225 88155290942353488695565919)
        ·
          refine ⟨132232936413530233043348879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88155290942353488695565919 132232936413530233043348879)
          ·
            refine ⟨198349404620295349565023319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132232936413530233043348879 198349404620295349565023319)
            ·
              refine ⟨297524106930443024347534979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198349404620295349565023319 297524106930443024347534979)
              ·
                refine ⟨446286160395664536521302469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297524106930443024347534979 446286160395664536521302469)
                ·
                  refine ⟨83678655074187100597744213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 446286160395664536521302469 83678655074187100597744213)
                  ·
                    refine ⟨980609239150630085129815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83678655074187100597744213 980609239150630085129815)
                    ·
                      rfl

theorem cell23_5729189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_5729189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729189 prefixEnd_5729189 := by exact prefixLift 5729189
  have htrace : WordTrace (prefixWord ++ tailWord_5729189) baseStart_5729189 baseEnd_5729189 := by
    simpa [prefixWord, tailWord_5729189, baseEnd_5729189] using wordTrace_append hprefix tailTrace_5729189
  have hstable : (prefixWord ++ tailWord_5729189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729189).length < 2 ^ (prefixWord ++ tailWord_5729189).sum := by decide
  have hdescent : baseEnd_5729189 < baseStart_5729189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729213 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_5729213 : Nat := 118140960795 + 5729213 * 2 ^ 59
def prefixEnd_5729213 : Nat := 4983230072969 + 3 ^ 40 * 5729213 * 2
def baseEnd_5729213 : Nat := 2941840040987598161489335

theorem tailTrace_5729213 : CollatzResearch.WordTrace tailWord_5729213 prefixEnd_5729213 2941840040987598161489335 := by
  unfold tailWord_5729213
  simp only [CollatzResearch.WordTrace]
  refine ⟨208961564993047247525400293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139307709995364831683600195 208961564993047247525400293)
  ·
    refine ⟨39180293436196358911012555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 208961564993047247525400293 39180293436196358911012555)
    ·
      refine ⟨58770440154294538366518833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39180293436196358911012555 58770440154294538366518833)
      ·
        refine ⟨44077830115720903774889125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58770440154294538366518833 44077830115720903774889125)
        ·
          refine ⟨8264593146697669457791711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44077830115720903774889125 8264593146697669457791711)
          ·
            refine ⟨12396889720046504186687567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8264593146697669457791711 12396889720046504186687567)
            ·
              refine ⟨18595334580069756280031351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12396889720046504186687567 18595334580069756280031351)
              ·
                refine ⟨27893001870104634420047027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18595334580069756280031351 27893001870104634420047027)
                ·
                  refine ⟨41839502805156951630070541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27893001870104634420047027 41839502805156951630070541)
                  ·
                    refine ⟨15689813551933856861276453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41839502805156951630070541 15689813551933856861276453)
                    ·
                      refine ⟨2941840040987598161489335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15689813551933856861276453 2941840040987598161489335)
                      ·
                        rfl

theorem cell23_5729213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_5729213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729213 prefixEnd_5729213 := by exact prefixLift 5729213
  have htrace : WordTrace (prefixWord ++ tailWord_5729213) baseStart_5729213 baseEnd_5729213 := by
    simpa [prefixWord, tailWord_5729213, baseEnd_5729213] using wordTrace_append hprefix tailTrace_5729213
  have hstable : (prefixWord ++ tailWord_5729213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729213).length < 2 ^ (prefixWord ++ tailWord_5729213).sum := by decide
  have hdescent : baseEnd_5729213 < baseStart_5729213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729219 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 10]
def baseStart_5729219 : Nat := 118140960795 + 5729219 * 2 ^ 59
def prefixEnd_5729219 : Nat := 4983230072969 + 3 ^ 40 * 5729219 * 2
def baseEnd_5729219 : Nat := 326871457985725015334923

theorem tailTrace_5729219 : CollatzResearch.WordTrace tailWord_5729219 prefixEnd_5729219 326871457985725015334923 := by
  unfold tailWord_5729219
  simp only [CollatzResearch.WordTrace]
  refine ⟨208961783831025510550118711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139307855887350340366745807 208961783831025510550118711)
  ·
    refine ⟨313442675746538265825178067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208961783831025510550118711 313442675746538265825178067)
    ·
      refine ⟨470164013619807398737767101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313442675746538265825178067 470164013619807398737767101)
      ·
        refine ⟨176311505107427774526662663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 470164013619807398737767101 176311505107427774526662663)
        ·
          refine ⟨264467257661141661789993995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176311505107427774526662663 264467257661141661789993995)
          ·
            refine ⟨396700886491712492684990993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264467257661141661789993995 396700886491712492684990993)
            ·
              refine ⟨297525664868784369513743245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396700886491712492684990993 297525664868784369513743245)
              ·
                refine ⟨111572124325794138567653717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297525664868784369513743245 111572124325794138567653717)
                ·
                  refine ⟨326871457985725015334923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 111572124325794138567653717 326871457985725015334923)
                  ·
                    rfl

theorem cell23_5729219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 10].length) (baseStart_5729219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729219 prefixEnd_5729219 := by exact prefixLift 5729219
  have htrace : WordTrace (prefixWord ++ tailWord_5729219) baseStart_5729219 baseEnd_5729219 := by
    simpa [prefixWord, tailWord_5729219, baseEnd_5729219] using wordTrace_append hprefix tailTrace_5729219
  have hstable : (prefixWord ++ tailWord_5729219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729219).length < 2 ^ (prefixWord ++ tailWord_5729219).sum := by decide
  have hdescent : baseEnd_5729219 < baseStart_5729219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729240 : List Nat := [2, 1, 2, 2, 2, 3, 2, 4, 1, 4]
def baseStart_5729240 : Nat := 118140960795 + 5729240 * 2 ^ 59
def prefixEnd_5729240 : Nat := 4983230072969 + 3 ^ 40 * 5729240 * 2
def baseEnd_5729240 : Nat := 980617968321756518617237

theorem tailTrace_5729240 : CollatzResearch.WordTrace tailWord_5729240 prefixEnd_5729240 980617968321756518617237 := by
  unfold tailWord_5729240
  simp only [CollatzResearch.WordTrace]
  refine ⟨104481274881974715568316587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139308366509299620757755449 104481274881974715568316587)
  ·
    refine ⟨156721912322962073352474881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104481274881974715568316587 156721912322962073352474881)
    ·
      refine ⟨117541434242221555014356161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156721912322962073352474881 117541434242221555014356161)
      ·
        refine ⟨88156075681666166260767121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117541434242221555014356161 88156075681666166260767121)
        ·
          refine ⟨66117056761249624695575341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88156075681666166260767121 66117056761249624695575341)
          ·
            refine ⟨24793896285468609260840753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66117056761249624695575341 24793896285468609260840753)
            ·
              refine ⟨18595422214101456945630565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24793896285468609260840753 18595422214101456945630565)
              ·
                refine ⟨3486641665144023177305731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18595422214101456945630565 3486641665144023177305731)
                ·
                  refine ⟨5229962497716034765958597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486641665144023177305731 5229962497716034765958597)
                  ·
                    refine ⟨980617968321756518617237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5229962497716034765958597 980617968321756518617237)
                    ·
                      rfl

theorem cell23_5729240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_5729240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729240 prefixEnd_5729240 := by exact prefixLift 5729240
  have htrace : WordTrace (prefixWord ++ tailWord_5729240) baseStart_5729240 baseEnd_5729240 := by
    simpa [prefixWord, tailWord_5729240, baseEnd_5729240] using wordTrace_append hprefix tailTrace_5729240
  have hstable : (prefixWord ++ tailWord_5729240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729240).length < 2 ^ (prefixWord ++ tailWord_5729240).sum := by decide
  have hdescent : baseEnd_5729240 < baseStart_5729240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729250 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_5729250 : Nat := 118140960795 + 5729250 * 2 ^ 59
def prefixEnd_5729250 : Nat := 4983230072969 + 3 ^ 40 * 5729250 * 2
def baseEnd_5729250 : Nat := 2941859039771814516726665

theorem tailTrace_5729250 : CollatzResearch.WordTrace tailWord_5729250 prefixEnd_5729250 2941859039771814516726665 := by
  unfold tailWord_5729250
  simp only [CollatzResearch.WordTrace]
  refine ⟨52240728623478300711124301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139308609662608801896331469 52240728623478300711124301)
  ·
    refine ⟨19590273233804362766671613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52240728623478300711124301 19590273233804362766671613)
    ·
      refine ⟨7346352462676636037501855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19590273233804362766671613 7346352462676636037501855)
      ·
        refine ⟨11019528694014954056252783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7346352462676636037501855 11019528694014954056252783)
        ·
          refine ⟨16529293041022431084379175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11019528694014954056252783 16529293041022431084379175)
          ·
            refine ⟨24793939561533646626568763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16529293041022431084379175 24793939561533646626568763)
            ·
              refine ⟨37190909342300469939853145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24793939561533646626568763 37190909342300469939853145)
              ·
                refine ⟨27893182006725352454889859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37190909342300469939853145 27893182006725352454889859)
                ·
                  refine ⟨41839773010088028682334789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27893182006725352454889859 41839773010088028682334789)
                  ·
                    refine ⟨7844957439391505377937773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41839773010088028682334789 7844957439391505377937773)
                    ·
                      refine ⟨2941859039771814516726665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7844957439391505377937773 2941859039771814516726665)
                      ·
                        rfl

theorem cell23_5729250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_5729250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729250 prefixEnd_5729250 := by exact prefixLift 5729250
  have htrace : WordTrace (prefixWord ++ tailWord_5729250) baseStart_5729250 baseEnd_5729250 := by
    simpa [prefixWord, tailWord_5729250, baseEnd_5729250] using wordTrace_append hprefix tailTrace_5729250
  have hstable : (prefixWord ++ tailWord_5729250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729250).length < 2 ^ (prefixWord ++ tailWord_5729250).sum := by decide
  have hdescent : baseEnd_5729250 < baseStart_5729250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729273 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 1, 5, 2]
def baseStart_5729273 : Nat := 118140960795 + 5729273 * 2 ^ 59
def prefixEnd_5729273 : Nat := 4983230072969 + 3 ^ 40 * 5729273 * 2
def baseEnd_5729273 : Nat := 2941870849826867926739059

theorem tailTrace_5729273 : CollatzResearch.WordTrace tailWord_5729273 prefixEnd_5729273 2941870849826867926739059 := by
  unfold tailWord_5729273
  simp only [CollatzResearch.WordTrace]
  refine ⟨208963753372829877772584473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139309168915219918515056315 208963753372829877772584473)
  ·
    refine ⟨156722815029622408329438355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208963753372829877772584473 156722815029622408329438355)
    ·
      refine ⟨235084222544433612494157533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156722815029622408329438355 235084222544433612494157533)
      ·
        refine ⟨88156583454162604685309075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235084222544433612494157533 88156583454162604685309075)
        ·
          refine ⟨132234875181243907027963613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88156583454162604685309075 132234875181243907027963613)
          ·
            refine ⟨49588078192966465135486355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132234875181243907027963613 49588078192966465135486355)
            ·
              refine ⟨74382117289449697703229533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49588078192966465135486355 74382117289449697703229533)
              ·
                refine ⟨27893293983543636638711075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74382117289449697703229533 27893293983543636638711075)
                ·
                  refine ⟨41839940975315454958066613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27893293983543636638711075 41839940975315454958066613)
                  ·
                    refine ⟨3922494466435823902318745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41839940975315454958066613 3922494466435823902318745)
                    ·
                      refine ⟨2941870849826867926739059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922494466435823902318745 2941870849826867926739059)
                      ·
                        rfl

theorem cell23_5729273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_5729273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729273 prefixEnd_5729273 := by exact prefixLift 5729273
  have htrace : WordTrace (prefixWord ++ tailWord_5729273) baseStart_5729273 baseEnd_5729273 := by
    simpa [prefixWord, tailWord_5729273, baseEnd_5729273] using wordTrace_append hprefix tailTrace_5729273
  have hstable : (prefixWord ++ tailWord_5729273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729273).length < 2 ^ (prefixWord ++ tailWord_5729273).sum := by decide
  have hdescent : baseEnd_5729273 < baseStart_5729273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729290 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2]
def baseStart_5729290 : Nat := 118140960795 + 5729290 * 2 ^ 59
def prefixEnd_5729290 : Nat := 4983230072969 + 3 ^ 40 * 5729290 * 2
def baseEnd_5729290 : Nat := 2941879578997994360226481

theorem tailTrace_5729290 : CollatzResearch.WordTrace tailWord_5729290 prefixEnd_5729290 2941879578997994360226481 := by
  unfold tailWord_5729290
  simp only [CollatzResearch.WordTrace]
  refine ⟨52241093353442072418988331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139309582275845526450635549 52241093353442072418988331)
  ·
    refine ⟨78361640030163108628482497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52241093353442072418988331 78361640030163108628482497)
    ·
      refine ⟨58771230022622331471361873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78361640030163108628482497 58771230022622331471361873)
      ·
        refine ⟨44078422516966748603521405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58771230022622331471361873 44078422516966748603521405)
        ·
          refine ⟨16529408443862530726320527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44078422516966748603521405 16529408443862530726320527)
          ·
            refine ⟨24794112665793796089480791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16529408443862530726320527 24794112665793796089480791)
            ·
              refine ⟨37191168998690694134221187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24794112665793796089480791 37191168998690694134221187)
              ·
                refine ⟨55786753498036041201331781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37191168998690694134221187 55786753498036041201331781)
                ·
                  refine ⟨10460016280881757725249709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55786753498036041201331781 10460016280881757725249709)
                  ·
                    refine ⟨3922506105330659146968641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10460016280881757725249709 3922506105330659146968641)
                    ·
                      refine ⟨2941879578997994360226481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922506105330659146968641 2941879578997994360226481)
                      ·
                        rfl

theorem cell23_5729290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_5729290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729290 prefixEnd_5729290 := by exact prefixLift 5729290
  have htrace : WordTrace (prefixWord ++ tailWord_5729290) baseStart_5729290 baseEnd_5729290 := by
    simpa [prefixWord, tailWord_5729290, baseEnd_5729290] using wordTrace_append hprefix tailTrace_5729290
  have hstable : (prefixWord ++ tailWord_5729290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729290).length < 2 ^ (prefixWord ++ tailWord_5729290).sum := by decide
  have hdescent : baseEnd_5729290 < baseStart_5729290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729323 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 3]
def baseStart_5729323 : Nat := 118140960795 + 5729323 * 2 ^ 59
def prefixEnd_5729323 : Nat := 4983230072969 + 3 ^ 40 * 5729323 * 2
def baseEnd_5729323 : Nat := 2941896523859592731113829

theorem tailTrace_5729323 : CollatzResearch.WordTrace tailWord_5729323 prefixEnd_5729323 2941896523859592731113829 := by
  unfold tailWord_5729323
  simp only [CollatzResearch.WordTrace]
  refine ⟨208965577022648736311904623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139310384681765824207936415 208965577022648736311904623)
  ·
    refine ⟨313448365533973104467856935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208965577022648736311904623 313448365533973104467856935)
    ·
      refine ⟨470172548300959656701785403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313448365533973104467856935 470172548300959656701785403)
      ·
        refine ⟨705258822451439485052678105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470172548300959656701785403 705258822451439485052678105)
        ·
          refine ⟨528944116838579613789508579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705258822451439485052678105 528944116838579613789508579)
          ·
            refine ⟨793416175257869420684262869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528944116838579613789508579 793416175257869420684262869)
            ·
              refine ⟨18595691607606314547287411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 793416175257869420684262869 18595691607606314547287411)
              ·
                refine ⟨27893537411409471820931117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18595691607606314547287411 27893537411409471820931117)
                ·
                  refine ⟨10460076529278551932849169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27893537411409471820931117 10460076529278551932849169)
                  ·
                    refine ⟨7845057396958913949636877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10460076529278551932849169 7845057396958913949636877)
                    ·
                      refine ⟨2941896523859592731113829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7845057396958913949636877 2941896523859592731113829)
                      ·
                        rfl

theorem cell23_5729323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 3].length) (baseStart_5729323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729323 prefixEnd_5729323 := by exact prefixLift 5729323
  have htrace : WordTrace (prefixWord ++ tailWord_5729323) baseStart_5729323 baseEnd_5729323 := by
    simpa [prefixWord, tailWord_5729323, baseEnd_5729323] using wordTrace_append hprefix tailTrace_5729323
  have hstable : (prefixWord ++ tailWord_5729323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729323).length < 2 ^ (prefixWord ++ tailWord_5729323).sum := by decide
  have hdescent : baseEnd_5729323 < baseStart_5729323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729337 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 1, 1, 4]
def baseStart_5729337 : Nat := 118140960795 + 5729337 * 2 ^ 59
def prefixEnd_5729337 : Nat := 4983230072969 + 3 ^ 40 * 5729337 * 2
def baseEnd_5729337 : Nat := 2941903712588755676338765

theorem tailTrace_5729337 : CollatzResearch.WordTrace tailWord_5729337 prefixEnd_5729337 2941903712588755676338765 := by
  unfold tailWord_5729337
  simp only [CollatzResearch.WordTrace]
  refine ⟨208966087644598016702914265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139310725096398677801942843 208966087644598016702914265)
  ·
    refine ⟨156724565733448512527185699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208966087644598016702914265 156724565733448512527185699)
    ·
      refine ⟨235086848600172768790778549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156724565733448512527185699 235086848600172768790778549)
      ·
        refine ⟨22039392056266197074135489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235086848600172768790778549 22039392056266197074135489)
        ·
          refine ⟨16529544042199647805601617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22039392056266197074135489 16529544042199647805601617)
          ·
            refine ⟨12397158031649735854201213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16529544042199647805601617 12397158031649735854201213)
            ·
              refine ⟨4648934261868650945325455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12397158031649735854201213 4648934261868650945325455)
              ·
                refine ⟨6973401392802976417988183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4648934261868650945325455 6973401392802976417988183)
                ·
                  refine ⟨10460102089204464626982275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6973401392802976417988183 10460102089204464626982275)
                  ·
                    refine ⟨15690153133806696940473413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10460102089204464626982275 15690153133806696940473413)
                    ·
                      refine ⟨2941903712588755676338765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15690153133806696940473413 2941903712588755676338765)
                      ·
                        rfl

theorem cell23_5729337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_5729337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729337 prefixEnd_5729337 := by exact prefixLift 5729337
  have htrace : WordTrace (prefixWord ++ tailWord_5729337) baseStart_5729337 baseEnd_5729337 := by
    simpa [prefixWord, tailWord_5729337, baseEnd_5729337] using wordTrace_append hprefix tailTrace_5729337
  have hstable : (prefixWord ++ tailWord_5729337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729337).length < 2 ^ (prefixWord ++ tailWord_5729337).sum := by decide
  have hdescent : baseEnd_5729337 < baseStart_5729337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729340 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_5729340 : Nat := 118140960795 + 5729340 * 2 ^ 59
def prefixEnd_5729340 : Nat := 4983230072969 + 3 ^ 40 * 5729340 * 2
def baseEnd_5729340 : Nat := 2941905253030719164601251

theorem tailTrace_5729340 : CollatzResearch.WordTrace tailWord_5729340 prefixEnd_5729340 2941905253030719164601251 := by
  unfold tailWord_5729340
  simp only [CollatzResearch.WordTrace]
  refine ⟨104483098531793574107636737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139310798042391432143515649 104483098531793574107636737)
  ·
    refine ⟨78362323898845180580727553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104483098531793574107636737 78362323898845180580727553)
    ·
      refine ⟨58771742924133885435545665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78362323898845180580727553 58771742924133885435545665)
      ·
        refine ⟨44078807193100414076659249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58771742924133885435545665 44078807193100414076659249)
        ·
          refine ⟨33059105394825310557494437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44078807193100414076659249 33059105394825310557494437)
          ·
            refine ⟨6198582261529745729530207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33059105394825310557494437 6198582261529745729530207)
            ·
              refine ⟨9297873392294618594295311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6198582261529745729530207 9297873392294618594295311)
              ·
                refine ⟨13946810088441927891442967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9297873392294618594295311 13946810088441927891442967)
                ·
                  refine ⟨20920215132662891837164451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13946810088441927891442967 20920215132662891837164451)
                  ·
                    refine ⟨31380322698994337755746677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20920215132662891837164451 31380322698994337755746677)
                    ·
                      refine ⟨2941905253030719164601251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31380322698994337755746677 2941905253030719164601251)
                      ·
                        rfl

theorem cell23_5729340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_5729340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729340 prefixEnd_5729340 := by exact prefixLift 5729340
  have htrace : WordTrace (prefixWord ++ tailWord_5729340) baseStart_5729340 baseEnd_5729340 := by
    simpa [prefixWord, tailWord_5729340, baseEnd_5729340] using wordTrace_append hprefix tailTrace_5729340
  have hstable : (prefixWord ++ tailWord_5729340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729340).length < 2 ^ (prefixWord ++ tailWord_5729340).sum := by decide
  have hdescent : baseEnd_5729340 < baseStart_5729340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729363 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 2, 7, 2]
def baseStart_5729363 : Nat := 118140960795 + 5729363 * 2 ^ 59
def prefixEnd_5729363 : Nat := 4983230072969 + 3 ^ 40 * 5729363 * 2
def baseEnd_5729363 : Nat := 2941917063085772574613645

theorem tailTrace_5729363 : CollatzResearch.WordTrace tailWord_5729363 prefixEnd_5729363 2941917063085772574613645 := by
  unfold tailWord_5729363
  simp only [CollatzResearch.WordTrace]
  refine ⟨208967035942503823143360743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139311357295002548762240495 208967035942503823143360743)
  ·
    refine ⟨313450553913755734715041115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208967035942503823143360743 313450553913755734715041115)
    ·
      refine ⟨470175830870633602072561673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313450553913755734715041115 470175830870633602072561673)
      ·
        refine ⟨352631873152975201554421255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470175830870633602072561673 352631873152975201554421255)
        ·
          refine ⟨528947809729462802331631883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352631873152975201554421255 528947809729462802331631883)
          ·
            refine ⟨793421714594194203497447825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528947809729462802331631883 793421714594194203497447825)
            ·
              refine ⟨595066285945645652623085869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793421714594194203497447825 595066285945645652623085869)
              ·
                refine ⟨223149857229617119733657201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 595066285945645652623085869 223149857229617119733657201)
                ·
                  refine ⟨167362392922212839800242901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223149857229617119733657201 167362392922212839800242901)
                  ·
                    refine ⟨3922556084114363432818193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 167362392922212839800242901 3922556084114363432818193)
                    ·
                      refine ⟨2941917063085772574613645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922556084114363432818193 2941917063085772574613645)
                      ·
                        rfl

theorem cell23_5729363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 7, 2].length) (baseStart_5729363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729363 prefixEnd_5729363 := by exact prefixLift 5729363
  have htrace : WordTrace (prefixWord ++ tailWord_5729363) baseStart_5729363 baseEnd_5729363 := by
    simpa [prefixWord, tailWord_5729363, baseEnd_5729363] using wordTrace_append hprefix tailTrace_5729363
  have hstable : (prefixWord ++ tailWord_5729363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729363).length < 2 ^ (prefixWord ++ tailWord_5729363).sum := by decide
  have hdescent : baseEnd_5729363 < baseStart_5729363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729374 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_5729374 : Nat := 118140960795 + 5729374 * 2 ^ 59
def prefixEnd_5729374 : Nat := 4983230072969 + 3 ^ 40 * 5729374 * 2
def baseEnd_5729374 : Nat := 2941922711372972031576095

theorem tailTrace_5729374 : CollatzResearch.WordTrace tailWord_5729374 prefixEnd_5729374 2941922711372972031576095 := by
  unfold tailWord_5729374
  simp only [CollatzResearch.WordTrace]
  refine ⟨26120929643182996502751397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139311624763642648014674117 26120929643182996502751397)
  ·
    refine ⟨4897674308096811844265887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26120929643182996502751397 4897674308096811844265887)
    ·
      refine ⟨7346511462145217766398831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4897674308096811844265887 7346511462145217766398831)
      ·
        refine ⟨11019767193217826649598247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7346511462145217766398831 11019767193217826649598247)
        ·
          refine ⟨16529650789826739974397371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11019767193217826649598247 16529650789826739974397371)
          ·
            refine ⟨24794476184740109961596057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16529650789826739974397371 24794476184740109961596057)
            ·
              refine ⟨18595857138555082471197043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24794476184740109961596057 18595857138555082471197043)
              ·
                refine ⟨27893785707832623706795565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18595857138555082471197043 27893785707832623706795565)
                ·
                  refine ⟨10460169640437233890048337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27893785707832623706795565 10460169640437233890048337)
                  ·
                    refine ⟨7845127230327925417536253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10460169640437233890048337 7845127230327925417536253)
                    ·
                      refine ⟨2941922711372972031576095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7845127230327925417536253 2941922711372972031576095)
                      ·
                        rfl

theorem cell23_5729374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_5729374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729374 prefixEnd_5729374 := by exact prefixLift 5729374
  have htrace : WordTrace (prefixWord ++ tailWord_5729374) baseStart_5729374 baseEnd_5729374 := by
    simpa [prefixWord, tailWord_5729374, baseEnd_5729374] using wordTrace_append hprefix tailTrace_5729374
  have hstable : (prefixWord ++ tailWord_5729374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729374).length < 2 ^ (prefixWord ++ tailWord_5729374).sum := by decide
  have hdescent : baseEnd_5729374 < baseStart_5729374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729427 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 2, 2, 2]
def baseStart_5729427 : Nat := 118140960795 + 5729427 * 2 ^ 59
def prefixEnd_5729427 : Nat := 4983230072969 + 3 ^ 40 * 5729427 * 2
def baseEnd_5729427 : Nat := 2941949925847660324213351

theorem tailTrace_5729427 : CollatzResearch.WordTrace tailWord_5729427 prefixEnd_5729427 2941949925847660324213351 := by
  unfold tailWord_5729427
  simp only [CollatzResearch.WordTrace]
  refine ⟨208969370214271962073690535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139312913476181308049127023 208969370214271962073690535)
  ·
    refine ⟨313454055321407943110535803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208969370214271962073690535 313454055321407943110535803)
    ·
      refine ⟨470181082982111914665803705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313454055321407943110535803 470181082982111914665803705)
      ·
        refine ⟨352635812236583935999352779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470181082982111914665803705 352635812236583935999352779)
        ·
          refine ⟨528953718354875903999029169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352635812236583935999352779 528953718354875903999029169)
          ·
            refine ⟨396715288766156927999271877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528953718354875903999029169 396715288766156927999271877)
            ·
              refine ⟨74384116643654423999863477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 396715288766156927999271877 74384116643654423999863477)
              ·
                refine ⟨6973510935342602249987201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74384116643654423999863477 6973510935342602249987201)
                ·
                  refine ⟨5230133201506951687490401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6973510935342602249987201 5230133201506951687490401)
                  ·
                    refine ⟨3922599901130213765617801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5230133201506951687490401 3922599901130213765617801)
                    ·
                      refine ⟨2941949925847660324213351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922599901130213765617801 2941949925847660324213351)
                      ·
                        rfl

theorem cell23_5729427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 2, 2].length) (baseStart_5729427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729427 prefixEnd_5729427 := by exact prefixLift 5729427
  have htrace : WordTrace (prefixWord ++ tailWord_5729427) baseStart_5729427 baseEnd_5729427 := by
    simpa [prefixWord, tailWord_5729427, baseEnd_5729427] using wordTrace_append hprefix tailTrace_5729427
  have hstable : (prefixWord ++ tailWord_5729427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729427).length < 2 ^ (prefixWord ++ tailWord_5729427).sum := by decide
  have hdescent : baseEnd_5729427 < baseStart_5729427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729443 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 3]
def baseStart_5729443 : Nat := 118140960795 + 5729443 * 2 ^ 59
def prefixEnd_5729443 : Nat := 4983230072969 + 3 ^ 40 * 5729443 * 2
def baseEnd_5729443 : Nat := 2941958141538132261613277

theorem tailTrace_5729443 : CollatzResearch.WordTrace tailWord_5729443 prefixEnd_5729443 2941958141538132261613277 := by
  unfold tailWord_5729443
  simp only [CollatzResearch.WordTrace]
  refine ⟨208969953782213996806272983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139313302521475997870848655 208969953782213996806272983)
  ·
    refine ⟨313454930673320995209409475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208969953782213996806272983 313454930673320995209409475)
    ·
      refine ⟨470182396009981492814114213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313454930673320995209409475 470182396009981492814114213)
      ·
        refine ⟨88159199251871529902646415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 470182396009981492814114213 88159199251871529902646415)
        ·
          refine ⟨132238798877807294853969623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88159199251871529902646415 132238798877807294853969623)
          ·
            refine ⟨198358198316710942280954435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132238798877807294853969623 198358198316710942280954435)
            ·
              refine ⟨297537297475066413421431653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198358198316710942280954435 297537297475066413421431653)
              ·
                refine ⟨55788243276574952516518435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 297537297475066413421431653 55788243276574952516518435)
                ·
                  refine ⟨83682364914862428774777653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55788243276574952516518435 83682364914862428774777653)
                  ·
                    refine ⟨7845221710768352697635405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83682364914862428774777653 7845221710768352697635405)
                    ·
                      refine ⟨2941958141538132261613277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7845221710768352697635405 2941958141538132261613277)
                      ·
                        rfl

theorem cell23_5729443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_5729443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729443 prefixEnd_5729443 := by exact prefixLift 5729443
  have htrace : WordTrace (prefixWord ++ tailWord_5729443) baseStart_5729443 baseEnd_5729443 := by
    simpa [prefixWord, tailWord_5729443, baseEnd_5729443] using wordTrace_append hprefix tailTrace_5729443
  have hstable : (prefixWord ++ tailWord_5729443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729443).length < 2 ^ (prefixWord ++ tailWord_5729443).sum := by decide
  have hdescent : baseEnd_5729443 < baseStart_5729443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729483 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 4]
def baseStart_5729483 : Nat := 118140960795 + 5729483 * 2 ^ 59
def prefixEnd_5729483 : Nat := 4983230072969 + 3 ^ 40 * 5729483 * 2
def baseEnd_5729483 : Nat := 2941978680764312105113093

theorem tailTrace_5729483 : CollatzResearch.WordTrace tailWord_5729483 prefixEnd_5729483 2941978680764312105113093 := by
  unfold tailWord_5729483
  simp only [CollatzResearch.WordTrace]
  refine ⟨208971412702069083637729103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139314275134712722425152735 208971412702069083637729103)
  ·
    refine ⟨313457119053103625456593655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208971412702069083637729103 313457119053103625456593655)
    ·
      refine ⟨470185678579655438184890483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313457119053103625456593655 470185678579655438184890483)
      ·
        refine ⟨705278517869483157277335725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470185678579655438184890483 705278517869483157277335725)
        ·
          refine ⟨264479444201056183979000897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 705278517869483157277335725 264479444201056183979000897)
          ·
            refine ⟨198359583150792137984250673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264479444201056183979000897 198359583150792137984250673)
            ·
              refine ⟨148769687363094103488188005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198359583150792137984250673 148769687363094103488188005)
              ·
                refine ⟨27894316380580144404035251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148769687363094103488188005 27894316380580144404035251)
                ·
                  refine ⟨41841474570870216606052877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27894316380580144404035251 41841474570870216606052877)
                  ·
                    refine ⟨15690552964076331227269829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41841474570870216606052877 15690552964076331227269829)
                    ·
                      refine ⟨2941978680764312105113093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15690552964076331227269829 2941978680764312105113093)
                      ·
                        rfl

theorem cell23_5729483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 4].length) (baseStart_5729483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729483 prefixEnd_5729483 := by exact prefixLift 5729483
  have htrace : WordTrace (prefixWord ++ tailWord_5729483) baseStart_5729483 baseEnd_5729483 := by
    simpa [prefixWord, tailWord_5729483, baseEnd_5729483] using wordTrace_append hprefix tailTrace_5729483
  have hstable : (prefixWord ++ tailWord_5729483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729483).length < 2 ^ (prefixWord ++ tailWord_5729483).sum := by decide
  have hdescent : baseEnd_5729483 < baseStart_5729483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729517 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5729517 : Nat := 118140960795 + 5729517 * 2 ^ 59
def prefixEnd_5729517 : Nat := 4983230072969 + 3 ^ 40 * 5729517 * 2
def baseEnd_5729517 : Nat := 2941996139106564972087937

theorem tailTrace_5729517 : CollatzResearch.WordTrace tailWord_5729517 prefixEnd_5729517 2941996139106564972087937 := by
  unfold tailWord_5729517
  simp only [CollatzResearch.WordTrace]
  refine ⟨208972652783945907444466805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139315101855963938296311203 208972652783945907444466805)
  ·
    refine ⟨19591186198494928822918763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 208972652783945907444466805 19591186198494928822918763)
    ·
      refine ⟨29386779297742393234378145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19591186198494928822918763 29386779297742393234378145)
      ·
        refine ⟨22040084473306794925783609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29386779297742393234378145 22040084473306794925783609)
        ·
          refine ⟨16530063354980096194337707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22040084473306794925783609 16530063354980096194337707)
          ·
            refine ⟨24795095032470144291506561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16530063354980096194337707 24795095032470144291506561)
            ·
              refine ⟨18596321274352608218629921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24795095032470144291506561 18596321274352608218629921)
              ·
                refine ⟨13947240955764456163972441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18596321274352608218629921 13947240955764456163972441)
                ·
                  refine ⟨10460430716823342122979331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13947240955764456163972441 10460430716823342122979331)
                  ·
                    refine ⟨15690646075235013184468997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10460430716823342122979331 15690646075235013184468997)
                    ·
                      refine ⟨2941996139106564972087937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15690646075235013184468997 2941996139106564972087937)
                      ·
                        rfl

theorem cell23_5729517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5729517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729517 prefixEnd_5729517 := by exact prefixLift 5729517
  have htrace : WordTrace (prefixWord ++ tailWord_5729517) baseStart_5729517 baseEnd_5729517 := by
    simpa [prefixWord, tailWord_5729517, baseEnd_5729517] using wordTrace_append hprefix tailTrace_5729517
  have hstable : (prefixWord ++ tailWord_5729517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729517).length < 2 ^ (prefixWord ++ tailWord_5729517).sum := by decide
  have hdescent : baseEnd_5729517 < baseStart_5729517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729527 : List Nat := [1, 1, 3, 1, 1, 1, 2, 8, 1, 4]
def baseStart_5729527 : Nat := 118140960795 + 5729527 * 2 ^ 59
def prefixEnd_5729527 : Nat := 4983230072969 + 3 ^ 40 * 5729527 * 2
def baseEnd_5729527 : Nat := 980667091304369977654297

theorem tailTrace_5729527 : CollatzResearch.WordTrace tailWord_5729527 prefixEnd_5729527 980667091304369977654297 := by
  unfold tailWord_5729527
  simp only [CollatzResearch.WordTrace]
  refine ⟨208973017513909679152330835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139315345009273119434887223 208973017513909679152330835)
  ·
    refine ⟨313459526270864518728496253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208973017513909679152330835 313459526270864518728496253)
    ·
      refine ⟨117547322351574194523186095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313459526270864518728496253 117547322351574194523186095)
      ·
        refine ⟨176320983527361291784779143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117547322351574194523186095 176320983527361291784779143)
        ·
          refine ⟨264481475291041937677168715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176320983527361291784779143 264481475291041937677168715)
          ·
            refine ⟨396722212936562906515753073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264481475291041937677168715 396722212936562906515753073)
            ·
              refine ⟨297541659702422179886814805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396722212936562906515753073 297541659702422179886814805)
              ·
                refine ⟨3486816324637759920548611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 297541659702422179886814805 3486816324637759920548611)
                ·
                  refine ⟨5230224486956639880822917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486816324637759920548611 5230224486956639880822917)
                  ·
                    refine ⟨980667091304369977654297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5230224486956639880822917 980667091304369977654297)
                    ·
                      rfl

theorem cell23_5729527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_5729527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729527 prefixEnd_5729527 := by exact prefixLift 5729527
  have htrace : WordTrace (prefixWord ++ tailWord_5729527) baseStart_5729527 baseEnd_5729527 := by
    simpa [prefixWord, tailWord_5729527, baseEnd_5729527] using wordTrace_append hprefix tailTrace_5729527
  have hstable : (prefixWord ++ tailWord_5729527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729527).length < 2 ^ (prefixWord ++ tailWord_5729527).sum := by decide
  have hdescent : baseEnd_5729527 < baseStart_5729527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729534 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_5729534 : Nat := 118140960795 + 5729534 * 2 ^ 59
def prefixEnd_5729534 : Nat := 4983230072969 + 3 ^ 40 * 5729534 * 2
def baseEnd_5729534 : Nat := 2942004868277691405575359

theorem tailTrace_5729534 : CollatzResearch.WordTrace tailWord_5729534 prefixEnd_5729534 2942004868277691405575359 := by
  unfold tailWord_5729534
  simp only [CollatzResearch.WordTrace]
  refine ⟨26121659103110539918479457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139315515216589546231890437 26121659103110539918479457)
  ·
    refine ⟨19591244327332904938859593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26121659103110539918479457 19591244327332904938859593)
    ·
      refine ⟨14693433245499678704144695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19591244327332904938859593 14693433245499678704144695)
      ·
        refine ⟨22040149868249518056217043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14693433245499678704144695 22040149868249518056217043)
        ·
          refine ⟨33060224802374277084325565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22040149868249518056217043 33060224802374277084325565)
          ·
            refine ⟨12397584300890353906622087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33060224802374277084325565 12397584300890353906622087)
            ·
              refine ⟨18596376451335530859933131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12397584300890353906622087 18596376451335530859933131)
              ·
                refine ⟨27894564677003296289899697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18596376451335530859933131 27894564677003296289899697)
                ·
                  refine ⟨20920923507752472217424773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27894564677003296289899697 20920923507752472217424773)
                  ·
                    refine ⟨3922673157703588540767145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20920923507752472217424773 3922673157703588540767145)
                    ·
                      refine ⟨2942004868277691405575359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922673157703588540767145 2942004868277691405575359)
                      ·
                        rfl

theorem cell23_5729534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_5729534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729534 prefixEnd_5729534 := by exact prefixLift 5729534
  have htrace : WordTrace (prefixWord ++ tailWord_5729534) baseStart_5729534 baseEnd_5729534 := by
    simpa [prefixWord, tailWord_5729534, baseEnd_5729534] using wordTrace_append hprefix tailTrace_5729534
  have hstable : (prefixWord ++ tailWord_5729534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729534).length < 2 ^ (prefixWord ++ tailWord_5729534).sum := by decide
  have hdescent : baseEnd_5729534 < baseStart_5729534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729563 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 5]
def baseStart_5729563 : Nat := 118140960795 + 5729563 * 2 ^ 59
def prefixEnd_5729563 : Nat := 4983230072969 + 3 ^ 40 * 5729563 * 2
def baseEnd_5729563 : Nat := 2942019759216671792112725

theorem tailTrace_5729563 : CollatzResearch.WordTrace tailWord_5729563 prefixEnd_5729563 2942019759216671792112725 := by
  unfold tailWord_5729563
  simp only [CollatzResearch.WordTrace]
  refine ⟨208974330541779257300641343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139316220361186171533760895 208974330541779257300641343)
  ·
    refine ⟨313461495812668885950962015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208974330541779257300641343 313461495812668885950962015)
    ·
      refine ⟨470192243719003328926443023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313461495812668885950962015 470192243719003328926443023)
      ·
        refine ⟨705288365578504993389664535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470192243719003328926443023 705288365578504993389664535)
        ·
          refine ⟨1057932548367757490084496803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705288365578504993389664535 1057932548367757490084496803)
          ·
            refine ⟨1586898822551636235126745205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057932548367757490084496803 1586898822551636235126745205)
            ·
              refine ⟨148771764614215897043132363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1586898822551636235126745205 148771764614215897043132363)
              ·
                refine ⟨223157646921323845564698545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148771764614215897043132363 223157646921323845564698545)
                ·
                  refine ⟨167368235190992884173523909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223157646921323845564698545 167368235190992884173523909)
                  ·
                    refine ⟨31381544098311165782535733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167368235190992884173523909 31381544098311165782535733)
                    ·
                      refine ⟨2942019759216671792112725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31381544098311165782535733 2942019759216671792112725)
                      ·
                        rfl

theorem cell23_5729563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_5729563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729563 prefixEnd_5729563 := by exact prefixLift 5729563
  have htrace : WordTrace (prefixWord ++ tailWord_5729563) baseStart_5729563 baseEnd_5729563 := by
    simpa [prefixWord, tailWord_5729563, baseEnd_5729563] using wordTrace_append hprefix tailTrace_5729563
  have hstable : (prefixWord ++ tailWord_5729563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729563).length < 2 ^ (prefixWord ++ tailWord_5729563).sum := by decide
  have hdescent : baseEnd_5729563 < baseStart_5729563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729584 : List Nat := [2, 1, 1, 1, 2, 2, 3, 6, 1, 1, 3]
def baseStart_5729584 : Nat := 118140960795 + 5729584 * 2 ^ 59
def prefixEnd_5729584 : Nat := 4983230072969 + 3 ^ 40 * 5729584 * 2
def baseEnd_5729584 : Nat := 2942030542310416209950129

theorem tailTrace_5729584 : CollatzResearch.WordTrace tailWord_5729584 prefixEnd_5729584 2942030542310416209950129 := by
  unfold tailWord_5729584
  simp only [CollatzResearch.WordTrace]
  refine ⟨104487548237351588943577903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139316730983135451924770537 104487548237351588943577903)
  ·
    refine ⟨156731322356027383415366855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104487548237351588943577903 156731322356027383415366855)
    ·
      refine ⟨235096983534041075123050283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156731322356027383415366855 235096983534041075123050283)
      ·
        refine ⟨352645475301061612684575425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235096983534041075123050283 352645475301061612684575425)
        ·
          refine ⟨264484106475796209513431569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352645475301061612684575425 264484106475796209513431569)
          ·
            refine ⟨198363079856847157135073677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264484106475796209513431569 198363079856847157135073677)
            ·
              refine ⟨74386154946317683925652629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198363079856847157135073677 74386154946317683925652629)
              ·
                refine ⟨3486851013108641434014967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74386154946317683925652629 3486851013108641434014967)
                ·
                  refine ⟨5230276519662962151022451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3486851013108641434014967 5230276519662962151022451)
                  ·
                    refine ⟨7845414779494443226533677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5230276519662962151022451 7845414779494443226533677)
                    ·
                      refine ⟨2942030542310416209950129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7845414779494443226533677 2942030542310416209950129)
                      ·
                        rfl

theorem cell23_5729584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 1, 1, 3].length) (baseStart_5729584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729584 prefixEnd_5729584 := by exact prefixLift 5729584
  have htrace : WordTrace (prefixWord ++ tailWord_5729584) baseStart_5729584 baseEnd_5729584 := by
    simpa [prefixWord, tailWord_5729584, baseEnd_5729584] using wordTrace_append hprefix tailTrace_5729584
  have hstable : (prefixWord ++ tailWord_5729584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729584).length < 2 ^ (prefixWord ++ tailWord_5729584).sum := by decide
  have hdescent : baseEnd_5729584 < baseStart_5729584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729604 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_5729604 : Nat := 118140960795 + 5729604 * 2 ^ 59
def prefixEnd_5729604 : Nat := 4983230072969 + 3 ^ 40 * 5729604 * 2
def baseEnd_5729604 : Nat := 980680270641168710566679

theorem tailTrace_5729604 : CollatzResearch.WordTrace tailWord_5729604 prefixEnd_5729604 980680270641168710566679 := by
  unfold tailWord_5729604
  simp only [CollatzResearch.WordTrace]
  refine ⟨104487912967315360651441933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139317217289753814201922577 104487912967315360651441933)
  ·
    refine ⟨39182967362743260244290725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104487912967315360651441933 39182967362743260244290725)
    ·
      refine ⟨7346806380514361295804511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39182967362743260244290725 7346806380514361295804511)
      ·
        refine ⟨11020209570771541943706767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7346806380514361295804511 11020209570771541943706767)
        ·
          refine ⟨16530314356157312915560151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11020209570771541943706767 16530314356157312915560151)
          ·
            refine ⟨24795471534235969373340227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16530314356157312915560151 24795471534235969373340227)
            ·
              refine ⟨37193207301353954060010341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24795471534235969373340227 37193207301353954060010341)
              ·
                refine ⟨6973726369003866386251939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37193207301353954060010341 6973726369003866386251939)
                ·
                  refine ⟨10460589553505799579377909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6973726369003866386251939 10460589553505799579377909)
                  ·
                    refine ⟨980680270641168710566679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10460589553505799579377909 980680270641168710566679)
                    ·
                      rfl

theorem cell23_5729604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_5729604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729604 prefixEnd_5729604 := by exact prefixLift 5729604
  have htrace : WordTrace (prefixWord ++ tailWord_5729604) baseStart_5729604 baseEnd_5729604 := by
    simpa [prefixWord, tailWord_5729604, baseEnd_5729604] using wordTrace_append hprefix tailTrace_5729604
  have hstable : (prefixWord ++ tailWord_5729604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729604).length < 2 ^ (prefixWord ++ tailWord_5729604).sum := by decide
  have hdescent : baseEnd_5729604 < baseStart_5729604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729607 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_5729607 : Nat := 118140960795 + 5729607 * 2 ^ 59
def prefixEnd_5729607 : Nat := 4983230072969 + 3 ^ 40 * 5729607 * 2
def baseEnd_5729607 : Nat := 2942042352365469619962523

theorem tailTrace_5729607 : CollatzResearch.WordTrace tailWord_5729607 prefixEnd_5729607 2942042352365469619962523 := by
  unfold tailWord_5729607
  simp only [CollatzResearch.WordTrace]
  refine ⟨208975935353619852815243075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139317290235746568543495383 208975935353619852815243075)
  ·
    refine ⟨313463903030429779222864613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208975935353619852815243075 313463903030429779222864613)
    ·
      refine ⟨58774481818205583604287115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313463903030429779222864613 58774481818205583604287115)
      ·
        refine ⟨88161722727308375406430673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58774481818205583604287115 88161722727308375406430673)
        ·
          refine ⟨66121292045481281554823005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88161722727308375406430673 66121292045481281554823005)
          ·
            refine ⟨24795484517055480583058627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66121292045481281554823005 24795484517055480583058627)
            ·
              refine ⟨37193226775583220874587941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24795484517055480583058627 37193226775583220874587941)
              ·
                refine ⟨6973730020421853913985239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37193226775583220874587941 6973730020421853913985239)
                ·
                  refine ⟨10460595030632780870977859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6973730020421853913985239 10460595030632780870977859)
                  ·
                    refine ⟨15690892545949171306466789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10460595030632780870977859 15690892545949171306466789)
                    ·
                      refine ⟨2942042352365469619962523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15690892545949171306466789 2942042352365469619962523)
                      ·
                        rfl

theorem cell23_5729607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_5729607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729607 prefixEnd_5729607 := by exact prefixLift 5729607
  have htrace : WordTrace (prefixWord ++ tailWord_5729607) baseStart_5729607 baseEnd_5729607 := by
    simpa [prefixWord, tailWord_5729607, baseEnd_5729607] using wordTrace_append hprefix tailTrace_5729607
  have hstable : (prefixWord ++ tailWord_5729607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729607).length < 2 ^ (prefixWord ++ tailWord_5729607).sum := by decide
  have hdescent : baseEnd_5729607 < baseStart_5729607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729610 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_5729610 : Nat := 118140960795 + 5729610 * 2 ^ 59
def prefixEnd_5729610 : Nat := 4983230072969 + 3 ^ 40 * 5729610 * 2
def baseEnd_5729610 : Nat := 2942043892807433108225009

theorem tailTrace_5729610 : CollatzResearch.WordTrace tailWord_5729610 prefixEnd_5729610 2942043892807433108225009 := by
  unfold tailWord_5729610
  simp only [CollatzResearch.WordTrace]
  refine ⟨52244011193152246081900571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139317363181739322885068189 52244011193152246081900571)
  ·
    refine ⟨78366016789728369122850857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52244011193152246081900571 78366016789728369122850857)
    ·
      refine ⟨58774512592296276842138143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78366016789728369122850857 58774512592296276842138143)
      ·
        refine ⟨88161768888444415263207215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58774512592296276842138143 88161768888444415263207215)
        ·
          refine ⟨132242653332666622894810823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88161768888444415263207215 132242653332666622894810823)
          ·
            refine ⟨198363979998999934342216235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132242653332666622894810823 198363979998999934342216235)
            ·
              refine ⟨297545969998499901513324353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198363979998999934342216235 297545969998499901513324353)
              ·
                refine ⟨223159477498874926134993265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297545969998499901513324353 223159477498874926134993265)
                ·
                  refine ⟨167369608124156194601244949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223159477498874926134993265 167369608124156194601244949)
                  ·
                    refine ⟨7845450380819821621933357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 167369608124156194601244949 7845450380819821621933357)
                    ·
                      refine ⟨2942043892807433108225009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7845450380819821621933357 2942043892807433108225009)
                      ·
                        rfl

theorem cell23_5729610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_5729610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729610 prefixEnd_5729610 := by exact prefixLift 5729610
  have htrace : WordTrace (prefixWord ++ tailWord_5729610) baseStart_5729610 baseEnd_5729610 := by
    simpa [prefixWord, tailWord_5729610, baseEnd_5729610] using wordTrace_append hprefix tailTrace_5729610
  have hstable : (prefixWord ++ tailWord_5729610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729610).length < 2 ^ (prefixWord ++ tailWord_5729610).sum := by decide
  have hdescent : baseEnd_5729610 < baseStart_5729610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729634 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_5729634 : Nat := 118140960795 + 5729634 * 2 ^ 59
def prefixEnd_5729634 : Nat := 4983230072969 + 3 ^ 40 * 5729634 * 2
def baseEnd_5729634 : Nat := 980685405447713671441633

theorem tailTrace_5729634 : CollatzResearch.WordTrace tailWord_5729634 prefixEnd_5729634 980685405447713671441633 := by
  unfold tailWord_5729634
  simp only [CollatzResearch.WordTrace]
  refine ⟨52244230031130509106618989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139317946749681357617650637 52244230031130509106618989)
  ·
    refine ⟨19591586261673940914982121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52244230031130509106618989 19591586261673940914982121)
    ·
      refine ⟨14693689696255455686236591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19591586261673940914982121 14693689696255455686236591)
      ·
        refine ⟨22040534544383183529354887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14693689696255455686236591 22040534544383183529354887)
        ·
          refine ⟨33060801816574775294032331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22040534544383183529354887 33060801816574775294032331)
          ·
            refine ⟨49591202724862162941048497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33060801816574775294032331 49591202724862162941048497)
            ·
              refine ⟨37193402043646622205786373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49591202724862162941048497 37193402043646622205786373)
              ·
                refine ⟨6973762883183741663584945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37193402043646622205786373 6973762883183741663584945)
                ·
                  refine ⟨5230322162387806247688709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6973762883183741663584945 5230322162387806247688709)
                  ·
                    refine ⟨980685405447713671441633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5230322162387806247688709 980685405447713671441633)
                    ·
                      rfl

theorem cell23_5729634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_5729634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729634 prefixEnd_5729634 := by exact prefixLift 5729634
  have htrace : WordTrace (prefixWord ++ tailWord_5729634) baseStart_5729634 baseEnd_5729634 := by
    simpa [prefixWord, tailWord_5729634, baseEnd_5729634] using wordTrace_append hprefix tailTrace_5729634
  have hstable : (prefixWord ++ tailWord_5729634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729634).length < 2 ^ (prefixWord ++ tailWord_5729634).sum := by decide
  have hdescent : baseEnd_5729634 < baseStart_5729634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729650 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_5729650 : Nat := 118140960795 + 5729650 * 2 ^ 59
def prefixEnd_5729650 : Nat := 4983230072969 + 3 ^ 40 * 5729650 * 2
def baseEnd_5729650 : Nat := 2942064432033612951724825

theorem tailTrace_5729650 : CollatzResearch.WordTrace tailWord_5729650 prefixEnd_5729650 2942064432033612951724825 := by
  unfold tailWord_5729650
  simp only [CollatzResearch.WordTrace]
  refine ⟨52244375923116017789764601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139318335794976047439372269 52244375923116017789764601)
  ·
    refine ⟨39183281942337013342323451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52244375923116017789764601 39183281942337013342323451)
    ·
      refine ⟨58774922913505520013485177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39183281942337013342323451 58774922913505520013485177)
      ·
        refine ⟨44081192185129140010113883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58774922913505520013485177 44081192185129140010113883)
        ·
          refine ⟨66121788277693710015170825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44081192185129140010113883 66121788277693710015170825)
          ·
            refine ⟨49591341208270282511378119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66121788277693710015170825 49591341208270282511378119)
            ·
              refine ⟨74387011812405423767067179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49591341208270282511378119 74387011812405423767067179)
              ·
                refine ⟨111580517718608135650600769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74387011812405423767067179 111580517718608135650600769)
                ·
                  refine ⟨83685388288956101737950577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111580517718608135650600769 83685388288956101737950577)
                  ·
                    refine ⟨62764041216717076303462933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83685388288956101737950577 62764041216717076303462933)
                    ·
                      refine ⟨2942064432033612951724825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62764041216717076303462933 2942064432033612951724825)
                      ·
                        rfl

theorem cell23_5729650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_5729650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729650 prefixEnd_5729650 := by exact prefixLift 5729650
  have htrace : WordTrace (prefixWord ++ tailWord_5729650) baseStart_5729650 baseEnd_5729650 := by
    simpa [prefixWord, tailWord_5729650, baseEnd_5729650] using wordTrace_append hprefix tailTrace_5729650
  have hstable : (prefixWord ++ tailWord_5729650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729650).length < 2 ^ (prefixWord ++ tailWord_5729650).sum := by decide
  have hdescent : baseEnd_5729650 < baseStart_5729650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729678 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3]
def baseStart_5729678 : Nat := 118140960795 + 5729678 * 2 ^ 59
def prefixEnd_5729678 : Nat := 4983230072969 + 3 ^ 40 * 5729678 * 2
def baseEnd_5729678 : Nat := 2942078809491938842174697

theorem tailTrace_5729678 : CollatzResearch.WordTrace tailWord_5729678 prefixEnd_5729678 2942078809491938842174697 := by
  unfold tailWord_5729678
  simp only [CollatzResearch.WordTrace]
  refine ⟨26122315617045328992634711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139319016624241754627385125 26122315617045328992634711)
  ·
    refine ⟨39183473425567993488952067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26122315617045328992634711 39183473425567993488952067)
    ·
      refine ⟨58775210138351990233428101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39183473425567993488952067 58775210138351990233428101)
      ·
        refine ⟨11020351900940998168767769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58775210138351990233428101 11020351900940998168767769)
        ·
          refine ⟨8265263925705748626575827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11020351900940998168767769 8265263925705748626575827)
          ·
            refine ⟨12397895888558622939863741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8265263925705748626575827 12397895888558622939863741)
            ·
              refine ⟨4649210958209483602448903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12397895888558622939863741 4649210958209483602448903)
              ·
                refine ⟨6973816437314225403673355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649210958209483602448903 6973816437314225403673355)
                ·
                  refine ⟨10460724655971338105510033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6973816437314225403673355 10460724655971338105510033)
                  ·
                    refine ⟨7845543491978503579132525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10460724655971338105510033 7845543491978503579132525)
                    ·
                      refine ⟨2942078809491938842174697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7845543491978503579132525 2942078809491938842174697)
                      ·
                        rfl

theorem cell23_5729678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_5729678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729678 prefixEnd_5729678 := by exact prefixLift 5729678
  have htrace : WordTrace (prefixWord ++ tailWord_5729678) baseStart_5729678 baseEnd_5729678 := by
    simpa [prefixWord, tailWord_5729678, baseEnd_5729678] using wordTrace_append hprefix tailTrace_5729678
  have hstable : (prefixWord ++ tailWord_5729678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729678).length < 2 ^ (prefixWord ++ tailWord_5729678).sum := by decide
  have hdescent : baseEnd_5729678 < baseStart_5729678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729720 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 9]
def baseStart_5729720 : Nat := 118140960795 + 5729720 * 2 ^ 59
def prefixEnd_5729720 : Nat := 4983230072969 + 3 ^ 40 * 5729720 * 2
def baseEnd_5729720 : Nat := 326900041742158630872167

theorem tailTrace_5729720 : CollatzResearch.WordTrace tailWord_5729720 prefixEnd_5729720 326900041742158630872167 := by
  unfold tailWord_5729720
  simp only [CollatzResearch.WordTrace]
  refine ⟨104490028401105236557053307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139320037868140315409404409 104490028401105236557053307)
  ·
    refine ⟨156735042601657854835579961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104490028401105236557053307 156735042601657854835579961)
    ·
      refine ⟨117551281951243391126684971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156735042601657854835579961 117551281951243391126684971)
      ·
        refine ⟨176326922926865086690027457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117551281951243391126684971 176326922926865086690027457)
        ·
          refine ⟨132245192195148815017520593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176326922926865086690027457 132245192195148815017520593)
          ·
            refine ⟨99183894146361611263140445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132245192195148815017520593 99183894146361611263140445)
            ·
              refine ⟨37193960304885604223677667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99183894146361611263140445 37193960304885604223677667)
              ·
                refine ⟨55790940457328406335516501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37193960304885604223677667 55790940457328406335516501)
                ·
                  refine ⟨326900041742158630872167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55790940457328406335516501 326900041742158630872167)
                  ·
                    rfl

theorem cell23_5729720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 9].length) (baseStart_5729720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729720 prefixEnd_5729720 := by exact prefixLift 5729720
  have htrace : WordTrace (prefixWord ++ tailWord_5729720) baseStart_5729720 baseEnd_5729720 := by
    simpa [prefixWord, tailWord_5729720, baseEnd_5729720] using wordTrace_append hprefix tailTrace_5729720
  have hstable : (prefixWord ++ tailWord_5729720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729720).length < 2 ^ (prefixWord ++ tailWord_5729720).sum := by decide
  have hdescent : baseEnd_5729720 < baseStart_5729720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729748 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_5729748 : Nat := 118140960795 + 5729748 * 2 ^ 59
def prefixEnd_5729748 : Nat := 4983230072969 + 3 ^ 40 * 5729748 * 2
def baseEnd_5729748 : Nat := 2942114753137753568299375

theorem tailTrace_5729748 : CollatzResearch.WordTrace tailWord_5729748 prefixEnd_5729748 2942114753137753568299375 := by
  unfold tailWord_5729748
  simp only [CollatzResearch.WordTrace]
  refine ⟨104490539023054516948062949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139320718697406022597417265 104490539023054516948062949)
  ·
    refine ⟨19591976066822721927761803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104490539023054516948062949 19591976066822721927761803)
    ·
      refine ⟨29387964100234082891642705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19591976066822721927761803 29387964100234082891642705)
      ·
        refine ⟨22040973075175562168732029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29387964100234082891642705 22040973075175562168732029)
        ·
          refine ⟨8265364903190835813274511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22040973075175562168732029 8265364903190835813274511)
          ·
            refine ⟨12398047354786253719911767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8265364903190835813274511 12398047354786253719911767)
            ·
              refine ⟨18597071032179380579867651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12398047354786253719911767 18597071032179380579867651)
              ·
                refine ⟨27895606548269070869801477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18597071032179380579867651 27895606548269070869801477)
                ·
                  refine ⟨5230426227800450788087777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27895606548269070869801477 5230426227800450788087777)
                  ·
                    refine ⟨3922819670850338091065833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5230426227800450788087777 3922819670850338091065833)
                    ·
                      refine ⟨2942114753137753568299375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922819670850338091065833 2942114753137753568299375)
                      ·
                        rfl

theorem cell23_5729748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_5729748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729748 prefixEnd_5729748 := by exact prefixLift 5729748
  have htrace : WordTrace (prefixWord ++ tailWord_5729748) baseStart_5729748 baseEnd_5729748 := by
    simpa [prefixWord, tailWord_5729748, baseEnd_5729748] using wordTrace_append hprefix tailTrace_5729748
  have hstable : (prefixWord ++ tailWord_5729748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729748).length < 2 ^ (prefixWord ++ tailWord_5729748).sum := by decide
  have hdescent : baseEnd_5729748 < baseStart_5729748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729754 : List Nat := [3, 1, 1, 2, 3, 2, 2, 4, 5]
def baseStart_5729754 : Nat := 118140960795 + 5729754 * 2 ^ 59
def prefixEnd_5729754 : Nat := 4983230072969 + 3 ^ 40 * 5729754 * 2
def baseEnd_5729754 : Nat := 326901981557964504980483

theorem tailTrace_5729754 : CollatzResearch.WordTrace tailWord_5729754 prefixEnd_5729754 326901981557964504980483 := by
  unfold tailWord_5729754
  simp only [CollatzResearch.WordTrace]
  refine ⟨52245324221021824230211079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139320864589391531280562877 52245324221021824230211079)
  ·
    refine ⟨78367986331532736345316619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52245324221021824230211079 78367986331532736345316619)
    ·
      refine ⟨117551979497299104517974929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78367986331532736345316619 117551979497299104517974929)
      ·
        refine ⟨88163984622974328388481197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117551979497299104517974929 88163984622974328388481197)
        ·
          refine ⟨33061494233615373145680449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88163984622974328388481197 33061494233615373145680449)
          ·
            refine ⟨24796120675211529859260337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33061494233615373145680449 24796120675211529859260337)
            ·
              refine ⟨18597090506408647394445253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24796120675211529859260337 18597090506408647394445253)
              ·
                refine ⟨3486954469951621386458485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18597090506408647394445253 3486954469951621386458485)
                ·
                  refine ⟨326901981557964504980483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3486954469951621386458485 326901981557964504980483)
                  ·
                    rfl

theorem cell23_5729754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_5729754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729754 prefixEnd_5729754 := by exact prefixLift 5729754
  have htrace : WordTrace (prefixWord ++ tailWord_5729754) baseStart_5729754 baseEnd_5729754 := by
    simpa [prefixWord, tailWord_5729754, baseEnd_5729754] using wordTrace_append hprefix tailTrace_5729754
  have hstable : (prefixWord ++ tailWord_5729754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729754).length < 2 ^ (prefixWord ++ tailWord_5729754).sum := by decide
  have hdescent : baseEnd_5729754 < baseStart_5729754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729765 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 2, 2, 2]
def baseStart_5729765 : Nat := 118140960795 + 5729765 * 2 ^ 59
def prefixEnd_5729765 : Nat := 4983230072969 + 3 ^ 40 * 5729765 * 2
def baseEnd_5729765 : Nat := 2942123482308880001786797

theorem tailTrace_5729765 : CollatzResearch.WordTrace tailWord_5729765 prefixEnd_5729765 2942123482308880001786797 := by
  unfold tailWord_5729765
  simp only [CollatzResearch.WordTrace]
  refine ⟨208981698087047445799494749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139321132058031630532996499 208981698087047445799494749)
  ·
    refine ⟨78368136782642792174810531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208981698087047445799494749 78368136782642792174810531)
    ·
      refine ⟨117552205173964188262215797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78368136782642792174810531 117552205173964188262215797)
      ·
        refine ⟨11020519235059142649582731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117552205173964188262215797 11020519235059142649582731)
        ·
          refine ⟨16530778852588713974374097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11020519235059142649582731 16530778852588713974374097)
          ·
            refine ⟨12398084139441535480780573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16530778852588713974374097 12398084139441535480780573)
            ·
              refine ⟨4649281552290575805292715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12398084139441535480780573 4649281552290575805292715)
              ·
                refine ⟨6973922328435863707939073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649281552290575805292715 6973922328435863707939073)
                ·
                  refine ⟨5230441746326897780954305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6973922328435863707939073 5230441746326897780954305)
                  ·
                    refine ⟨3922831309745173335715729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5230441746326897780954305 3922831309745173335715729)
                    ·
                      refine ⟨2942123482308880001786797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922831309745173335715729 2942123482308880001786797)
                      ·
                        rfl

theorem cell23_5729765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_5729765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729765 prefixEnd_5729765 := by exact prefixLift 5729765
  have htrace : WordTrace (prefixWord ++ tailWord_5729765) baseStart_5729765 baseEnd_5729765 := by
    simpa [prefixWord, tailWord_5729765, baseEnd_5729765] using wordTrace_append hprefix tailTrace_5729765
  have hstable : (prefixWord ++ tailWord_5729765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729765).length < 2 ^ (prefixWord ++ tailWord_5729765).sum := by decide
  have hdescent : baseEnd_5729765 < baseStart_5729765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729767 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 1, 7]
def baseStart_5729767 : Nat := 118140960795 + 5729767 * 2 ^ 59
def prefixEnd_5729767 : Nat := 4983230072969 + 3 ^ 40 * 5729767 * 2
def baseEnd_5729767 : Nat := 980708169756729664653929

theorem tailTrace_5729767 : CollatzResearch.WordTrace tailWord_5729767 prefixEnd_5729767 980708169756729664653929 := by
  unfold tailWord_5729767
  simp only [CollatzResearch.WordTrace]
  refine ⟨208981771033040200141067555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139321180688693466760711703 208981771033040200141067555)
  ·
    refine ⟨313472656549560300211601333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208981771033040200141067555 313472656549560300211601333)
    ·
      refine ⟨29388061551521278144837625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 313472656549560300211601333 29388061551521278144837625)
      ·
        refine ⟨22041046163640958608628219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29388061551521278144837625 22041046163640958608628219)
        ·
          refine ⟨33061569245461437912942329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22041046163640958608628219 33061569245461437912942329)
          ·
            refine ⟨24796176934096078434706747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33061569245461437912942329 24796176934096078434706747)
            ·
              refine ⟨37194265401144117652060121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24796176934096078434706747 37194265401144117652060121)
              ·
                refine ⟨27895699050858088239045091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37194265401144117652060121 27895699050858088239045091)
                ·
                  refine ⟨41843548576287132358567637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27895699050858088239045091 41843548576287132358567637)
                  ·
                    refine ⟨980708169756729664653929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41843548576287132358567637 980708169756729664653929)
                    ·
                      rfl

theorem cell23_5729767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_5729767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729767 prefixEnd_5729767 := by exact prefixLift 5729767
  have htrace : WordTrace (prefixWord ++ tailWord_5729767) baseStart_5729767 baseEnd_5729767 := by
    simpa [prefixWord, tailWord_5729767, baseEnd_5729767] using wordTrace_append hprefix tailTrace_5729767
  have hstable : (prefixWord ++ tailWord_5729767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729767).length < 2 ^ (prefixWord ++ tailWord_5729767).sum := by decide
  have hdescent : baseEnd_5729767 < baseStart_5729767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729805 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 7]
def baseStart_5729805 : Nat := 118140960795 + 5729805 * 2 ^ 59
def prefixEnd_5729805 : Nat := 4983230072969 + 3 ^ 40 * 5729805 * 2
def baseEnd_5729805 : Nat := 326904891281673316142957

theorem tailTrace_5729805 : CollatzResearch.WordTrace tailWord_5729805 prefixEnd_5729805 326904891281673316142957 := by
  unfold tailWord_5729805
  simp only [CollatzResearch.WordTrace]
  refine ⟨208983157006902532630950869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139322104671268355087300579 208983157006902532630950869)
  ·
    refine ⟨4898042742349278108537911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 208983157006902532630950869 4898042742349278108537911)
    ·
      refine ⟨7347064113523917162806867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4898042742349278108537911 7347064113523917162806867)
      ·
        refine ⟨11020596170285875744210301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7347064113523917162806867 11020596170285875744210301)
        ·
          refine ⟨4132723563857203404078863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11020596170285875744210301 4132723563857203404078863)
          ·
            refine ⟨6199085345785805106118295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4132723563857203404078863 6199085345785805106118295)
            ·
              refine ⟨9298628018678707659177443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6199085345785805106118295 9298628018678707659177443)
              ·
                refine ⟨13947942028018061488766165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9298628018678707659177443 13947942028018061488766165)
                ·
                  refine ⟨326904891281673316142957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13947942028018061488766165 326904891281673316142957)
                  ·
                    rfl

theorem cell23_5729805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_5729805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729805 prefixEnd_5729805 := by exact prefixLift 5729805
  have htrace : WordTrace (prefixWord ++ tailWord_5729805) baseStart_5729805 baseEnd_5729805 := by
    simpa [prefixWord, tailWord_5729805, baseEnd_5729805] using wordTrace_append hprefix tailTrace_5729805
  have hstable : (prefixWord ++ tailWord_5729805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729805).length < 2 ^ (prefixWord ++ tailWord_5729805).sum := by decide
  have hdescent : baseEnd_5729805 < baseStart_5729805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729864 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 5, 5, 2]
def baseStart_5729864 : Nat := 118140960795 + 5729864 * 2 ^ 59
def prefixEnd_5729864 : Nat := 4983230072969 + 3 ^ 40 * 5729864 * 2
def baseEnd_5729864 : Nat := 2942174316893675114448841

theorem tailTrace_5729864 : CollatzResearch.WordTrace tailWord_5729864 prefixEnd_5729864 2942174316893675114448841 := by
  unfold tailWord_5729864
  simp only [CollatzResearch.WordTrace]
  refine ⟨104492654456844392853674323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139323539275792523804899097 104492654456844392853674323)
  ·
    refine ⟨156738981685266589280511485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104492654456844392853674323 156738981685266589280511485)
    ·
      refine ⟨58777118131974970980191807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156738981685266589280511485 58777118131974970980191807)
      ·
        refine ⟨88165677197962456470287711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58777118131974970980191807 88165677197962456470287711)
        ·
          refine ⟨132248515796943684705431567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88165677197962456470287711 132248515796943684705431567)
          ·
            refine ⟨198372773695415527058147351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132248515796943684705431567 198372773695415527058147351)
            ·
              refine ⟨297559160543123290587221027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198372773695415527058147351 297559160543123290587221027)
              ·
                refine ⟨446338740814684935880831541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297559160543123290587221027 446338740814684935880831541)
                ·
                  refine ⟨41844256951376712738827957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 446338740814684935880831541 41844256951376712738827957)
                  ·
                    refine ⟨3922899089191566819265121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41844256951376712738827957 3922899089191566819265121)
                    ·
                      refine ⟨2942174316893675114448841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922899089191566819265121 2942174316893675114448841)
                      ·
                        rfl

theorem cell23_5729864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_5729864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729864 prefixEnd_5729864 := by exact prefixLift 5729864
  have htrace : WordTrace (prefixWord ++ tailWord_5729864) baseStart_5729864 baseEnd_5729864 := by
    simpa [prefixWord, tailWord_5729864, baseEnd_5729864] using wordTrace_append hprefix tailTrace_5729864
  have hstable : (prefixWord ++ tailWord_5729864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729864).length < 2 ^ (prefixWord ++ tailWord_5729864).sum := by decide
  have hdescent : baseEnd_5729864 < baseStart_5729864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729874 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_5729874 : Nat := 118140960795 + 5729874 * 2 ^ 59
def prefixEnd_5729874 : Nat := 4983230072969 + 3 ^ 40 * 5729874 * 2
def baseEnd_5729874 : Nat := 980726483900073358441265

theorem tailTrace_5729874 : CollatzResearch.WordTrace tailWord_5729874 prefixEnd_5729874 980726483900073358441265 := by
  unfold tailWord_5729874
  simp only [CollatzResearch.WordTrace]
  refine ⟨52246418410913139353803169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139323782429101704943475117 52246418410913139353803169)
  ·
    refine ⟨39184813808184854515352377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52246418410913139353803169 39184813808184854515352377)
    ·
      refine ⟨29388610356138640886514283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39184813808184854515352377 29388610356138640886514283)
      ·
        refine ⟨44082915534207961329771425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29388610356138640886514283 44082915534207961329771425)
        ·
          refine ⟨33062186650655970997328569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44082915534207961329771425 33062186650655970997328569)
          ·
            refine ⟨24796639987991978247996427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33062186650655970997328569 24796639987991978247996427)
            ·
              refine ⟨37194959981987967371994641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24796639987991978247996427 37194959981987967371994641)
              ·
                refine ⟨27896219986490975528995981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37194959981987967371994641 27896219986490975528995981)
                ·
                  refine ⟨10461082494934115823373493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27896219986490975528995981 10461082494934115823373493)
                  ·
                    refine ⟨980726483900073358441265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10461082494934115823373493 980726483900073358441265)
                    ·
                      rfl

theorem cell23_5729874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_5729874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729874 prefixEnd_5729874 := by exact prefixLift 5729874
  have htrace : WordTrace (prefixWord ++ tailWord_5729874) baseStart_5729874 baseEnd_5729874 := by
    simpa [prefixWord, tailWord_5729874, baseEnd_5729874] using wordTrace_append hprefix tailTrace_5729874
  have hstable : (prefixWord ++ tailWord_5729874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729874).length < 2 ^ (prefixWord ++ tailWord_5729874).sum := by decide
  have hdescent : baseEnd_5729874 < baseStart_5729874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729898 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_5729898 : Nat := 118140960795 + 5729898 * 2 ^ 59
def prefixEnd_5729898 : Nat := 4983230072969 + 3 ^ 40 * 5729898 * 2
def baseEnd_5729898 : Nat := 2942191775235927981423685

theorem tailTrace_5729898 : CollatzResearch.WordTrace tailWord_5729898 prefixEnd_5729898 2942191775235927981423685 := by
  unfold tailWord_5729898
  simp only [CollatzResearch.WordTrace]
  refine ⟨52246637248891402378521587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139324365997043739676057565 52246637248891402378521587)
  ·
    refine ⟨78369955873337103567782381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52246637248891402378521587 78369955873337103567782381)
    ·
      refine ⟨29388733452501413837918393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78369955873337103567782381 29388733452501413837918393)
      ·
        refine ⟨22041550089376060378438795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29388733452501413837918393 22041550089376060378438795)
        ·
          refine ⟨33062325134064090567658193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22041550089376060378438795 33062325134064090567658193)
          ·
            refine ⟨24796743850548067925743645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33062325134064090567658193 24796743850548067925743645)
            ·
              refine ⟨9298778943955525472153867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24796743850548067925743645 9298778943955525472153867)
              ·
                refine ⟨13948168415933288208230801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9298778943955525472153867 13948168415933288208230801)
                ·
                  refine ⟨10461126311949966156173101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13948168415933288208230801 10461126311949966156173101)
                  ·
                    refine ⟨3922922366981237308564913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10461126311949966156173101 3922922366981237308564913)
                    ·
                      refine ⟨2942191775235927981423685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922922366981237308564913 2942191775235927981423685)
                      ·
                        rfl

theorem cell23_5729898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_5729898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729898 prefixEnd_5729898 := by exact prefixLift 5729898
  have htrace : WordTrace (prefixWord ++ tailWord_5729898) baseStart_5729898 baseEnd_5729898 := by
    simpa [prefixWord, tailWord_5729898, baseEnd_5729898] using wordTrace_append hprefix tailTrace_5729898
  have hstable : (prefixWord ++ tailWord_5729898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729898).length < 2 ^ (prefixWord ++ tailWord_5729898).sum := by decide
  have hdescent : baseEnd_5729898 < baseStart_5729898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729904 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 1, 6]
def baseStart_5729904 : Nat := 118140960795 + 5729904 * 2 ^ 59
def prefixEnd_5729904 : Nat := 4983230072969 + 3 ^ 40 * 5729904 * 2
def baseEnd_5729904 : Nat := 980731618706618319316219

theorem tailTrace_5729904 : CollatzResearch.WordTrace tailWord_5729904 prefixEnd_5729904 980731618706618319316219 := by
  unfold tailWord_5729904
  simp only [CollatzResearch.WordTrace]
  refine ⟨104493383916771936269402383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139324511889029248359203177 104493383916771936269402383)
  ·
    refine ⟨156740075875157904404103575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104493383916771936269402383 156740075875157904404103575)
    ·
      refine ⟨235110113812736856606155363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156740075875157904404103575 235110113812736856606155363)
      ·
        refine ⟨352665170719105284909233045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235110113812736856606155363 352665170719105284909233045)
        ·
          refine ⟨16531179877458060230120299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 352665170719105284909233045 16531179877458060230120299)
          ·
            refine ⟨24796769816187090345180449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16531179877458060230120299 24796769816187090345180449)
            ·
              refine ⟨18597577362140317758885337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24796769816187090345180449 18597577362140317758885337)
              ·
                refine ⟨13948183021605238319164003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18597577362140317758885337 13948183021605238319164003)
                ·
                  refine ⟨20922274532407857478746005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13948183021605238319164003 20922274532407857478746005)
                  ·
                    refine ⟨980731618706618319316219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20922274532407857478746005 980731618706618319316219)
                    ·
                      rfl

theorem cell23_5729904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_5729904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729904 prefixEnd_5729904 := by exact prefixLift 5729904
  have htrace : WordTrace (prefixWord ++ tailWord_5729904) baseStart_5729904 baseEnd_5729904 := by
    simpa [prefixWord, tailWord_5729904, baseEnd_5729904] using wordTrace_append hprefix tailTrace_5729904
  have hstable : (prefixWord ++ tailWord_5729904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729904).length < 2 ^ (prefixWord ++ tailWord_5729904).sum := by decide
  have hdescent : baseEnd_5729904 < baseStart_5729904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729907 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 4]
def baseStart_5729907 : Nat := 118140960795 + 5729907 * 2 ^ 59
def prefixEnd_5729907 : Nat := 4983230072969 + 3 ^ 40 * 5729907 * 2
def baseEnd_5729907 : Nat := 2942196396561818446211143

theorem tailTrace_5729907 : CollatzResearch.WordTrace tailWord_5729907 prefixEnd_5729907 2942196396561818446211143 := by
  unfold tailWord_5729907
  simp only [CollatzResearch.WordTrace]
  refine ⟨208986877252533004051163975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139324584835022002700775983 208986877252533004051163975)
  ·
    refine ⟨313480315878799506076745963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208986877252533004051163975 313480315878799506076745963)
    ·
      refine ⟨470220473818199259115118945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313480315878799506076745963 470220473818199259115118945)
      ·
        refine ⟨352665355363649444336339209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470220473818199259115118945 352665355363649444336339209)
        ·
          refine ⟨264499016522737083252254407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352665355363649444336339209 264499016522737083252254407)
          ·
            refine ⟨396748524784105624878381611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264499016522737083252254407 396748524784105624878381611)
            ·
              refine ⟨595122787176158437317572417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396748524784105624878381611 595122787176158437317572417)
              ·
                refine ⟨446342090382118827988179313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595122787176158437317572417 446342090382118827988179313)
                ·
                  refine ⟨334756567786589120991134485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446342090382118827988179313 334756567786589120991134485)
                  ·
                    refine ⟨15691714114996365046459429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 334756567786589120991134485 15691714114996365046459429)
                    ·
                      refine ⟨2942196396561818446211143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15691714114996365046459429 2942196396561818446211143)
                      ·
                        rfl

theorem cell23_5729907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_5729907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729907 prefixEnd_5729907 := by exact prefixLift 5729907
  have htrace : WordTrace (prefixWord ++ tailWord_5729907) baseStart_5729907 baseEnd_5729907 := by
    simpa [prefixWord, tailWord_5729907, baseEnd_5729907] using wordTrace_append hprefix tailTrace_5729907
  have hstable : (prefixWord ++ tailWord_5729907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729907).length < 2 ^ (prefixWord ++ tailWord_5729907).sum := by decide
  have hdescent : baseEnd_5729907 < baseStart_5729907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729911 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 7, 2, 2]
def baseStart_5729911 : Nat := 118140960795 + 5729911 * 2 ^ 59
def prefixEnd_5729911 : Nat := 4983230072969 + 3 ^ 40 * 5729911 * 2
def baseEnd_5729911 : Nat := 2942198450484436430561125

theorem tailTrace_5729911 : CollatzResearch.WordTrace tailWord_5729911 prefixEnd_5729911 2942198450484436430561125 := by
  unfold tailWord_5729911
  simp only [CollatzResearch.WordTrace]
  refine ⟨208987023144518512734309587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139324682096345675156206391 208987023144518512734309587)
  ·
    refine ⟨313480534716777769101464381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208987023144518512734309587 313480534716777769101464381)
    ·
      refine ⟨117555200518791663413049143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313480534716777769101464381 117555200518791663413049143)
      ·
        refine ⟨176332800778187495119573715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117555200518791663413049143 176332800778187495119573715)
        ·
          refine ⟨264499201167281242679360573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176332800778187495119573715 264499201167281242679360573)
          ·
            refine ⟨99187200437730466004760215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264499201167281242679360573 99187200437730466004760215)
            ·
              refine ⟨148780800656595699007140323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99187200437730466004760215 148780800656595699007140323)
              ·
                refine ⟨223171200984893548510710485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148780800656595699007140323 223171200984893548510710485)
                ·
                  refine ⟨5230575023083442543219777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 223171200984893548510710485 5230575023083442543219777)
                  ·
                    refine ⟨3922931267312581907414833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5230575023083442543219777 3922931267312581907414833)
                    ·
                      refine ⟨2942198450484436430561125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922931267312581907414833 2942198450484436430561125)
                      ·
                        rfl

theorem cell23_5729911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 2, 2].length) (baseStart_5729911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729911 prefixEnd_5729911 := by exact prefixLift 5729911
  have htrace : WordTrace (prefixWord ++ tailWord_5729911) baseStart_5729911 baseEnd_5729911 := by
    simpa [prefixWord, tailWord_5729911, baseEnd_5729911] using wordTrace_append hprefix tailTrace_5729911
  have hstable : (prefixWord ++ tailWord_5729911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729911).length < 2 ^ (prefixWord ++ tailWord_5729911).sum := by decide
  have hdescent : baseEnd_5729911 < baseStart_5729911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729914 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3]
def baseStart_5729914 : Nat := 118140960795 + 5729914 * 2 ^ 59
def prefixEnd_5729914 : Nat := 4983230072969 + 3 ^ 40 * 5729914 * 2
def baseEnd_5729914 : Nat := 2942199990926399918823611

theorem tailTrace_5729914 : CollatzResearch.WordTrace tailWord_5729914 prefixEnd_5729914 2942199990926399918823611 := by
  unfold tailWord_5729914
  simp only [CollatzResearch.WordTrace]
  refine ⟨52246783140876911061667199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139324755042338429497779197 52246783140876911061667199)
  ·
    refine ⟨78370174711315366592500799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52246783140876911061667199 78370174711315366592500799)
    ·
      refine ⟨117555262066973049888751199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78370174711315366592500799 117555262066973049888751199)
      ·
        refine ⟨176332893100459574833126799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117555262066973049888751199 176332893100459574833126799)
        ·
          refine ⟨264499339650689362249690199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176332893100459574833126799 264499339650689362249690199)
          ·
            refine ⟨396749009476034043374535299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264499339650689362249690199 396749009476034043374535299)
            ·
              refine ⟨595123514214051065061802949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396749009476034043374535299 595123514214051065061802949)
              ·
                refine ⟨111585658915134574699088053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 595123514214051065061802949 111585658915134574699088053)
                ·
                  refine ⟨10461155523293866378039505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111585658915134574699088053 10461155523293866378039505)
                  ·
                    refine ⟨7845866642470399783529629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10461155523293866378039505 7845866642470399783529629)
                    ·
                      refine ⟨2942199990926399918823611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7845866642470399783529629 2942199990926399918823611)
                      ·
                        rfl

theorem cell23_5729914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_5729914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729914 prefixEnd_5729914 := by exact prefixLift 5729914
  have htrace : WordTrace (prefixWord ++ tailWord_5729914) baseStart_5729914 baseEnd_5729914 := by
    simpa [prefixWord, tailWord_5729914, baseEnd_5729914] using wordTrace_append hprefix tailTrace_5729914
  have hstable : (prefixWord ++ tailWord_5729914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729914).length < 2 ^ (prefixWord ++ tailWord_5729914).sum := by decide
  have hdescent : baseEnd_5729914 < baseStart_5729914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729921 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 4, 4]
def baseStart_5729921 : Nat := 118140960795 + 5729921 * 2 ^ 59
def prefixEnd_5729921 : Nat := 4983230072969 + 3 ^ 40 * 5729921 * 2
def baseEnd_5729921 : Nat := 980734528430327130478693

theorem tailTrace_5729921 : CollatzResearch.WordTrace tailWord_5729921 prefixEnd_5729921 980734528430327130478693 := by
  unfold tailWord_5729921
  simp only [CollatzResearch.WordTrace]
  refine ⟨208987387874482284442173617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139324925249654856294782411 208987387874482284442173617)
  ·
    refine ⟨156740540905861713331630213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208987387874482284442173617 156740540905861713331630213)
    ·
      refine ⟨29388851419849071249680665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156740540905861713331630213 29388851419849071249680665)
      ·
        refine ⟨22041638564886803437260499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29388851419849071249680665 22041638564886803437260499)
        ·
          refine ⟨33062457847330205155890749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22041638564886803437260499 33062457847330205155890749)
          ·
            refine ⟨12398421692748826933459031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33062457847330205155890749 12398421692748826933459031)
            ·
              refine ⟨18597632539123240400188547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12398421692748826933459031 18597632539123240400188547)
              ·
                refine ⟨27896448808684860600282821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18597632539123240400188547 27896448808684860600282821)
                ·
                  refine ⟨5230584151628411362553029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27896448808684860600282821 5230584151628411362553029)
                  ·
                    refine ⟨980734528430327130478693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5230584151628411362553029 980734528430327130478693)
                    ·
                      rfl

theorem cell23_5729921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_5729921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729921 prefixEnd_5729921 := by exact prefixLift 5729921
  have htrace : WordTrace (prefixWord ++ tailWord_5729921) baseStart_5729921 baseEnd_5729921 := by
    simpa [prefixWord, tailWord_5729921, baseEnd_5729921] using wordTrace_append hprefix tailTrace_5729921
  have hstable : (prefixWord ++ tailWord_5729921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729921).length < 2 ^ (prefixWord ++ tailWord_5729921).sum := by decide
  have hdescent : baseEnd_5729921 < baseStart_5729921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729937 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_5729937 : Nat := 118140960795 + 5729937 * 2 ^ 59
def prefixEnd_5729937 : Nat := 4983230072969 + 3 ^ 40 * 5729937 * 2
def baseEnd_5729937 : Nat := 2942211800981453328836005

theorem tailTrace_5729937 : CollatzResearch.WordTrace tailWord_5729937 prefixEnd_5729937 2942211800981453328836005 := by
  unfold tailWord_5729937
  simp only [CollatzResearch.WordTrace]
  refine ⟨208987971442424319174756065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139325314294949546116504043 208987971442424319174756065)
  ·
    refine ⟨156740978581818239381067049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208987971442424319174756065 156740978581818239381067049)
    ·
      refine ⟨117555733936363679535800287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156740978581818239381067049 117555733936363679535800287)
      ·
        refine ⟨176333600904545519303700431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117555733936363679535800287 176333600904545519303700431)
        ·
          refine ⟨264500401356818278955550647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176333600904545519303700431 264500401356818278955550647)
          ·
            refine ⟨396750602035227418433325971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264500401356818278955550647 396750602035227418433325971)
            ·
              refine ⟨595125903052841127649988957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396750602035227418433325971 595125903052841127649988957)
              ·
                refine ⟨223172213644815422868745859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 595125903052841127649988957 223172213644815422868745859)
                ·
                  refine ⟨334758320467223134303118789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223172213644815422868745859 334758320467223134303118789)
                  ·
                    refine ⟨62767185087604337681834773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 334758320467223134303118789 62767185087604337681834773)
                    ·
                      refine ⟨2942211800981453328836005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62767185087604337681834773 2942211800981453328836005)
                      ·
                        rfl

theorem cell23_5729937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_5729937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729937 prefixEnd_5729937 := by exact prefixLift 5729937
  have htrace : WordTrace (prefixWord ++ tailWord_5729937) baseStart_5729937 baseEnd_5729937 := by
    simpa [prefixWord, tailWord_5729937, baseEnd_5729937] using wordTrace_append hprefix tailTrace_5729937
  have hstable : (prefixWord ++ tailWord_5729937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729937).length < 2 ^ (prefixWord ++ tailWord_5729937).sum := by decide
  have hdescent : baseEnd_5729937 < baseStart_5729937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729938 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_5729938 : Nat := 118140960795 + 5729938 * 2 ^ 59
def prefixEnd_5729938 : Nat := 4983230072969 + 3 ^ 40 * 5729938 * 2
def baseEnd_5729938 : Nat := 980737438154035941641167

theorem tailTrace_5729938 : CollatzResearch.WordTrace tailWord_5729938 prefixEnd_5729938 980737438154035941641167 := by
  unfold tailWord_5729938
  simp only [CollatzResearch.WordTrace]
  refine ⟨52247001978855174086385617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139325338610280464230361645 52247001978855174086385617)
  ·
    refine ⟨39185251484141380564789213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52247001978855174086385617 39185251484141380564789213)
    ·
      refine ⟨14694469306553017711795955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39185251484141380564789213 14694469306553017711795955)
      ·
        refine ⟨22041703959829526567693933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14694469306553017711795955 22041703959829526567693933)
        ·
          refine ⟨8265638984936072462885225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22041703959829526567693933 8265638984936072462885225)
          ·
            refine ⟨6199229238702054347163919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8265638984936072462885225 6199229238702054347163919)
            ·
              refine ⟨9298843858053081520745879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6199229238702054347163919 9298843858053081520745879)
              ·
                refine ⟨13948265787079622281118819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9298843858053081520745879 13948265787079622281118819)
                ·
                  refine ⟨20922398680619433421678229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13948265787079622281118819 20922398680619433421678229)
                  ·
                    refine ⟨980737438154035941641167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20922398680619433421678229 980737438154035941641167)
                    ·
                      rfl

theorem cell23_5729938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_5729938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729938 prefixEnd_5729938 := by exact prefixLift 5729938
  have htrace : WordTrace (prefixWord ++ tailWord_5729938) baseStart_5729938 baseEnd_5729938 := by
    simpa [prefixWord, tailWord_5729938, baseEnd_5729938] using wordTrace_append hprefix tailTrace_5729938
  have hstable : (prefixWord ++ tailWord_5729938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729938).length < 2 ^ (prefixWord ++ tailWord_5729938).sum := by decide
  have hdescent : baseEnd_5729938 < baseStart_5729938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729951 : List Nat := [1, 1, 2, 7, 1, 1, 1, 9]
def baseStart_5729951 : Nat := 118140960795 + 5729951 * 2 ^ 59
def prefixEnd_5729951 : Nat := 4983230072969 + 3 ^ 40 * 5729951 * 2
def baseEnd_5729951 : Nat := 108971073692985787928183

theorem tailTrace_5729951 : CollatzResearch.WordTrace tailWord_5729951 prefixEnd_5729951 108971073692985787928183 := by
  unfold tailWord_5729951
  simp only [CollatzResearch.WordTrace]
  refine ⟨208988482064373599565765707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139325654709582399710510471 208988482064373599565765707)
  ·
    refine ⟨313482723096560399348648561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208988482064373599565765707 313482723096560399348648561)
    ·
      refine ⟨235112042322420299511486421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313482723096560399348648561 235112042322420299511486421)
      ·
        refine ⟨5510438491931725769800463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 235112042322420299511486421 5510438491931725769800463)
        ·
          refine ⟨8265657737897588654700695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5510438491931725769800463 8265657737897588654700695)
          ·
            refine ⟨12398486606846382982051043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8265657737897588654700695 12398486606846382982051043)
            ·
              refine ⟨18597729910269574473076565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12398486606846382982051043 18597729910269574473076565)
              ·
                refine ⟨108971073692985787928183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18597729910269574473076565 108971073692985787928183)
                ·
                  rfl

theorem cell23_5729951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 9].length) (baseStart_5729951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729951 prefixEnd_5729951 := by exact prefixLift 5729951
  have htrace : WordTrace (prefixWord ++ tailWord_5729951) baseStart_5729951 baseEnd_5729951 := by
    simpa [prefixWord, tailWord_5729951, baseEnd_5729951] using wordTrace_append hprefix tailTrace_5729951
  have hstable : (prefixWord ++ tailWord_5729951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729951).length < 2 ^ (prefixWord ++ tailWord_5729951).sum := by decide
  have hdescent : baseEnd_5729951 < baseStart_5729951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729984 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 4]
def baseStart_5729984 : Nat := 118140960795 + 5729984 * 2 ^ 59
def prefixEnd_5729984 : Nat := 4983230072969 + 3 ^ 40 * 5729984 * 2
def baseEnd_5729984 : Nat := 2942235934572214644948289

theorem tailTrace_5729984 : CollatzResearch.WordTrace tailWord_5729984 prefixEnd_5729984 2942235934572214644948289 := by
  unfold tailWord_5729984
  simp only [CollatzResearch.WordTrace]
  refine ⟨104494842836627023100858503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139326457115502697467811337 104494842836627023100858503)
  ·
    refine ⟨156742264254940534651287755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104494842836627023100858503 156742264254940534651287755)
    ·
      refine ⟨235113396382410801976931633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156742264254940534651287755 235113396382410801976931633)
      ·
        refine ⟨176335047286808101482698725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235113396382410801976931633 176335047286808101482698725)
        ·
          refine ⟨33062821366276519028006011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176335047286808101482698725 33062821366276519028006011)
          ·
            refine ⟨49594232049414778542009017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33062821366276519028006011 49594232049414778542009017)
            ·
              refine ⟨37195674037061083906506763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49594232049414778542009017 37195674037061083906506763)
              ·
                refine ⟨55793511055591625859760145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37195674037061083906506763 55793511055591625859760145)
                ·
                  refine ⟨41845133291693719394820109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55793511055591625859760145 41845133291693719394820109)
                  ·
                    refine ⟨15691924984385144773057541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41845133291693719394820109 15691924984385144773057541)
                    ·
                      refine ⟨2942235934572214644948289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15691924984385144773057541 2942235934572214644948289)
                      ·
                        rfl

theorem cell23_5729984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_5729984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729984 prefixEnd_5729984 := by exact prefixLift 5729984
  have htrace : WordTrace (prefixWord ++ tailWord_5729984) baseStart_5729984 baseEnd_5729984 := by
    simpa [prefixWord, tailWord_5729984, baseEnd_5729984] using wordTrace_append hprefix tailTrace_5729984
  have hstable : (prefixWord ++ tailWord_5729984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729984).length < 2 ^ (prefixWord ++ tailWord_5729984).sum := by decide
  have hdescent : baseEnd_5729984 < baseStart_5729984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5729988 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_5729988 : Nat := 118140960795 + 5729988 * 2 ^ 59
def prefixEnd_5729988 : Nat := 4983230072969 + 3 ^ 40 * 5729988 * 2
def baseEnd_5729988 : Nat := 2942237988494832629298271

theorem tailTrace_5729988 : CollatzResearch.WordTrace tailWord_5729988 prefixEnd_5729988 2942237988494832629298271 := by
  unfold tailWord_5729988
  simp only [CollatzResearch.WordTrace]
  refine ⟨104494915782619777442431309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139326554376826369923241745 104494915782619777442431309)
  ·
    refine ⟨39185593418482416540911741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104494915782619777442431309 39185593418482416540911741)
    ·
      refine ⟨14694597531930906202841903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39185593418482416540911741 14694597531930906202841903)
      ·
        refine ⟨22041896297896359304262855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14694597531930906202841903 22041896297896359304262855)
        ·
          refine ⟨33062844446844538956394283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22041896297896359304262855 33062844446844538956394283)
          ·
            refine ⟨49594266670266808434591425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33062844446844538956394283 49594266670266808434591425)
            ·
              refine ⟨37195700002700106325943569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49594266670266808434591425 37195700002700106325943569)
              ·
                refine ⟨27896775002025079744457677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37195700002700106325943569 27896775002025079744457677)
                ·
                  refine ⟨10461290625759404904171629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27896775002025079744457677 10461290625759404904171629)
                  ·
                    refine ⟨3922983984659776839064361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10461290625759404904171629 3922983984659776839064361)
                    ·
                      refine ⟨2942237988494832629298271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3922983984659776839064361 2942237988494832629298271)
                      ·
                        rfl

theorem cell23_5729988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_5729988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5729988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5729988 prefixEnd_5729988 := by exact prefixLift 5729988
  have htrace : WordTrace (prefixWord ++ tailWord_5729988) baseStart_5729988 baseEnd_5729988 := by
    simpa [prefixWord, tailWord_5729988, baseEnd_5729988] using wordTrace_append hprefix tailTrace_5729988
  have hstable : (prefixWord ++ tailWord_5729988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5729988).length < 2 ^ (prefixWord ++ tailWord_5729988).sum := by decide
  have hdescent : baseEnd_5729988 < baseStart_5729988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5729988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
