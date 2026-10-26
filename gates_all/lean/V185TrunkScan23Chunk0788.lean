import V185TrunkScan23Chunk0787

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4661668 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_4661668 : Nat := 118140960795 + 4661668 * 2 ^ 59
def prefixEnd_4661668 : Nat := 4983230072969 + 3 ^ 40 * 4661668 * 2
def baseEnd_4661668 : Nat := 797892111894524145403795

theorem tailTrace_4661668 : CollatzResearch.WordTrace tailWord_4661668 prefixEnd_4661668 797892111894524145403795 := by
  unfold tailWord_4661668
  simp only [CollatzResearch.WordTrace]
  refine ⟨85012500037790230177404829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113350000050386973569873105 85012500037790230177404829)
  ·
    refine ⟨31879687514171336316526811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85012500037790230177404829 31879687514171336316526811)
    ·
      refine ⟨47819531271257004474790217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31879687514171336316526811 47819531271257004474790217)
      ·
        refine ⟨35864648453442753356092663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47819531271257004474790217 35864648453442753356092663)
        ·
          refine ⟨53796972680164130034138995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35864648453442753356092663 53796972680164130034138995)
          ·
            refine ⟨80695459020246195051208493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53796972680164130034138995 80695459020246195051208493)
            ·
              refine ⟨30260797132592323144203185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80695459020246195051208493 30260797132592323144203185)
              ·
                refine ⟨22695597849444242358152389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30260797132592323144203185 22695597849444242358152389)
                ·
                  refine ⟨4255424596770795442153573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22695597849444242358152389 4255424596770795442153573)
                  ·
                    refine ⟨797892111894524145403795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4255424596770795442153573 797892111894524145403795)
                    ·
                      rfl

theorem cell23_4661668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_4661668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661668 prefixEnd_4661668 := by exact prefixLift 4661668
  have htrace : WordTrace (prefixWord ++ tailWord_4661668) baseStart_4661668 baseEnd_4661668 := by
    simpa [prefixWord, tailWord_4661668, baseEnd_4661668] using wordTrace_append hprefix tailTrace_4661668
  have hstable : (prefixWord ++ tailWord_4661668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661668).length < 2 ^ (prefixWord ++ tailWord_4661668).sum := by decide
  have hdescent : baseEnd_4661668 < baseStart_4661668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661681 : List Nat := [1, 2, 2, 4, 1, 2, 11]
def baseStart_4661681 : Nat := 118140960795 + 4661681 * 2 ^ 59
def prefixEnd_4661681 : Nat := 4983230072969 + 3 ^ 40 * 4661681 * 2
def baseEnd_4661681 : Nat := 29551642110272603522825

theorem tailTrace_4661681 : CollatzResearch.WordTrace tailWord_4661681 prefixEnd_4661681 29551642110272603522825 := by
  unfold tailWord_4661681
  simp only [CollatzResearch.WordTrace]
  refine ⟨170025474224533363575032897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113350316149688909050021931 170025474224533363575032897)
  ·
    refine ⟨127519105668400022681274673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170025474224533363575032897 127519105668400022681274673)
    ·
      refine ⟨95639329251300017010956005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127519105668400022681274673 95639329251300017010956005)
      ·
        refine ⟨17932374234618753189554251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95639329251300017010956005 17932374234618753189554251)
        ·
          refine ⟨26898561351928129784331377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17932374234618753189554251 26898561351928129784331377)
          ·
            refine ⟨20173921013946097338248533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26898561351928129784331377 20173921013946097338248533)
            ·
              refine ⟨29551642110272603522825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20173921013946097338248533 29551642110272603522825)
              ·
                rfl

theorem cell23_4661681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 11].length) (baseStart_4661681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661681 prefixEnd_4661681 := by exact prefixLift 4661681
  have htrace : WordTrace (prefixWord ++ tailWord_4661681) baseStart_4661681 baseEnd_4661681 := by
    simpa [prefixWord, tailWord_4661681, baseEnd_4661681] using wordTrace_append hprefix tailTrace_4661681
  have hstable : (prefixWord ++ tailWord_4661681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661681).length < 2 ^ (prefixWord ++ tailWord_4661681).sum := by decide
  have hdescent : baseEnd_4661681 < baseStart_4661681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661725 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_4661725 : Nat := 118140960795 + 4661725 * 2 ^ 59
def prefixEnd_4661725 : Nat := 4983230072969 + 3 ^ 40 * 4661725 * 2
def baseEnd_4661725 : Nat := 2393705604080878713198623

theorem tailTrace_4661725 : CollatzResearch.WordTrace tailWord_4661725 prefixEnd_4661725 2393705604080878713198623 := by
  unfold tailWord_4661725
  simp only [CollatzResearch.WordTrace]
  refine ⟨170027079036373959089634629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113351386024249306059756419 170027079036373959089634629)
  ·
    refine ⟨31880077319320117329306493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170027079036373959089634629 31880077319320117329306493)
    ·
      refine ⟨11955028994745043998489935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31880077319320117329306493 11955028994745043998489935)
      ·
        refine ⟨17932543492117565997734903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11955028994745043998489935 17932543492117565997734903)
        ·
          refine ⟨26898815238176348996602355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17932543492117565997734903 26898815238176348996602355)
          ·
            refine ⟨40348222857264523494903533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26898815238176348996602355 40348222857264523494903533)
            ·
              refine ⟨15130583571474196310588825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40348222857264523494903533 15130583571474196310588825)
              ·
                refine ⟨11347937678605647232941619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15130583571474196310588825 11347937678605647232941619)
                ·
                  refine ⟨17021906517908470849412429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11347937678605647232941619 17021906517908470849412429)
                  ·
                    refine ⟨6383214944215676568529661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17021906517908470849412429 6383214944215676568529661)
                    ·
                      refine ⟨2393705604080878713198623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6383214944215676568529661 2393705604080878713198623)
                      ·
                        rfl

theorem cell23_4661725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_4661725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661725 prefixEnd_4661725 := by exact prefixLift 4661725
  have htrace : WordTrace (prefixWord ++ tailWord_4661725) baseStart_4661725 baseEnd_4661725 := by
    simpa [prefixWord, tailWord_4661725, baseEnd_4661725] using wordTrace_append hprefix tailTrace_4661725
  have hstable : (prefixWord ++ tailWord_4661725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661725).length < 2 ^ (prefixWord ++ tailWord_4661725).sum := by decide
  have hdescent : baseEnd_4661725 < baseStart_4661725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661742 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_4661742 : Nat := 118140960795 + 4661742 * 2 ^ 59
def prefixEnd_4661742 : Nat := 4983230072969 + 3 ^ 40 * 4661742 * 2
def baseEnd_4661742 : Nat := 2393714333252005146686045

theorem tailTrace_4661742 : CollatzResearch.WordTrace tailWord_4661742 prefixEnd_4661742 2393714333252005146686045 := by
  unfold tailWord_4661742
  simp only [CollatzResearch.WordTrace]
  refine ⟨21253462384664046374125435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113351799384874913995335653 21253462384664046374125435)
  ·
    refine ⟨31880193576996069561188153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21253462384664046374125435 31880193576996069561188153)
    ·
      refine ⟨23910145182747052170891115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31880193576996069561188153 23910145182747052170891115)
      ·
        refine ⟨35865217774120578256336673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23910145182747052170891115 35865217774120578256336673)
        ·
          refine ⟨26898913330590433692252505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35865217774120578256336673 26898913330590433692252505)
          ·
            refine ⟨20174184997942825269189379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26898913330590433692252505 20174184997942825269189379)
            ·
              refine ⟨30261277496914237903784069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20174184997942825269189379 30261277496914237903784069)
              ·
                refine ⟨5673989530671419606959513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30261277496914237903784069 5673989530671419606959513)
                ·
                  refine ⟨4255492148003564705219635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5673989530671419606959513 4255492148003564705219635)
                  ·
                    refine ⟨6383238222005347057829453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4255492148003564705219635 6383238222005347057829453)
                    ·
                      refine ⟨2393714333252005146686045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6383238222005347057829453 2393714333252005146686045)
                      ·
                        rfl

theorem cell23_4661742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_4661742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661742 prefixEnd_4661742 := by exact prefixLift 4661742
  have htrace : WordTrace (prefixWord ++ tailWord_4661742) baseStart_4661742 baseEnd_4661742 := by
    simpa [prefixWord, tailWord_4661742, baseEnd_4661742] using wordTrace_append hprefix tailTrace_4661742
  have hstable : (prefixWord ++ tailWord_4661742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661742).length < 2 ^ (prefixWord ++ tailWord_4661742).sum := by decide
  have hdescent : baseEnd_4661742 < baseStart_4661742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661765 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 1, 4, 2]
def baseStart_4661765 : Nat := 118140960795 + 4661765 * 2 ^ 59
def prefixEnd_4661765 : Nat := 4983230072969 + 3 ^ 40 * 4661765 * 2
def baseEnd_4661765 : Nat := 2393726143307058556698439

theorem tailTrace_4661765 : CollatzResearch.WordTrace tailWord_4661765 prefixEnd_4661765 2393726143307058556698439 := by
  unfold tailWord_4661765
  simp only [CollatzResearch.WordTrace]
  refine ⟨170028537956229045921090749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113352358637486030614060499 170028537956229045921090749)
  ·
    refine ⟨63760701733585892220409031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170028537956229045921090749 63760701733585892220409031)
    ·
      refine ⟨95641052600378838330613547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63760701733585892220409031 95641052600378838330613547)
      ·
        refine ⟨143461578900568257495920321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95641052600378838330613547 143461578900568257495920321)
        ·
          refine ⟨107596184175426193121940241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143461578900568257495920321 107596184175426193121940241)
          ·
            refine ⟨80697138131569644841455181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107596184175426193121940241 80697138131569644841455181)
            ·
              refine ⟨30261426799338616815545693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80697138131569644841455181 30261426799338616815545693)
              ·
                refine ⟨11348035049751981305829635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30261426799338616815545693 11348035049751981305829635)
                ·
                  refine ⟨17022052574627971958744453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11348035049751981305829635 17022052574627971958744453)
                  ·
                    refine ⟨3191634857742744742264585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17022052574627971958744453 3191634857742744742264585)
                    ·
                      refine ⟨2393726143307058556698439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3191634857742744742264585 2393726143307058556698439)
                      ·
                        rfl

theorem cell23_4661765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 4, 2].length) (baseStart_4661765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661765 prefixEnd_4661765 := by exact prefixLift 4661765
  have htrace : WordTrace (prefixWord ++ tailWord_4661765) baseStart_4661765 baseEnd_4661765 := by
    simpa [prefixWord, tailWord_4661765, baseEnd_4661765] using wordTrace_append hprefix tailTrace_4661765
  have hstable : (prefixWord ++ tailWord_4661765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661765).length < 2 ^ (prefixWord ++ tailWord_4661765).sum := by decide
  have hdescent : baseEnd_4661765 < baseStart_4661765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661768 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_4661768 : Nat := 118140960795 + 4661768 * 2 ^ 59
def prefixEnd_4661768 : Nat := 4983230072969 + 3 ^ 40 * 4661768 * 2
def baseEnd_4661768 : Nat := 2393727683749022044960925

theorem tailTrace_4661768 : CollatzResearch.WordTrace tailWord_4661768 prefixEnd_4661768 2393727683749022044960925 := by
  unfold tailWord_4661768
  simp only [CollatzResearch.WordTrace]
  refine ⟨85014323687609088716724979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113352431583478784955633305 85014323687609088716724979)
  ·
    refine ⟨127521485531413633075087469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85014323687609088716724979 127521485531413633075087469)
    ·
      refine ⟨47820557074280112403157801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127521485531413633075087469 47820557074280112403157801)
      ·
        refine ⟨35865417805710084302368351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47820557074280112403157801 35865417805710084302368351)
        ·
          refine ⟨53798126708565126453552527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35865417805710084302368351 53798126708565126453552527)
          ·
            refine ⟨80697190062847689680328791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53798126708565126453552527 80697190062847689680328791)
            ·
              refine ⟨121045785094271534520493187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80697190062847689680328791 121045785094271534520493187)
              ·
                refine ⟨181568677641407301780739781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121045785094271534520493187 181568677641407301780739781)
                ·
                  refine ⟨34044127057763869083888709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181568677641407301780739781 34044127057763869083888709)
                  ·
                    refine ⟨6383273823330725453229133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34044127057763869083888709 6383273823330725453229133)
                    ·
                      refine ⟨2393727683749022044960925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6383273823330725453229133 2393727683749022044960925)
                      ·
                        rfl

theorem cell23_4661768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_4661768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661768 prefixEnd_4661768 := by exact prefixLift 4661768
  have htrace : WordTrace (prefixWord ++ tailWord_4661768) baseStart_4661768 baseEnd_4661768 := by
    simpa [prefixWord, tailWord_4661768, baseEnd_4661768] using wordTrace_append hprefix tailTrace_4661768
  have hstable : (prefixWord ++ tailWord_4661768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661768).length < 2 ^ (prefixWord ++ tailWord_4661768).sum := by decide
  have hdescent : baseEnd_4661768 < baseStart_4661768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661818 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_4661818 : Nat := 118140960795 + 4661818 * 2 ^ 59
def prefixEnd_4661818 : Nat := 4983230072969 + 3 ^ 40 * 4661818 * 2
def baseEnd_4661818 : Nat := 797917785927248949778565

theorem tailTrace_4661818 : CollatzResearch.WordTrace tailWord_4661818 prefixEnd_4661818 797917785927248949778565 := by
  unfold tailWord_4661818
  simp only [CollatzResearch.WordTrace]
  refine ⟨42507617756259258993192527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113353647350024690648513405 42507617756259258993192527)
  ·
    refine ⟨63761426634388888489788791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42507617756259258993192527 63761426634388888489788791)
    ·
      refine ⟨95642139951583332734683187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63761426634388888489788791 95642139951583332734683187)
      ·
        refine ⟨143463209927374999102024781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95642139951583332734683187 143463209927374999102024781)
        ·
          refine ⟨53798703722765624663259293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143463209927374999102024781 53798703722765624663259293)
          ·
            refine ⟨20174513896037109248722235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53798703722765624663259293 20174513896037109248722235)
            ·
              refine ⟨30261770844055663873083353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20174513896037109248722235 30261770844055663873083353)
              ·
                refine ⟨22696328133041747904812515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30261770844055663873083353 22696328133041747904812515)
                ·
                  refine ⟨34044492199562621857218773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22696328133041747904812515 34044492199562621857218773)
                  ·
                    refine ⟨797917785927248949778565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34044492199562621857218773 797917785927248949778565)
                    ·
                      rfl

theorem cell23_4661818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_4661818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661818 prefixEnd_4661818 := by exact prefixLift 4661818
  have htrace : WordTrace (prefixWord ++ tailWord_4661818) baseStart_4661818 baseEnd_4661818 := by
    simpa [prefixWord, tailWord_4661818, baseEnd_4661818] using wordTrace_append hprefix tailTrace_4661818
  have hstable : (prefixWord ++ tailWord_4661818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661818).length < 2 ^ (prefixWord ++ tailWord_4661818).sum := by decide
  have hdescent : baseEnd_4661818 < baseStart_4661818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661852 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_4661852 : Nat := 118140960795 + 4661852 * 2 ^ 59
def prefixEnd_4661852 : Nat := 4983230072969 + 3 ^ 40 * 4661852 * 2
def baseEnd_4661852 : Nat := 797923605374666572103513

theorem tailTrace_4661852 : CollatzResearch.WordTrace tailWord_4661852 prefixEnd_4661852 797923605374666572103513 := by
  unfold tailWord_4661852
  simp only [CollatzResearch.WordTrace]
  refine ⟨85015855553456929889753905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113354474071275906519671873 85015855553456929889753905)
  ·
    refine ⟨63761891665092697417315429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85015855553456929889753905 63761891665092697417315429)
    ·
      refine ⟨11955354687204880765746643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63761891665092697417315429 11955354687204880765746643)
      ·
        refine ⟨17933032030807321148619965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11955354687204880765746643 17933032030807321148619965)
        ·
          refine ⟨6724887011552745430732487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17933032030807321148619965 6724887011552745430732487)
          ·
            refine ⟨10087330517329118146098731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6724887011552745430732487 10087330517329118146098731)
            ·
              refine ⟨15130995775993677219148097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10087330517329118146098731 15130995775993677219148097)
              ·
                refine ⟨11348246831995257914361073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15130995775993677219148097 11348246831995257914361073)
                ·
                  refine ⟨8511185123996443435770805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11348246831995257914361073 8511185123996443435770805)
                  ·
                    refine ⟨797923605374666572103513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8511185123996443435770805 797923605374666572103513)
                    ·
                      rfl

theorem cell23_4661852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_4661852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661852 prefixEnd_4661852 := by exact prefixLift 4661852
  have htrace : WordTrace (prefixWord ++ tailWord_4661852) baseStart_4661852 baseEnd_4661852 := by
    simpa [prefixWord, tailWord_4661852, baseEnd_4661852] using wordTrace_append hprefix tailTrace_4661852
  have hstable : (prefixWord ++ tailWord_4661852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661852).length < 2 ^ (prefixWord ++ tailWord_4661852).sum := by decide
  have hdescent : baseEnd_4661852 < baseStart_4661852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661855 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 4, 4, 2]
def baseStart_4661855 : Nat := 118140960795 + 4661855 * 2 ^ 59
def prefixEnd_4661855 : Nat := 4983230072969 + 3 ^ 40 * 4661855 * 2
def baseEnd_4661855 : Nat := 2393772356565963204573025

theorem tailTrace_4661855 : CollatzResearch.WordTrace tailWord_4661855 prefixEnd_4661855 2393772356565963204573025 := by
  unfold tailWord_4661855
  simp only [CollatzResearch.WordTrace]
  refine ⟨170031820525902991291867019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113354547017268660861244679 170031820525902991291867019)
  ·
    refine ⟨255047730788854486937800529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170031820525902991291867019 255047730788854486937800529)
    ·
      refine ⟨191285798091640865203350397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255047730788854486937800529 191285798091640865203350397)
      ·
        refine ⟨71732174284365324451256399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191285798091640865203350397 71732174284365324451256399)
        ·
          refine ⟨107598261426547986676884599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71732174284365324451256399 107598261426547986676884599)
          ·
            refine ⟨161397392139821980015326899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107598261426547986676884599 161397392139821980015326899)
            ·
              refine ⟨242096088209732970022990349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161397392139821980015326899 242096088209732970022990349)
              ·
                refine ⟨90786033078649863758621381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242096088209732970022990349 90786033078649863758621381)
                ·
                  refine ⟨17022381202246849454741509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90786033078649863758621381 17022381202246849454741509)
                  ·
                    refine ⟨3191696475421284272764033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17022381202246849454741509 3191696475421284272764033)
                    ·
                      refine ⟨2393772356565963204573025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3191696475421284272764033 2393772356565963204573025)
                      ·
                        rfl

theorem cell23_4661855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_4661855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661855 prefixEnd_4661855 := by exact prefixLift 4661855
  have htrace : WordTrace (prefixWord ++ tailWord_4661855) baseStart_4661855 baseEnd_4661855 := by
    simpa [prefixWord, tailWord_4661855, baseEnd_4661855] using wordTrace_append hprefix tailTrace_4661855
  have hstable : (prefixWord ++ tailWord_4661855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661855).length < 2 ^ (prefixWord ++ tailWord_4661855).sum := by decide
  have hdescent : baseEnd_4661855 < baseStart_4661855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661868 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_4661868 : Nat := 118140960795 + 4661868 * 2 ^ 59
def prefixEnd_4661868 : Nat := 4983230072969 + 3 ^ 40 * 4661868 * 2
def baseEnd_4661868 : Nat := 2393779031814471653710465

theorem tailTrace_4661868 : CollatzResearch.WordTrace tailWord_4661868 prefixEnd_4661868 2393779031814471653710465 := by
  unfold tailWord_4661868
  simp only [CollatzResearch.WordTrace]
  refine ⟨85016147337427947256045129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113354863116570596341393505 85016147337427947256045129)
  ·
    refine ⟨63762110503070960442033847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85016147337427947256045129 63762110503070960442033847)
    ·
      refine ⟨95643165754606440663050771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63762110503070960442033847 95643165754606440663050771)
      ·
        refine ⟨143464748631909660994576157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95643165754606440663050771 143464748631909660994576157)
        ·
          refine ⟨53799280736966122872966059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143464748631909660994576157 53799280736966122872966059)
          ·
            refine ⟨80698921105449184309449089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53799280736966122872966059 80698921105449184309449089)
            ·
              refine ⟨60524190829086888232086817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80698921105449184309449089 60524190829086888232086817)
              ·
                refine ⟨45393143121815166174065113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60524190829086888232086817 45393143121815166174065113)
                ·
                  refine ⟨34044857341361374630548835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45393143121815166174065113 34044857341361374630548835)
                  ·
                    refine ⟨51067286012042061945823253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34044857341361374630548835 51067286012042061945823253)
                    ·
                      refine ⟨2393779031814471653710465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51067286012042061945823253 2393779031814471653710465)
                      ·
                        rfl

theorem cell23_4661868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_4661868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661868 prefixEnd_4661868 := by exact prefixLift 4661868
  have htrace : WordTrace (prefixWord ++ tailWord_4661868) baseStart_4661868 baseEnd_4661868 := by
    simpa [prefixWord, tailWord_4661868, baseEnd_4661868] using wordTrace_append hprefix tailTrace_4661868
  have hstable : (prefixWord ++ tailWord_4661868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661868).length < 2 ^ (prefixWord ++ tailWord_4661868).sum := by decide
  have hdescent : baseEnd_4661868 < baseStart_4661868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661892 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_4661892 : Nat := 118140960795 + 4661892 * 2 ^ 59
def prefixEnd_4661892 : Nat := 4983230072969 + 3 ^ 40 * 4661892 * 2
def baseEnd_4661892 : Nat := 2393791355350179559810355

theorem tailTrace_4661892 : CollatzResearch.WordTrace tailWord_4661892 prefixEnd_4661892 2393791355350179559810355 := by
  unfold tailWord_4661892
  simp only [CollatzResearch.WordTrace]
  refine ⟨85016585013384473305481965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113355446684512631073975953 85016585013384473305481965)
  ·
    refine ⟨31881219380019177489555737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85016585013384473305481965 31881219380019177489555737)
    ·
      refine ⟨23910914535014383117166803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31881219380019177489555737 23910914535014383117166803)
      ·
        refine ⟨35866371802521574675750205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23910914535014383117166803 35866371802521574675750205)
        ·
          refine ⟨13449889425945590503406327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35866371802521574675750205 13449889425945590503406327)
          ·
            refine ⟨20174834138918385755109491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13449889425945590503406327 20174834138918385755109491)
            ·
              refine ⟨30262251208377578632664237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20174834138918385755109491 30262251208377578632664237)
              ·
                refine ⟨11348344203141591987249089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30262251208377578632664237 11348344203141591987249089)
                ·
                  refine ⟨8511258152356193990436817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11348344203141591987249089 8511258152356193990436817)
                  ·
                    refine ⟨6383443614267145492827613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8511258152356193990436817 6383443614267145492827613)
                    ·
                      refine ⟨2393791355350179559810355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6383443614267145492827613 2393791355350179559810355)
                      ·
                        rfl

theorem cell23_4661892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_4661892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661892 prefixEnd_4661892 := by exact prefixLift 4661892
  have htrace : WordTrace (prefixWord ++ tailWord_4661892) baseStart_4661892 baseEnd_4661892 := by
    simpa [prefixWord, tailWord_4661892, baseEnd_4661892] using wordTrace_append hprefix tailTrace_4661892
  have hstable : (prefixWord ++ tailWord_4661892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661892).length < 2 ^ (prefixWord ++ tailWord_4661892).sum := by decide
  have hdescent : baseEnd_4661892 < baseStart_4661892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661916 : List Nat := [2, 2, 3, 2, 2, 1, 4, 2, 1, 4]
def baseStart_4661916 : Nat := 118140960795 + 4661916 * 2 ^ 59
def prefixEnd_4661916 : Nat := 4983230072969 + 3 ^ 40 * 4661916 * 2
def baseEnd_4661916 : Nat := 797934559628629155303415

theorem tailTrace_4661916 : CollatzResearch.WordTrace tailWord_4661916 prefixEnd_4661916 797934559628629155303415 := by
  unfold tailWord_4661916
  simp only [CollatzResearch.WordTrace]
  refine ⟨85017022689340999354918801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113356030252454665806558401 85017022689340999354918801)
  ·
    refine ⟨63762767017005749516189101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85017022689340999354918801 63762767017005749516189101)
    ·
      refine ⟨23911037631377156068570913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63762767017005749516189101 23911037631377156068570913)
      ·
        refine ⟨17933278223532867051428185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23911037631377156068570913 17933278223532867051428185)
        ·
          refine ⟨13449958667649650288571139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17933278223532867051428185 13449958667649650288571139)
          ·
            refine ⟨20174938001474475432856709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13449958667649650288571139 20174938001474475432856709)
            ·
              refine ⟨3782800875276464143660633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20174938001474475432856709 3782800875276464143660633)
              ·
                refine ⟨2837100656457348107745475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3782800875276464143660633 2837100656457348107745475)
                ·
                  refine ⟨4255650984686022161618213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837100656457348107745475 4255650984686022161618213)
                  ·
                    refine ⟨797934559628629155303415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4255650984686022161618213 797934559628629155303415)
                    ·
                      rfl

theorem cell23_4661916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_4661916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661916 prefixEnd_4661916 := by exact prefixLift 4661916
  have htrace : WordTrace (prefixWord ++ tailWord_4661916) baseStart_4661916 baseEnd_4661916 := by
    simpa [prefixWord, tailWord_4661916, baseEnd_4661916] using wordTrace_append hprefix tailTrace_4661916
  have hstable : (prefixWord ++ tailWord_4661916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661916).length < 2 ^ (prefixWord ++ tailWord_4661916).sum := by decide
  have hdescent : baseEnd_4661916 < baseStart_4661916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661949 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 2, 3, 2]
def baseStart_4661949 : Nat := 118140960795 + 4661949 * 2 ^ 59
def prefixEnd_4661949 : Nat := 4983230072969 + 3 ^ 40 * 4661949 * 2
def baseEnd_4661949 : Nat := 2393820623747485836797593

theorem tailTrace_4661949 : CollatzResearch.WordTrace tailWord_4661949 prefixEnd_4661949 2393820623747485836797593 := by
  unfold tailWord_4661949
  simp only [CollatzResearch.WordTrace]
  refine ⟨170035248987562445345788901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113356832658374963563859267 170035248987562445345788901)
  ·
    refine ⟨31881609185167958502335419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170035248987562445345788901 31881609185167958502335419)
    ·
      refine ⟨47822413777751937753503129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31881609185167958502335419 47822413777751937753503129)
      ·
        refine ⟨35866810333313953315127347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47822413777751937753503129 35866810333313953315127347)
        ·
          refine ⟨53800215499970929972691021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35866810333313953315127347 53800215499970929972691021)
          ·
            refine ⟨20175080812489098739759133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53800215499970929972691021 20175080812489098739759133)
            ·
              refine ⟨7565655304683412027409675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20175080812489098739759133 7565655304683412027409675)
              ·
                refine ⟨11348482957025118041114513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7565655304683412027409675 11348482957025118041114513)
                ·
                  refine ⟨8511362217768838530835885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11348482957025118041114513 8511362217768838530835885)
                  ·
                    refine ⟨3191760831663314449063457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8511362217768838530835885 3191760831663314449063457)
                    ·
                      refine ⟨2393820623747485836797593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3191760831663314449063457 2393820623747485836797593)
                      ·
                        rfl

theorem cell23_4661949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_4661949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661949 prefixEnd_4661949 := by exact prefixLift 4661949
  have htrace : WordTrace (prefixWord ++ tailWord_4661949) baseStart_4661949 baseEnd_4661949 := by
    simpa [prefixWord, tailWord_4661949, baseEnd_4661949] using wordTrace_append hprefix tailTrace_4661949
  have hstable : (prefixWord ++ tailWord_4661949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661949).length < 2 ^ (prefixWord ++ tailWord_4661949).sum := by decide
  have hdescent : baseEnd_4661949 < baseStart_4661949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661956 : List Nat := [2, 3, 3, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_4661956 : Nat := 118140960795 + 4661956 * 2 ^ 59
def prefixEnd_4661956 : Nat := 4983230072969 + 3 ^ 40 * 4661956 * 2
def baseEnd_4661956 : Nat := 2393824218112067309410061

theorem tailTrace_4661956 : CollatzResearch.WordTrace tailWord_4661956 prefixEnd_4661956 2393824218112067309410061 := by
  unfold tailWord_4661956
  simp only [CollatzResearch.WordTrace]
  refine ⟨85017752149268542770646861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113357002865691390360862481 85017752149268542770646861)
  ·
    refine ⟨31881657055975703538992573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85017752149268542770646861 31881657055975703538992573)
    ·
      refine ⟨11955621395990888827122215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31881657055975703538992573 11955621395990888827122215)
      ·
        refine ⟨17933432093986333240683323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11955621395990888827122215 17933432093986333240683323)
        ·
          refine ⟨26900148140979499861024985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17933432093986333240683323 26900148140979499861024985)
          ·
            refine ⟨20175111105734624895768739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26900148140979499861024985 20175111105734624895768739)
            ·
              refine ⟨30262666658601937343653109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20175111105734624895768739 30262666658601937343653109)
              ·
                refine ⟨2837124999243931625967479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30262666658601937343653109 2837124999243931625967479)
                ·
                  refine ⟨4255687498865897438951219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837124999243931625967479 4255687498865897438951219)
                  ·
                    refine ⟨6383531248298846158426829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4255687498865897438951219 6383531248298846158426829)
                    ·
                      refine ⟨2393824218112067309410061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6383531248298846158426829 2393824218112067309410061)
                      ·
                        rfl

theorem cell23_4661956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_4661956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661956 prefixEnd_4661956 := by exact prefixLift 4661956
  have htrace : WordTrace (prefixWord ++ tailWord_4661956) baseStart_4661956 baseEnd_4661956 := by
    simpa [prefixWord, tailWord_4661956, baseEnd_4661956] using wordTrace_append hprefix tailTrace_4661956
  have hstable : (prefixWord ++ tailWord_4661956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661956).length < 2 ^ (prefixWord ++ tailWord_4661956).sum := by decide
  have hdescent : baseEnd_4661956 < baseStart_4661956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661992 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_4661992 : Nat := 118140960795 + 4661992 * 2 ^ 59
def prefixEnd_4661992 : Nat := 4983230072969 + 3 ^ 40 * 4661992 * 2
def baseEnd_4661992 : Nat := 2393842703415629168559895

theorem tailTrace_4661992 : CollatzResearch.WordTrace tailWord_4661992 prefixEnd_4661992 2393842703415629168559895 := by
  unfold tailWord_4661992
  simp only [CollatzResearch.WordTrace]
  refine ⟨85018408663203331844802115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113357878217604442459736153 85018408663203331844802115)
  ·
    refine ⟨127527612994804997767203173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85018408663203331844802115 127527612994804997767203173)
    ·
      refine ⟨23911427436525937081350595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127527612994804997767203173 23911427436525937081350595)
      ·
        refine ⟨35867141154788905622025893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23911427436525937081350595 35867141154788905622025893)
        ·
          refine ⟨6725088966522919804129855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35867141154788905622025893 6725088966522919804129855)
          ·
            refine ⟨10087633449784379706194783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6725088966522919804129855 10087633449784379706194783)
            ·
              refine ⟨15131450174676569559292175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10087633449784379706194783 15131450174676569559292175)
              ·
                refine ⟨22697175262014854338938263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15131450174676569559292175 22697175262014854338938263)
                ·
                  refine ⟨34045762893022281508407395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22697175262014854338938263 34045762893022281508407395)
                  ·
                    refine ⟨51068644339533422262611093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34045762893022281508407395 51068644339533422262611093)
                    ·
                      refine ⟨2393842703415629168559895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51068644339533422262611093 2393842703415629168559895)
                      ·
                        rfl

theorem cell23_4661992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_4661992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661992 prefixEnd_4661992 := by exact prefixLift 4661992
  have htrace : WordTrace (prefixWord ++ tailWord_4661992) baseStart_4661992 baseEnd_4661992 := by
    simpa [prefixWord, tailWord_4661992, baseEnd_4661992] using wordTrace_append hprefix tailTrace_4661992
  have hstable : (prefixWord ++ tailWord_4661992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661992).length < 2 ^ (prefixWord ++ tailWord_4661992).sum := by decide
  have hdescent : baseEnd_4661992 < baseStart_4661992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4661999 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 1, 2, 3]
def baseStart_4661999 : Nat := 118140960795 + 4661999 * 2 ^ 59
def prefixEnd_4661999 : Nat := 4983230072969 + 3 ^ 40 * 4661999 * 2
def baseEnd_4661999 : Nat := 2393846297780210641172363

theorem tailTrace_4661999 : CollatzResearch.WordTrace tailWord_4661999 prefixEnd_4661999 2393846297780210641172363 := by
  unfold tailWord_4661999
  simp only [CollatzResearch.WordTrace]
  refine ⟨170037072637381303885109051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113358048424920869256739367 170037072637381303885109051)
  ·
    refine ⟨255055608956071955827663577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170037072637381303885109051 255055608956071955827663577)
    ·
      refine ⟨191291706717053966870747683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255055608956071955827663577 191291706717053966870747683)
      ·
        refine ⟨286937560075580950306121525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191291706717053966870747683 286937560075580950306121525)
        ·
          refine ⟨26900396257085714091198893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 286937560075580950306121525 26900396257085714091198893)
          ·
            refine ⟨10087648596407142784199585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26900396257085714091198893 10087648596407142784199585)
            ·
              refine ⟨7565736447305357088149689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10087648596407142784199585 7565736447305357088149689)
              ·
                refine ⟨5674302335479017816112267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7565736447305357088149689 5674302335479017816112267)
                ·
                  refine ⟨8511453503218526724168401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5674302335479017816112267 8511453503218526724168401)
                  ·
                    refine ⟨6383590127413895043126301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8511453503218526724168401 6383590127413895043126301)
                    ·
                      refine ⟨2393846297780210641172363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6383590127413895043126301 2393846297780210641172363)
                      ·
                        rfl

theorem cell23_4661999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 2, 3].length) (baseStart_4661999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4661999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4661999 prefixEnd_4661999 := by exact prefixLift 4661999
  have htrace : WordTrace (prefixWord ++ tailWord_4661999) baseStart_4661999 baseEnd_4661999 := by
    simpa [prefixWord, tailWord_4661999, baseEnd_4661999] using wordTrace_append hprefix tailTrace_4661999
  have hstable : (prefixWord ++ tailWord_4661999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4661999).length < 2 ^ (prefixWord ++ tailWord_4661999).sum := by decide
  have hdescent : baseEnd_4661999 < baseStart_4661999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4661999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662002 : List Nat := [3, 2, 1, 3, 1, 2, 4, 7]
def baseStart_4662002 : Nat := 118140960795 + 4662002 * 2 ^ 59
def prefixEnd_4662002 : Nat := 4983230072969 + 3 ^ 40 * 4662002 * 2
def baseEnd_4662002 : Nat := 88661031045265708497587

theorem tailTrace_4662002 : CollatzResearch.WordTrace tailWord_4662002 prefixEnd_4662002 88661031045265708497587 := by
  unfold tailWord_4662002
  simp only [CollatzResearch.WordTrace]
  refine ⟨42509295514092608849367065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113358121370913623598312173 42509295514092608849367065)
  ·
    refine ⟨31881971635569456637025299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42509295514092608849367065 31881971635569456637025299)
    ·
      refine ⟨47822957453354184955537949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31881971635569456637025299 47822957453354184955537949)
      ·
        refine ⟨17933609045007819358326731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47822957453354184955537949 17933609045007819358326731)
        ·
          refine ⟨26900413567511729037490097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17933609045007819358326731 26900413567511729037490097)
          ·
            refine ⟨20175310175633796778117573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26900413567511729037490097 20175310175633796778117573)
            ·
              refine ⟨3782870657931336895897045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20175310175633796778117573 3782870657931336895897045)
              ·
                refine ⟨88661031045265708497587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3782870657931336895897045 88661031045265708497587)
                ·
                  rfl

theorem cell23_4662002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 7].length) (baseStart_4662002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662002 prefixEnd_4662002 := by exact prefixLift 4662002
  have htrace : WordTrace (prefixWord ++ tailWord_4662002) baseStart_4662002 baseEnd_4662002 := by
    simpa [prefixWord, tailWord_4662002, baseEnd_4662002] using wordTrace_append hprefix tailTrace_4662002
  have hstable : (prefixWord ++ tailWord_4662002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662002).length < 2 ^ (prefixWord ++ tailWord_4662002).sum := by decide
  have hdescent : baseEnd_4662002 < baseStart_4662002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662035 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 4]
def baseStart_4662035 : Nat := 118140960795 + 4662035 * 2 ^ 59
def prefixEnd_4662035 : Nat := 4983230072969 + 3 ^ 40 * 4662035 * 2
def baseEnd_4662035 : Nat := 2393864783083772500322197

theorem tailTrace_4662035 : CollatzResearch.WordTrace tailWord_4662035 prefixEnd_4662035 2393864783083772500322197 := by
  unfold tailWord_4662035
  simp only [CollatzResearch.WordTrace]
  refine ⟨170038385665250882033419559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113358923776833921355613039 170038385665250882033419559)
  ·
    refine ⟨255057578497876323050129339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170038385665250882033419559 255057578497876323050129339)
    ·
      refine ⟨382586367746814484575194009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255057578497876323050129339 382586367746814484575194009)
      ·
        refine ⟨286939775810110863431395507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382586367746814484575194009 286939775810110863431395507)
        ·
          refine ⟨430409663715166295147093261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286939775810110863431395507 430409663715166295147093261)
          ·
            refine ⟨161403623893187360680159973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 430409663715166295147093261 161403623893187360680159973)
            ·
              refine ⟨30263179479972630127529995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161403623893187360680159973 30263179479972630127529995)
              ·
                refine ⟨45394769219958945191294993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30263179479972630127529995 45394769219958945191294993)
                ·
                  refine ⟨34046076914969208893471245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45394769219958945191294993 34046076914969208893471245)
                  ·
                    refine ⟨12767278843113453335051717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34046076914969208893471245 12767278843113453335051717)
                    ·
                      refine ⟨2393864783083772500322197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12767278843113453335051717 2393864783083772500322197)
                      ·
                        rfl

theorem cell23_4662035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_4662035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662035 prefixEnd_4662035 := by exact prefixLift 4662035
  have htrace : WordTrace (prefixWord ++ tailWord_4662035) baseStart_4662035 baseEnd_4662035 := by
    simpa [prefixWord, tailWord_4662035, baseEnd_4662035] using wordTrace_append hprefix tailTrace_4662035
  have hstable : (prefixWord ++ tailWord_4662035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662035).length < 2 ^ (prefixWord ++ tailWord_4662035).sum := by decide
  have hdescent : baseEnd_4662035 < baseStart_4662035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662069 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_4662069 : Nat := 118140960795 + 4662069 * 2 ^ 59
def prefixEnd_4662069 : Nat := 4983230072969 + 3 ^ 40 * 4662069 * 2
def baseEnd_4662069 : Nat := 2393882241426025367297041

theorem tailTrace_4662069 : CollatzResearch.WordTrace tailWord_4662069 prefixEnd_4662069 2393882241426025367297041 := by
  unfold tailWord_4662069
  simp only [CollatzResearch.WordTrace]
  refine ⟨170039625747127705840157261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113359750498085137226771507 170039625747127705840157261)
  ·
    refine ⟨63764859655172889690058973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170039625747127705840157261 63764859655172889690058973)
    ·
      refine ⟨23911822370689833633772115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63764859655172889690058973 23911822370689833633772115)
      ·
        refine ⟨35867733556034750450658173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23911822370689833633772115 35867733556034750450658173)
        ·
          refine ⟨13450400083513031418996815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35867733556034750450658173 13450400083513031418996815)
          ·
            refine ⟨20175600125269547128495223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13450400083513031418996815 20175600125269547128495223)
            ·
              refine ⟨30263400187904320692742835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20175600125269547128495223 30263400187904320692742835)
              ·
                refine ⟨45395100281856481039114253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30263400187904320692742835 45395100281856481039114253)
                ·
                  refine ⟨17023162605696180389667845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45395100281856481039114253 17023162605696180389667845)
                  ·
                    refine ⟨3191842988568033823062721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17023162605696180389667845 3191842988568033823062721)
                    ·
                      refine ⟨2393882241426025367297041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3191842988568033823062721 2393882241426025367297041)
                      ·
                        rfl

theorem cell23_4662069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_4662069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662069 prefixEnd_4662069 := by exact prefixLift 4662069
  have htrace : WordTrace (prefixWord ++ tailWord_4662069) baseStart_4662069 baseEnd_4662069 := by
    simpa [prefixWord, tailWord_4662069, baseEnd_4662069] using wordTrace_append hprefix tailTrace_4662069
  have hstable : (prefixWord ++ tailWord_4662069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662069).length < 2 ^ (prefixWord ++ tailWord_4662069).sum := by decide
  have hdescent : baseEnd_4662069 < baseStart_4662069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662135 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 1, 10]
def baseStart_4662135 : Nat := 118140960795 + 4662135 * 2 ^ 59
def prefixEnd_4662135 : Nat := 4983230072969 + 3 ^ 40 * 4662135 * 2
def baseEnd_4662135 : Nat := 797972043716407369690579

theorem tailTrace_4662135 : CollatzResearch.WordTrace tailWord_4662135 prefixEnd_4662135 797972043716407369690579 := by
  unfold tailWord_4662135
  simp only [CollatzResearch.WordTrace]
  refine ⟨170042032964888599112059859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113361355309925732741373239 170042032964888599112059859)
  ·
    refine ⟨255063049447332898668089789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170042032964888599112059859 255063049447332898668089789)
    ·
      refine ⟨95648643542749837000533671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255063049447332898668089789 95648643542749837000533671)
      ·
        refine ⟨143472965314124755500800507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95648643542749837000533671 143472965314124755500800507)
        ·
          refine ⟨215209447971187133251200761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143472965314124755500800507 215209447971187133251200761)
          ·
            refine ⟨161407085978390349938400571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215209447971187133251200761 161407085978390349938400571)
            ·
              refine ⟨242110628967585524907600857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161407085978390349938400571 242110628967585524907600857)
              ·
                refine ⟨181582971725689143680700643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242110628967585524907600857 181582971725689143680700643)
                ·
                  refine ⟨272374457588533715521050965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181582971725689143680700643 272374457588533715521050965)
                  ·
                    refine ⟨797972043716407369690579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 272374457588533715521050965 797972043716407369690579)
                    ·
                      rfl

theorem cell23_4662135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_4662135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662135 prefixEnd_4662135 := by exact prefixLift 4662135
  have htrace : WordTrace (prefixWord ++ tailWord_4662135) baseStart_4662135 baseEnd_4662135 := by
    simpa [prefixWord, tailWord_4662135, baseEnd_4662135] using wordTrace_append hprefix tailTrace_4662135
  have hstable : (prefixWord ++ tailWord_4662135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662135).length < 2 ^ (prefixWord ++ tailWord_4662135).sum := by decide
  have hdescent : baseEnd_4662135 < baseStart_4662135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662243 : List Nat := [1, 1, 1, 6, 1, 1, 2, 5, 1, 1, 3]
def baseStart_4662243 : Nat := 118140960795 + 4662243 * 2 ^ 59
def prefixEnd_4662243 : Nat := 4983230072969 + 3 ^ 40 * 4662243 * 2
def baseEnd_4662243 : Nat := 2393971587059907686521241

theorem tailTrace_4662243 : CollatzResearch.WordTrace tailWord_4662243 prefixEnd_4662243 2393971587059907686521241 := by
  unfold tailWord_4662243
  simp only [CollatzResearch.WordTrace]
  refine ⟨170045972048497333556991383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113363981365664889037994255 170045972048497333556991383)
  ·
    refine ⟨255068958072746000335487075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170045972048497333556991383 255068958072746000335487075)
    ·
      refine ⟨382603437109119000503230613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255068958072746000335487075 382603437109119000503230613)
      ·
        refine ⟨17934536114489953148588935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 382603437109119000503230613 17934536114489953148588935)
        ·
          refine ⟨26901804171734929722883403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17934536114489953148588935 26901804171734929722883403)
          ·
            refine ⟨40352706257602394584325105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26901804171734929722883403 40352706257602394584325105)
            ·
              refine ⟨30264529693201795938243829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40352706257602394584325105 30264529693201795938243829)
              ·
                refine ⟨2837299658737668369210359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30264529693201795938243829 2837299658737668369210359)
                ·
                  refine ⟨4255949488106502553815539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837299658737668369210359 4255949488106502553815539)
                  ·
                    refine ⟨6383924232159753830723309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4255949488106502553815539 6383924232159753830723309)
                    ·
                      refine ⟨2393971587059907686521241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6383924232159753830723309 2393971587059907686521241)
                      ·
                        rfl

theorem cell23_4662243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_4662243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662243 prefixEnd_4662243 := by exact prefixLift 4662243
  have htrace : WordTrace (prefixWord ++ tailWord_4662243) baseStart_4662243 baseEnd_4662243 := by
    simpa [prefixWord, tailWord_4662243, baseEnd_4662243] using wordTrace_append hprefix tailTrace_4662243
  have hstable : (prefixWord ++ tailWord_4662243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662243).length < 2 ^ (prefixWord ++ tailWord_4662243).sum := by decide
  have hdescent : baseEnd_4662243 < baseStart_4662243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662266 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2]
def baseStart_4662266 : Nat := 118140960795 + 4662266 * 2 ^ 59
def prefixEnd_4662266 : Nat := 4983230072969 + 3 ^ 40 * 4662266 * 2
def baseEnd_4662266 : Nat := 2393983397114961096533635

theorem tailTrace_4662266 : CollatzResearch.WordTrace tailWord_4662266 prefixEnd_4662266 2393983397114961096533635 := by
  unfold tailWord_4662266
  simp only [CollatzResearch.WordTrace]
  refine ⟨42511702731853502121269663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113364540618276005656719101 42511702731853502121269663)
  ·
    refine ⟨63767554097780253181904495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42511702731853502121269663 63767554097780253181904495)
    ·
      refine ⟨95651331146670379772856743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63767554097780253181904495 95651331146670379772856743)
      ·
        refine ⟨143476996720005569659285115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95651331146670379772856743 143476996720005569659285115)
        ·
          refine ⟨215215495080008354488927673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143476996720005569659285115 215215495080008354488927673)
          ·
            refine ⟨161411621310006265866695755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215215495080008354488927673 161411621310006265866695755)
            ·
              refine ⟨242117431965009398800043633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161411621310006265866695755 242117431965009398800043633)
              ·
                refine ⟨181588073973757049100032725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242117431965009398800043633 181588073973757049100032725)
                ·
                  refine ⟨4255970483759930838282017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 181588073973757049100032725 4255970483759930838282017)
                  ·
                    refine ⟨3191977862819948128711513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4255970483759930838282017 3191977862819948128711513)
                    ·
                      refine ⟨2393983397114961096533635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3191977862819948128711513 2393983397114961096533635)
                      ·
                        rfl

theorem cell23_4662266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2].length) (baseStart_4662266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662266 prefixEnd_4662266 := by exact prefixLift 4662266
  have htrace : WordTrace (prefixWord ++ tailWord_4662266) baseStart_4662266 baseEnd_4662266 := by
    simpa [prefixWord, tailWord_4662266, baseEnd_4662266] using wordTrace_append hprefix tailTrace_4662266
  have hstable : (prefixWord ++ tailWord_4662266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662266).length < 2 ^ (prefixWord ++ tailWord_4662266).sum := by decide
  have hdescent : baseEnd_4662266 < baseStart_4662266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662283 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 3, 2, 2]
def baseStart_4662283 : Nat := 118140960795 + 4662283 * 2 ^ 59
def prefixEnd_4662283 : Nat := 4983230072969 + 3 ^ 40 * 4662283 * 2
def baseEnd_4662283 : Nat := 2393992126286087530021057

theorem tailTrace_4662283 : CollatzResearch.WordTrace tailWord_4662283 prefixEnd_4662283 2393992126286087530021057 := by
  unfold tailWord_4662283
  simp only [CollatzResearch.WordTrace]
  refine ⟨170047430968352420388447503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113364953978901613592298335 170047430968352420388447503)
  ·
    refine ⟨255071146452528630582671255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170047430968352420388447503 255071146452528630582671255)
    ·
      refine ⟨382606719678792945874006883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255071146452528630582671255 382606719678792945874006883)
      ·
        refine ⟨573910079518189418811010325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382606719678792945874006883 573910079518189418811010325)
        ·
          refine ⟨26902034977415129006766109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 573910079518189418811010325 26902034977415129006766109)
          ·
            refine ⟨10088263116530673377537291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26902034977415129006766109 10088263116530673377537291)
            ·
              refine ⟨15132394674796010066305937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10088263116530673377537291 15132394674796010066305937)
              ·
                refine ⟨11349296006097007549729453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15132394674796010066305937 11349296006097007549729453)
                ·
                  refine ⟨4255986002286377831148545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11349296006097007549729453 4255986002286377831148545)
                  ·
                    refine ⟨3191989501714783373361409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4255986002286377831148545 3191989501714783373361409)
                    ·
                      refine ⟨2393992126286087530021057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3191989501714783373361409 2393992126286087530021057)
                      ·
                        rfl

theorem cell23_4662283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 2, 2].length) (baseStart_4662283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662283 prefixEnd_4662283 := by exact prefixLift 4662283
  have htrace : WordTrace (prefixWord ++ tailWord_4662283) baseStart_4662283 baseEnd_4662283 := by
    simpa [prefixWord, tailWord_4662283, baseEnd_4662283] using wordTrace_append hprefix tailTrace_4662283
  have hstable : (prefixWord ++ tailWord_4662283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662283).length < 2 ^ (prefixWord ++ tailWord_4662283).sum := by decide
  have hdescent : baseEnd_4662283 < baseStart_4662283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662286 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_4662286 : Nat := 118140960795 + 4662286 * 2 ^ 59
def prefixEnd_4662286 : Nat := 4983230072969 + 3 ^ 40 * 4662286 * 2
def baseEnd_4662286 : Nat := 2393993666728051018283543

theorem tailTrace_4662286 : CollatzResearch.WordTrace tailWord_4662286 prefixEnd_4662286 2393993666728051018283543 := by
  unfold tailWord_4662286
  simp only [CollatzResearch.WordTrace]
  refine ⟨21255942548417693987600839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113365026924894367933871141 21255942548417693987600839)
  ·
    refine ⟨31883913822626540981401259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21255942548417693987600839 31883913822626540981401259)
    ·
      refine ⟨47825870733939811472101889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31883913822626540981401259 47825870733939811472101889)
      ·
        refine ⟨35869403050454858604076417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47825870733939811472101889 35869403050454858604076417)
        ·
          refine ⟨26902052287841143953057313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35869403050454858604076417 26902052287841143953057313)
          ·
            refine ⟨20176539215880857964792985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26902052287841143953057313 20176539215880857964792985)
            ·
              refine ⟨15132404411910643473594739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20176539215880857964792985 15132404411910643473594739)
              ·
                refine ⟨22698606617865965210392109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15132404411910643473594739 22698606617865965210392109)
                ·
                  refine ⟨8511977481699736953897041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22698606617865965210392109 8511977481699736953897041)
                  ·
                    refine ⟨6383983111274802715422781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8511977481699736953897041 6383983111274802715422781)
                    ·
                      refine ⟨2393993666728051018283543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6383983111274802715422781 2393993666728051018283543)
                      ·
                        rfl

theorem cell23_4662286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_4662286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662286 prefixEnd_4662286 := by exact prefixLift 4662286
  have htrace : WordTrace (prefixWord ++ tailWord_4662286) baseStart_4662286 baseEnd_4662286 := by
    simpa [prefixWord, tailWord_4662286, baseEnd_4662286] using wordTrace_append hprefix tailTrace_4662286
  have hstable : (prefixWord ++ tailWord_4662286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662286).length < 2 ^ (prefixWord ++ tailWord_4662286).sum := by decide
  have hdescent : baseEnd_4662286 < baseStart_4662286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662300 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_4662300 : Nat := 118140960795 + 4662300 * 2 ^ 59
def prefixEnd_4662300 : Nat := 4983230072969 + 3 ^ 40 * 4662300 * 2
def baseEnd_4662300 : Nat := 2394000855457213963508479

theorem tailTrace_4662300 : CollatzResearch.WordTrace tailWord_4662300 prefixEnd_4662300 2394000855457213963508479 := by
  unfold tailWord_4662300
  simp only [CollatzResearch.WordTrace]
  refine ⟨85024025504645416145908177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113365367339527221527877569 85024025504645416145908177)
  ·
    refine ⟨63768019128484062109431133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85024025504645416145908177 63768019128484062109431133)
    ·
      refine ⟨23913007173181523291036675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63768019128484062109431133 23913007173181523291036675)
      ·
        refine ⟨35869510759772284936555013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23913007173181523291036675 35869510759772284936555013)
        ·
          refine ⟨6725533267457303425604065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35869510759772284936555013 6725533267457303425604065)
          ·
            refine ⟨5044149950592977569203049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6725533267457303425604065 5044149950592977569203049)
            ·
              refine ⟨3783112462944733176902287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5044149950592977569203049 3783112462944733176902287)
              ·
                refine ⟨5674668694417099765353431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3783112462944733176902287 5674668694417099765353431)
                ·
                  refine ⟨8512003041625649648030147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5674668694417099765353431 8512003041625649648030147)
                  ·
                    refine ⟨12768004562438474472045221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8512003041625649648030147 12768004562438474472045221)
                    ·
                      refine ⟨2394000855457213963508479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12768004562438474472045221 2394000855457213963508479)
                      ·
                        rfl

theorem cell23_4662300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_4662300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662300 prefixEnd_4662300 := by exact prefixLift 4662300
  have htrace : WordTrace (prefixWord ++ tailWord_4662300) baseStart_4662300 baseEnd_4662300 := by
    simpa [prefixWord, tailWord_4662300, baseEnd_4662300] using wordTrace_append hprefix tailTrace_4662300
  have hstable : (prefixWord ++ tailWord_4662300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662300).length < 2 ^ (prefixWord ++ tailWord_4662300).sum := by decide
  have hdescent : baseEnd_4662300 < baseStart_4662300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662303 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 1, 2, 3]
def baseStart_4662303 : Nat := 118140960795 + 4662303 * 2 ^ 59
def prefixEnd_4662303 : Nat := 4983230072969 + 3 ^ 40 * 4662303 * 2
def baseEnd_4662303 : Nat := 2394002395899177451770965

theorem tailTrace_4662303 : CollatzResearch.WordTrace tailWord_4662303 prefixEnd_4662303 2394002395899177451770965 := by
  unfold tailWord_4662303
  simp only [CollatzResearch.WordTrace]
  refine ⟨170048160428279963804175563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113365440285519975869450375 170048160428279963804175563)
  ·
    refine ⟨255072240642419945706263345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170048160428279963804175563 255072240642419945706263345)
    ·
      refine ⟨191304180481814959279697509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255072240642419945706263345 191304180481814959279697509)
      ·
        refine ⟨35869533840340304864943283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191304180481814959279697509 35869533840340304864943283)
        ·
          refine ⟨53804300760510457297414925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35869533840340304864943283 53804300760510457297414925)
          ·
            refine ⟨20176612785191421486530597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53804300760510457297414925 20176612785191421486530597)
            ·
              refine ⟨3783114897223391528724487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20176612785191421486530597 3783114897223391528724487)
              ·
                refine ⟨5674672345835087293086731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3783114897223391528724487 5674672345835087293086731)
                ·
                  refine ⟨8512008518752630939630097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5674672345835087293086731 8512008518752630939630097)
                  ·
                    refine ⟨6384006389064473204722573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8512008518752630939630097 6384006389064473204722573)
                    ·
                      refine ⟨2394002395899177451770965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6384006389064473204722573 2394002395899177451770965)
                      ·
                        rfl

theorem cell23_4662303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_4662303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662303 prefixEnd_4662303 := by exact prefixLift 4662303
  have htrace : WordTrace (prefixWord ++ tailWord_4662303) baseStart_4662303 baseEnd_4662303 := by
    simpa [prefixWord, tailWord_4662303, baseEnd_4662303] using wordTrace_append hprefix tailTrace_4662303
  have hstable : (prefixWord ++ tailWord_4662303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662303).length < 2 ^ (prefixWord ++ tailWord_4662303).sum := by decide
  have hdescent : baseEnd_4662303 < baseStart_4662303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662316 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 3]
def baseStart_4662316 : Nat := 118140960795 + 4662316 * 2 ^ 59
def prefixEnd_4662316 : Nat := 4983230072969 + 3 ^ 40 * 4662316 * 2
def baseEnd_4662316 : Nat := 2394009071147685900908405

theorem tailTrace_4662316 : CollatzResearch.WordTrace tailWord_4662316 prefixEnd_4662316 2394009071147685900908405 := by
  unfold tailWord_4662316
  simp only [CollatzResearch.WordTrace]
  refine ⟨85024317288616433512199401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113365756384821911349599201 85024317288616433512199401)
  ·
    refine ⟨63768237966462325134149551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85024317288616433512199401 63768237966462325134149551)
    ·
      refine ⟨95652356949693487701224327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63768237966462325134149551 95652356949693487701224327)
      ·
        refine ⟨143478535424540231551836491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95652356949693487701224327 143478535424540231551836491)
        ·
          refine ⟨215217803136810347327754737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143478535424540231551836491 215217803136810347327754737)
          ·
            refine ⟨161413352352607760495816053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215217803136810347327754737 161413352352607760495816053)
            ·
              refine ⟨15132501783056977546482755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 161413352352607760495816053 15132501783056977546482755)
              ·
                refine ⟨22698752674585466319724133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15132501783056977546482755 22698752674585466319724133)
                ·
                  refine ⟨4256016126484774934948275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22698752674585466319724133 4256016126484774934948275)
                  ·
                    refine ⟨6384024189727162402422413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4256016126484774934948275 6384024189727162402422413)
                    ·
                      refine ⟨2394009071147685900908405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6384024189727162402422413 2394009071147685900908405)
                      ·
                        rfl

theorem cell23_4662316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_4662316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662316 prefixEnd_4662316 := by exact prefixLift 4662316
  have htrace : WordTrace (prefixWord ++ tailWord_4662316) baseStart_4662316 baseEnd_4662316 := by
    simpa [prefixWord, tailWord_4662316, baseEnd_4662316] using wordTrace_append hprefix tailTrace_4662316
  have hstable : (prefixWord ++ tailWord_4662316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662316).length < 2 ^ (prefixWord ++ tailWord_4662316).sum := by decide
  have hdescent : baseEnd_4662316 < baseStart_4662316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662333 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_4662333 : Nat := 118140960795 + 4662333 * 2 ^ 59
def prefixEnd_4662333 : Nat := 4983230072969 + 3 ^ 40 * 4662333 * 2
def baseEnd_4662333 : Nat := 2394017800318812334395827

theorem tailTrace_4662333 : CollatzResearch.WordTrace tailWord_4662333 prefixEnd_4662333 2394017800318812334395827 := by
  unfold tailWord_4662333
  simp only [CollatzResearch.WordTrace]
  refine ⟨170049254618171278927767653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113366169745447519285178435 170049254618171278927767653)
  ·
    refine ⟨31884235240907114798956435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170049254618171278927767653 31884235240907114798956435)
    ·
      refine ⟨47826352861360672198434653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31884235240907114798956435 47826352861360672198434653)
      ·
        refine ⟨17934882323010252074412995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47826352861360672198434653 17934882323010252074412995)
        ·
          refine ⟨26902323484515378111619493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17934882323010252074412995 26902323484515378111619493)
          ·
            refine ⟨5044185653346633395928655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26902323484515378111619493 5044185653346633395928655)
            ·
              refine ⟨7566278480019950093892983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5044185653346633395928655 7566278480019950093892983)
              ·
                refine ⟨11349417720029925140839475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7566278480019950093892983 11349417720029925140839475)
                ·
                  refine ⟨17024126580044887711259213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11349417720029925140839475 17024126580044887711259213)
                  ·
                    refine ⟨6384047467516832891722205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17024126580044887711259213 6384047467516832891722205)
                    ·
                      refine ⟨2394017800318812334395827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6384047467516832891722205 2394017800318812334395827)
                      ·
                        rfl

theorem cell23_4662333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_4662333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662333 prefixEnd_4662333 := by exact prefixLift 4662333
  have htrace : WordTrace (prefixWord ++ tailWord_4662333) baseStart_4662333 baseEnd_4662333 := by
    simpa [prefixWord, tailWord_4662333, baseEnd_4662333] using wordTrace_append hprefix tailTrace_4662333
  have hstable : (prefixWord ++ tailWord_4662333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662333).length < 2 ^ (prefixWord ++ tailWord_4662333).sum := by decide
  have hdescent : baseEnd_4662333 < baseStart_4662333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662343 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 1, 3, 2]
def baseStart_4662343 : Nat := 118140960795 + 4662343 * 2 ^ 59
def prefixEnd_4662343 : Nat := 4983230072969 + 3 ^ 40 * 4662343 * 2
def baseEnd_4662343 : Nat := 2394022935125357295270781

theorem tailTrace_4662343 : CollatzResearch.WordTrace tailWord_4662343 prefixEnd_4662343 2394022935125357295270781 := by
  unfold tailWord_4662343
  simp only [CollatzResearch.WordTrace]
  refine ⟨170049619348135050635631683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113366412898756700423754455 170049619348135050635631683)
  ·
    refine ⟨255074429022202575953447525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170049619348135050635631683 255074429022202575953447525)
    ·
      refine ⟨47826455441662982991271411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255074429022202575953447525 47826455441662982991271411)
      ·
        refine ⟨71739683162494474486907117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47826455441662982991271411 71739683162494474486907117)
        ·
          refine ⟨26902381185935427932590169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71739683162494474486907117 26902381185935427932590169)
          ·
            refine ⟨20176785889451570949442627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26902381185935427932590169 20176785889451570949442627)
            ·
              refine ⟨30265178834177356424163941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20176785889451570949442627 30265178834177356424163941)
              ·
                refine ⟨5674721031408254329530739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30265178834177356424163941 5674721031408254329530739)
                ·
                  refine ⟨8512081547112381494296109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5674721031408254329530739 8512081547112381494296109)
                  ·
                    refine ⟨3192030580167143060361041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8512081547112381494296109 3192030580167143060361041)
                    ·
                      refine ⟨2394022935125357295270781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192030580167143060361041 2394022935125357295270781)
                      ·
                        rfl

theorem cell23_4662343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_4662343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662343 prefixEnd_4662343 := by exact prefixLift 4662343
  have htrace : WordTrace (prefixWord ++ tailWord_4662343) baseStart_4662343 baseEnd_4662343 := by
    simpa [prefixWord, tailWord_4662343, baseEnd_4662343] using wordTrace_append hprefix tailTrace_4662343
  have hstable : (prefixWord ++ tailWord_4662343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662343).length < 2 ^ (prefixWord ++ tailWord_4662343).sum := by decide
  have hdescent : baseEnd_4662343 < baseStart_4662343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662359 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 3]
def baseStart_4662359 : Nat := 118140960795 + 4662359 * 2 ^ 59
def prefixEnd_4662359 : Nat := 4983230072969 + 3 ^ 40 * 4662359 * 2
def baseEnd_4662359 : Nat := 2394031150815829232670707

theorem tailTrace_4662359 : CollatzResearch.WordTrace tailWord_4662359 prefixEnd_4662359 2394031150815829232670707 := by
  unfold tailWord_4662359
  simp only [CollatzResearch.WordTrace]
  refine ⟨170050202916077085368214131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113366801944051390245476087 170050202916077085368214131)
  ·
    refine ⟨255075304374115628052321197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170050202916077085368214131 255075304374115628052321197)
    ·
      refine ⟨95653239140293360519620449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255075304374115628052321197 95653239140293360519620449)
      ·
        refine ⟨71739929355220020389715337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95653239140293360519620449 71739929355220020389715337)
        ·
          refine ⟨53804947016415015292286503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71739929355220020389715337 53804947016415015292286503)
          ·
            refine ⟨80707420524622522938429755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53804947016415015292286503 80707420524622522938429755)
            ·
              refine ⟨121061130786933784407644633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80707420524622522938429755 121061130786933784407644633)
              ·
                refine ⟨90795848090200338305733475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121061130786933784407644633 90795848090200338305733475)
                ·
                  refine ⟨136193772135300507458600213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90795848090200338305733475 136193772135300507458600213)
                  ·
                    refine ⟨6384083068842211287121885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 136193772135300507458600213 6384083068842211287121885)
                    ·
                      refine ⟨2394031150815829232670707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6384083068842211287121885 2394031150815829232670707)
                      ·
                        rfl

theorem cell23_4662359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_4662359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662359 prefixEnd_4662359 := by exact prefixLift 4662359
  have htrace : WordTrace (prefixWord ++ tailWord_4662359) baseStart_4662359 baseEnd_4662359 := by
    simpa [prefixWord, tailWord_4662359, baseEnd_4662359] using wordTrace_append hprefix tailTrace_4662359
  have hstable : (prefixWord ++ tailWord_4662359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662359).length < 2 ^ (prefixWord ++ tailWord_4662359).sum := by decide
  have hdescent : baseEnd_4662359 < baseStart_4662359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662369 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_4662369 : Nat := 118140960795 + 4662369 * 2 ^ 59
def prefixEnd_4662369 : Nat := 4983230072969 + 3 ^ 40 * 4662369 * 2
def baseEnd_4662369 : Nat := 2394036285622374193545661

theorem tailTrace_4662369 : CollatzResearch.WordTrace tailWord_4662369 prefixEnd_4662369 2394036285622374193545661 := by
  unfold tailWord_4662369
  simp only [CollatzResearch.WordTrace]
  refine ⟨170050567646040857076078161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113367045097360571384052107 170050567646040857076078161)
  ·
    refine ⟨127537925734530642807058621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170050567646040857076078161 127537925734530642807058621)
    ·
      refine ⟨47826722150448991052646983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127537925734530642807058621 47826722150448991052646983)
      ·
        refine ⟨71740083225673486578970475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47826722150448991052646983 71740083225673486578970475)
        ·
          refine ⟨107610124838510229868455713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71740083225673486578970475 107610124838510229868455713)
          ·
            refine ⟨80707593628882672401341785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107610124838510229868455713 80707593628882672401341785)
            ·
              refine ⟨60530695221662004301006339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80707593628882672401341785 60530695221662004301006339)
              ·
                refine ⟨90796042832493006451509509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60530695221662004301006339 90796042832493006451509509)
                ·
                  refine ⟨17024258031092438709658033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90796042832493006451509509 17024258031092438709658033)
                  ·
                    refine ⟨12768193523319329032243525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17024258031092438709658033 12768193523319329032243525)
                    ·
                      refine ⟨2394036285622374193545661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12768193523319329032243525 2394036285622374193545661)
                      ·
                        rfl

theorem cell23_4662369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_4662369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662369 prefixEnd_4662369 := by exact prefixLift 4662369
  have htrace : WordTrace (prefixWord ++ tailWord_4662369) baseStart_4662369 baseEnd_4662369 := by
    simpa [prefixWord, tailWord_4662369, baseEnd_4662369] using wordTrace_append hprefix tailTrace_4662369
  have hstable : (prefixWord ++ tailWord_4662369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662369).length < 2 ^ (prefixWord ++ tailWord_4662369).sum := by decide
  have hdescent : baseEnd_4662369 < baseStart_4662369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662373 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 4, 2, 2]
def baseStart_4662373 : Nat := 118140960795 + 4662373 * 2 ^ 59
def prefixEnd_4662373 : Nat := 4983230072969 + 3 ^ 40 * 4662373 * 2
def baseEnd_4662373 : Nat := 2394038339544992177895643

theorem tailTrace_4662373 : CollatzResearch.WordTrace tailWord_4662373 prefixEnd_4662373 2394038339544992177895643 := by
  unfold tailWord_4662373
  simp only [CollatzResearch.WordTrace]
  refine ⟨170050713538026365759223773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113367142358684243839482515 170050713538026365759223773)
  ·
    refine ⟨63769017576759887159708915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170050713538026365759223773 63769017576759887159708915)
    ·
      refine ⟨95653526365139830739563373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63769017576759887159708915 95653526365139830739563373)
      ·
        refine ⟨35870072386927436527336265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95653526365139830739563373 35870072386927436527336265)
        ·
          refine ⟨26902554290195577395502199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35870072386927436527336265 26902554290195577395502199)
          ·
            refine ⟨40353831435293366093253299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26902554290195577395502199 40353831435293366093253299)
            ·
              refine ⟨60530747152940049139879949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40353831435293366093253299 60530747152940049139879949)
              ·
                refine ⟨22699030182352518427454981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60530747152940049139879949 22699030182352518427454981)
                ·
                  refine ⟨4256068159191097205147809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22699030182352518427454981 4256068159191097205147809)
                  ·
                    refine ⟨3192051119393322903860857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4256068159191097205147809 3192051119393322903860857)
                    ·
                      refine ⟨2394038339544992177895643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192051119393322903860857 2394038339544992177895643)
                      ·
                        rfl

theorem cell23_4662373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_4662373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662373 prefixEnd_4662373 := by exact prefixLift 4662373
  have htrace : WordTrace (prefixWord ++ tailWord_4662373) baseStart_4662373 baseEnd_4662373 := by
    simpa [prefixWord, tailWord_4662373, baseEnd_4662373] using wordTrace_append hprefix tailTrace_4662373
  have hstable : (prefixWord ++ tailWord_4662373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662373).length < 2 ^ (prefixWord ++ tailWord_4662373).sum := by decide
  have hdescent : baseEnd_4662373 < baseStart_4662373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662419 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 5]
def baseStart_4662419 : Nat := 118140960795 + 4662419 * 2 ^ 59
def prefixEnd_4662419 : Nat := 4983230072969 + 3 ^ 40 * 4662419 * 2
def baseEnd_4662419 : Nat := 2394061959655098997920431

theorem tailTrace_4662419 : CollatzResearch.WordTrace tailWord_4662419 prefixEnd_4662419 2394061959655098997920431 := by
  unfold tailWord_4662419
  simp only [CollatzResearch.WordTrace]
  refine ⟨170052391295859715615398311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113368260863906477076932207 170052391295859715615398311)
  ·
    refine ⟨255078586943789573423097467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170052391295859715615398311 255078586943789573423097467)
    ·
      refine ⟨382617880415684360134646201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255078586943789573423097467 382617880415684360134646201)
      ·
        refine ⟨286963410311763270100984651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382617880415684360134646201 286963410311763270100984651)
        ·
          refine ⟨430445115467644905151476977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286963410311763270100984651 430445115467644905151476977)
          ·
            refine ⟨322833836600733678863607733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430445115467644905151476977 322833836600733678863607733)
            ·
              refine ⟨30265672181318782393463225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 322833836600733678863607733 30265672181318782393463225)
              ·
                refine ⟨22699254135989086795097419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30265672181318782393463225 22699254135989086795097419)
                ·
                  refine ⟨34048881203983630192646129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22699254135989086795097419 34048881203983630192646129)
                  ·
                    refine ⟨25536660902987722644484597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34048881203983630192646129 25536660902987722644484597)
                    ·
                      refine ⟨2394061959655098997920431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25536660902987722644484597 2394061959655098997920431)
                      ·
                        rfl

theorem cell23_4662419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_4662419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662419 prefixEnd_4662419 := by exact prefixLift 4662419
  have htrace : WordTrace (prefixWord ++ tailWord_4662419) baseStart_4662419 baseEnd_4662419 := by
    simpa [prefixWord, tailWord_4662419, baseEnd_4662419] using wordTrace_append hprefix tailTrace_4662419
  have hstable : (prefixWord ++ tailWord_4662419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662419).length < 2 ^ (prefixWord ++ tailWord_4662419).sum := by decide
  have hdescent : baseEnd_4662419 < baseStart_4662419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662430 : List Nat := [4, 3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_4662430 : Nat := 118140960795 + 4662430 * 2 ^ 59
def prefixEnd_4662430 : Nat := 4983230072969 + 3 ^ 40 * 4662430 * 2
def baseEnd_4662430 : Nat := 266007511993588717209209

theorem tailTrace_4662430 : CollatzResearch.WordTrace tailWord_4662430 prefixEnd_4662430 266007511993588717209209 := by
  unfold tailWord_4662430
  simp only [CollatzResearch.WordTrace]
  refine ⟨21256599062352483061756093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113368528332546576329365829 21256599062352483061756093)
  ·
    refine ⟨7971224648382181148158535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21256599062352483061756093 7971224648382181148158535)
    ·
      refine ⟨11956836972573271722237803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7971224648382181148158535 11956836972573271722237803)
      ·
        refine ⟨17935255458859907583356705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11956836972573271722237803 17935255458859907583356705)
        ·
          refine ⟨13451441594144930687517529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17935255458859907583356705 13451441594144930687517529)
          ·
            refine ⟨10088581195608698015638147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13451441594144930687517529 10088581195608698015638147)
            ·
              refine ⟨15132871793413047023457221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10088581195608698015638147 15132871793413047023457221)
              ·
                refine ⟨2837413461264946316898229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15132871793413047023457221 2837413461264946316898229)
                ·
                  refine ⟨266007511993588717209209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2837413461264946316898229 266007511993588717209209)
                  ·
                    rfl

theorem cell23_4662430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_4662430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662430 prefixEnd_4662430 := by exact prefixLift 4662430
  have htrace : WordTrace (prefixWord ++ tailWord_4662430) baseStart_4662430 baseEnd_4662430 := by
    simpa [prefixWord, tailWord_4662430, baseEnd_4662430] using wordTrace_append hprefix tailTrace_4662430
  have hstable : (prefixWord ++ tailWord_4662430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662430).length < 2 ^ (prefixWord ++ tailWord_4662430).sum := by decide
  have hdescent : baseEnd_4662430 < baseStart_4662430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662436 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_4662436 : Nat := 118140960795 + 4662436 * 2 ^ 59
def prefixEnd_4662436 : Nat := 4983230072969 + 3 ^ 40 * 4662436 * 2
def baseEnd_4662436 : Nat := 2394070688826225431407853

theorem tailTrace_4662436 : CollatzResearch.WordTrace tailWord_4662436 prefixEnd_4662436 2394070688826225431407853 := by
  unfold tailWord_4662436
  simp only [CollatzResearch.WordTrace]
  refine ⟨85026505668399063759383581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113368674224532085012511441 85026505668399063759383581)
  ·
    refine ⟨31884939625649648909768843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85026505668399063759383581 31884939625649648909768843)
    ·
      refine ⟨47827409438474473364653265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31884939625649648909768843 47827409438474473364653265)
      ·
        refine ⟨35870557078855855023489949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47827409438474473364653265 35870557078855855023489949)
        ·
          refine ⟨13451458904570945633808731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35870557078855855023489949 13451458904570945633808731)
          ·
            refine ⟨20177188356856418450713097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13451458904570945633808731 20177188356856418450713097)
            ·
              refine ⟨15132891267642313838034823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20177188356856418450713097 15132891267642313838034823)
              ·
                refine ⟨22699336901463470757052235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15132891267642313838034823 22699336901463470757052235)
                ·
                  refine ⟨34049005352195206135578353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22699336901463470757052235 34049005352195206135578353)
                  ·
                    refine ⟨25536754014146404601683765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34049005352195206135578353 25536754014146404601683765)
                    ·
                      refine ⟨2394070688826225431407853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25536754014146404601683765 2394070688826225431407853)
                      ·
                        rfl

theorem cell23_4662436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_4662436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662436 prefixEnd_4662436 := by exact prefixLift 4662436
  have htrace : WordTrace (prefixWord ++ tailWord_4662436) baseStart_4662436 baseEnd_4662436 := by
    simpa [prefixWord, tailWord_4662436, baseEnd_4662436] using wordTrace_append hprefix tailTrace_4662436
  have hstable : (prefixWord ++ tailWord_4662436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662436).length < 2 ^ (prefixWord ++ tailWord_4662436).sum := by decide
  have hdescent : baseEnd_4662436 < baseStart_4662436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662459 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 4]
def baseStart_4662459 : Nat := 118140960795 + 4662459 * 2 ^ 59
def prefixEnd_4662459 : Nat := 4983230072969 + 3 ^ 40 * 4662459 * 2
def baseEnd_4662459 : Nat := 2394082498881278841420247

theorem tailTrace_4662459 : CollatzResearch.WordTrace tailWord_4662459 prefixEnd_4662459 2394082498881278841420247 := by
  unfold tailWord_4662459
  simp only [CollatzResearch.WordTrace]
  refine ⟨170053850215714802446854431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113369233477143201631236287 170053850215714802446854431)
  ·
    refine ⟨255080775323572203670281647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170053850215714802446854431 255080775323572203670281647)
    ·
      refine ⟨382621162985358305505422471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255080775323572203670281647 382621162985358305505422471)
      ·
        refine ⟨573931744478037458258133707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382621162985358305505422471 573931744478037458258133707)
        ·
          refine ⟨860897616717056187387200561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573931744478037458258133707 860897616717056187387200561)
          ·
            refine ⟨645673212537792140540400421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860897616717056187387200561 645673212537792140540400421)
            ·
              refine ⟨121063727350836026351325079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 645673212537792140540400421 121063727350836026351325079)
              ·
                refine ⟨181595591026254039526987619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121063727350836026351325079 181595591026254039526987619)
                ·
                  refine ⟨272393386539381059290481429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181595591026254039526987619 272393386539381059290481429)
                  ·
                    refine ⟨12768439994033487154241317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 272393386539381059290481429 12768439994033487154241317)
                    ·
                      refine ⟨2394082498881278841420247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12768439994033487154241317 2394082498881278841420247)
                      ·
                        rfl

theorem cell23_4662459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 4].length) (baseStart_4662459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662459 prefixEnd_4662459 := by exact prefixLift 4662459
  have htrace : WordTrace (prefixWord ++ tailWord_4662459) baseStart_4662459 baseEnd_4662459 := by
    simpa [prefixWord, tailWord_4662459, baseEnd_4662459] using wordTrace_append hprefix tailTrace_4662459
  have hstable : (prefixWord ++ tailWord_4662459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662459).length < 2 ^ (prefixWord ++ tailWord_4662459).sum := by decide
  have hdescent : baseEnd_4662459 < baseStart_4662459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662469 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 8]
def baseStart_4662469 : Nat := 118140960795 + 4662469 * 2 ^ 59
def prefixEnd_4662469 : Nat := 4983230072969 + 3 ^ 40 * 4662469 * 2
def baseEnd_4662469 : Nat := 266009737076424866921689

theorem tailTrace_4662469 : CollatzResearch.WordTrace tailWord_4662469 prefixEnd_4662469 266009737076424866921689 := by
  unfold tailWord_4662469
  simp only [CollatzResearch.WordTrace]
  refine ⟨170054214945678574154718461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113369476630452382769812307 170054214945678574154718461)
  ·
    refine ⟨63770330604629465308019423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170054214945678574154718461 63770330604629465308019423)
    ·
      refine ⟨95655495906944197962029135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63770330604629465308019423 95655495906944197962029135)
      ·
        refine ⟨143483243860416296943043703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95655495906944197962029135 143483243860416296943043703)
        ·
          refine ⟨215224865790624445414565555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143483243860416296943043703 215224865790624445414565555)
          ·
            refine ⟨322837298685936668121848333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215224865790624445414565555 322837298685936668121848333)
            ·
              refine ⟨121063987007226250545693125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 322837298685936668121848333 121063987007226250545693125)
              ·
                refine ⟨22699497563854921977317461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121063987007226250545693125 22699497563854921977317461)
                ·
                  refine ⟨266009737076424866921689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22699497563854921977317461 266009737076424866921689)
                  ·
                    rfl

theorem cell23_4662469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_4662469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662469 prefixEnd_4662469 := by exact prefixLift 4662469
  have htrace : WordTrace (prefixWord ++ tailWord_4662469) baseStart_4662469 baseEnd_4662469 := by
    simpa [prefixWord, tailWord_4662469, baseEnd_4662469] using wordTrace_append hprefix tailTrace_4662469
  have hstable : (prefixWord ++ tailWord_4662469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662469).length < 2 ^ (prefixWord ++ tailWord_4662469).sum := by decide
  have hdescent : baseEnd_4662469 < baseStart_4662469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662524 : List Nat := [2, 2, 2, 1, 6, 1, 1, 3, 1, 4]
def baseStart_4662524 : Nat := 118140960795 + 4662524 * 2 ^ 59
def prefixEnd_4662524 : Nat := 4983230072969 + 3 ^ 40 * 4662524 * 2
def baseEnd_4662524 : Nat := 798038625041273695702483

theorem tailTrace_4662524 : CollatzResearch.WordTrace tailWord_4662524 prefixEnd_4662524 798038625041273695702483 := by
  unfold tailWord_4662524
  simp only [CollatzResearch.WordTrace]
  refine ⟨85028110480239659273985313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113370813973652879031980417 85028110480239659273985313)
  ·
    refine ⟨63771082860179744455488985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85028110480239659273985313 63771082860179744455488985)
    ·
      refine ⟨47828312145134808341616739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63771082860179744455488985 47828312145134808341616739)
      ·
        refine ⟨71742468217702212512425109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47828312145134808341616739 71742468217702212512425109)
        ·
          refine ⟨3362928197704791211519927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71742468217702212512425109 3362928197704791211519927)
          ·
            refine ⟨5044392296557186817279891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3362928197704791211519927 5044392296557186817279891)
            ·
              refine ⟨7566588444835780225919837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5044392296557186817279891 7566588444835780225919837)
              ·
                refine ⟨2837470666813417584719939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7566588444835780225919837 2837470666813417584719939)
                ·
                  refine ⟨4256206000220126377079909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837470666813417584719939 4256206000220126377079909)
                  ·
                    refine ⟨798038625041273695702483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4256206000220126377079909 798038625041273695702483)
                    ·
                      rfl

theorem cell23_4662524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_4662524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662524 prefixEnd_4662524 := by exact prefixLift 4662524
  have htrace : WordTrace (prefixWord ++ tailWord_4662524) baseStart_4662524 baseEnd_4662524 := by
    simpa [prefixWord, tailWord_4662524, baseEnd_4662524] using wordTrace_append hprefix tailTrace_4662524
  have hstable : (prefixWord ++ tailWord_4662524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662524).length < 2 ^ (prefixWord ++ tailWord_4662524).sum := by decide
  have hdescent : baseEnd_4662524 < baseStart_4662524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662540 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 2, 3, 2]
def baseStart_4662540 : Nat := 118140960795 + 4662540 * 2 ^ 59
def prefixEnd_4662540 : Nat := 4983230072969 + 3 ^ 40 * 4662540 * 2
def baseEnd_4662540 : Nat := 2394124090814293024507375

theorem tailTrace_4662540 : CollatzResearch.WordTrace tailWord_4662540 prefixEnd_4662540 2394124090814293024507375 := by
  unfold tailWord_4662540
  simp only [CollatzResearch.WordTrace]
  refine ⟨85028402264210676640276537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113371203018947568853702049 85028402264210676640276537)
  ·
    refine ⟨63771301698158007480207403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85028402264210676640276537 63771301698158007480207403)
    ·
      refine ⟨95656952547237011220311105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63771301698158007480207403 95656952547237011220311105)
      ·
        refine ⟨71742714410427758415233329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95656952547237011220311105 71742714410427758415233329)
        ·
          refine ⟨53807035807820818811424997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71742714410427758415233329 53807035807820818811424997)
          ·
            refine ⟨10088819213966403527142187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53807035807820818811424997 10088819213966403527142187)
            ·
              refine ⟨15133228820949605290713281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10088819213966403527142187 15133228820949605290713281)
              ·
                refine ⟨11349921615712203968034961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15133228820949605290713281 11349921615712203968034961)
                ·
                  refine ⟨8512441211784152976026221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11349921615712203968034961 8512441211784152976026221)
                  ·
                    refine ⟨3192165454419057366009833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8512441211784152976026221 3192165454419057366009833)
                    ·
                      refine ⟨2394124090814293024507375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192165454419057366009833 2394124090814293024507375)
                      ·
                        rfl

theorem cell23_4662540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_4662540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662540 prefixEnd_4662540 := by exact prefixLift 4662540
  have htrace : WordTrace (prefixWord ++ tailWord_4662540) baseStart_4662540 baseEnd_4662540 := by
    simpa [prefixWord, tailWord_4662540, baseEnd_4662540] using wordTrace_append hprefix tailTrace_4662540
  have hstable : (prefixWord ++ tailWord_4662540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662540).length < 2 ^ (prefixWord ++ tailWord_4662540).sum := by decide
  have hdescent : baseEnd_4662540 < baseStart_4662540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662570 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4662570 : Nat := 118140960795 + 4662570 * 2 ^ 59
def prefixEnd_4662570 : Nat := 4983230072969 + 3 ^ 40 * 4662570 * 2
def baseEnd_4662570 : Nat := 2394139495233927907132237

theorem tailTrace_4662570 : CollatzResearch.WordTrace tailWord_4662570 prefixEnd_4662570 2394139495233927907132237 := by
  unfold tailWord_4662570
  simp only [CollatzResearch.WordTrace]
  refine ⟨42514474679578167101036291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113371932478875112269430109 42514474679578167101036291)
  ·
    refine ⟨63771712019367250651554437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42514474679578167101036291 63771712019367250651554437)
    ·
      refine ⟨11957196003631359497166457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63771712019367250651554437 11957196003631359497166457)
      ·
        refine ⟨8967897002723519622874843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11957196003631359497166457 8967897002723519622874843)
        ·
          refine ⟨13451845504085279434312265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8967897002723519622874843 13451845504085279434312265)
          ·
            refine ⟨10088884128063959575734199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13451845504085279434312265 10088884128063959575734199)
            ·
              refine ⟨15133326192095939363601299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10088884128063959575734199 15133326192095939363601299)
              ·
                refine ⟨22699989288143909045401949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15133326192095939363601299 22699989288143909045401949)
                ·
                  refine ⟨8512495983053965892025731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22699989288143909045401949 8512495983053965892025731)
                  ·
                    refine ⟨12768743974580948838038597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8512495983053965892025731 12768743974580948838038597)
                    ·
                      refine ⟨2394139495233927907132237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12768743974580948838038597 2394139495233927907132237)
                      ·
                        rfl

theorem cell23_4662570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4662570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662570 prefixEnd_4662570 := by exact prefixLift 4662570
  have htrace : WordTrace (prefixWord ++ tailWord_4662570) baseStart_4662570 baseEnd_4662570 := by
    simpa [prefixWord, tailWord_4662570, baseEnd_4662570] using wordTrace_append hprefix tailTrace_4662570
  have hstable : (prefixWord ++ tailWord_4662570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662570).length < 2 ^ (prefixWord ++ tailWord_4662570).sum := by decide
  have hdescent : baseEnd_4662570 < baseStart_4662570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662598 : List Nat := [6, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4662598 : Nat := 118140960795 + 4662598 * 2 ^ 59
def prefixEnd_4662598 : Nat := 4983230072969 + 3 ^ 40 * 4662598 * 2
def baseEnd_4662598 : Nat := 2394153872692253797582109

theorem tailTrace_4662598 : CollatzResearch.WordTrace tailWord_4662598 prefixEnd_4662598 2394153872692253797582109 := by
  unfold tailWord_4662598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5314341248819100912067639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113372613308140819457442965 5314341248819100912067639)
  ·
    refine ⟨7971511873228651368101459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5314341248819100912067639 7971511873228651368101459)
    ·
      refine ⟨11957267809842977052152189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7971511873228651368101459 11957267809842977052152189)
      ·
        refine ⟨4483975428691116394557071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11957267809842977052152189 4483975428691116394557071)
        ·
          refine ⟨6725963143036674591835607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4483975428691116394557071 6725963143036674591835607)
          ·
            refine ⟨10088944714555011887753411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6725963143036674591835607 10088944714555011887753411)
            ·
              refine ⟨15133417071832517831630117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10088944714555011887753411 15133417071832517831630117)
              ·
                refine ⟨2837515700968597093430647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15133417071832517831630117 2837515700968597093430647)
                ·
                  refine ⟨4256273551452895640145971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837515700968597093430647 4256273551452895640145971)
                  ·
                    refine ⟨6384410327179343460218957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4256273551452895640145971 6384410327179343460218957)
                    ·
                      refine ⟨2394153872692253797582109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6384410327179343460218957 2394153872692253797582109)
                      ·
                        rfl

theorem cell23_4662598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4662598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662598 prefixEnd_4662598 := by exact prefixLift 4662598
  have htrace : WordTrace (prefixWord ++ tailWord_4662598) baseStart_4662598 baseEnd_4662598 := by
    simpa [prefixWord, tailWord_4662598, baseEnd_4662598] using wordTrace_append hprefix tailTrace_4662598
  have hstable : (prefixWord ++ tailWord_4662598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662598).length < 2 ^ (prefixWord ++ tailWord_4662598).sum := by decide
  have hdescent : baseEnd_4662598 < baseStart_4662598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662603 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 8, 1, 3]
def baseStart_4662603 : Nat := 118140960795 + 4662603 * 2 ^ 59
def prefixEnd_4662603 : Nat := 4983230072969 + 3 ^ 40 * 4662603 * 2
def baseEnd_4662603 : Nat := 2394156440095526278019585

theorem tailTrace_4662603 : CollatzResearch.WordTrace tailWord_4662603 prefixEnd_4662603 2394156440095526278019585 := by
  unfold tailWord_4662603
  simp only [CollatzResearch.WordTrace]
  refine ⟨170059102327193115040096463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113372734884795410026730975 170059102327193115040096463)
  ·
    refine ⟨255088653490789672560144695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170059102327193115040096463 255088653490789672560144695)
    ·
      refine ⟨382632980236184508840217043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255088653490789672560144695 382632980236184508840217043)
      ·
        refine ⟨573949470354276763260325565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382632980236184508840217043 573949470354276763260325565)
        ·
          refine ⟨215231051382853786222622087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 573949470354276763260325565 215231051382853786222622087)
          ·
            refine ⟨322846577074280679333933131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215231051382853786222622087 322846577074280679333933131)
            ·
              refine ⟨484269865611421019000899697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322846577074280679333933131 484269865611421019000899697)
              ·
                refine ⟨363202399208565764250674773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484269865611421019000899697 363202399208565764250674773)
                ·
                  refine ⟨4256278115725380049812595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 363202399208565764250674773 4256278115725380049812595)
                  ·
                    refine ⟨6384417173588070074718893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4256278115725380049812595 6384417173588070074718893)
                    ·
                      refine ⟨2394156440095526278019585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6384417173588070074718893 2394156440095526278019585)
                      ·
                        rfl

theorem cell23_4662603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 1, 3].length) (baseStart_4662603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662603 prefixEnd_4662603 := by exact prefixLift 4662603
  have htrace : WordTrace (prefixWord ++ tailWord_4662603) baseStart_4662603 baseEnd_4662603 := by
    simpa [prefixWord, tailWord_4662603, baseEnd_4662603] using wordTrace_append hprefix tailTrace_4662603
  have hstable : (prefixWord ++ tailWord_4662603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662603).length < 2 ^ (prefixWord ++ tailWord_4662603).sum := by decide
  have hdescent : baseEnd_4662603 < baseStart_4662603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662604 : List Nat := [2, 2, 1, 3, 2, 3, 1, 4, 1, 2, 2]
def baseStart_4662604 : Nat := 118140960795 + 4662604 * 2 ^ 59
def prefixEnd_4662604 : Nat := 4983230072969 + 3 ^ 40 * 4662604 * 2
def baseEnd_4662604 : Nat := 2394156953576180774107081

theorem tailTrace_4662604 : CollatzResearch.WordTrace tailWord_4662604 prefixEnd_4662604 2394156953576180774107081 := by
  unfold tailWord_4662604
  simp only [CollatzResearch.WordTrace]
  refine ⟨85029569400094746105441433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113372759200126328140588577 85029569400094746105441433)
  ·
    refine ⟨63772177050071059579081075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85029569400094746105441433 63772177050071059579081075)
    ·
      refine ⟨95658265575106589368621613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63772177050071059579081075 95658265575106589368621613)
      ·
        refine ⟨35871849590664971013233105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95658265575106589368621613 35871849590664971013233105)
        ·
          refine ⟨26903887192998728259924829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35871849590664971013233105 26903887192998728259924829)
          ·
            refine ⟨10088957697374523097471811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26903887192998728259924829 10088957697374523097471811)
            ·
              refine ⟨15133436546061784646207717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10088957697374523097471811 15133436546061784646207717)
              ·
                refine ⟨2837519352386584621163947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15133436546061784646207717 2837519352386584621163947)
                ·
                  refine ⟨4256279028579876931745921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837519352386584621163947 4256279028579876931745921)
                  ·
                    refine ⟨3192209271434907698809441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4256279028579876931745921 3192209271434907698809441)
                    ·
                      refine ⟨2394156953576180774107081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192209271434907698809441 2394156953576180774107081)
                      ·
                        rfl

theorem cell23_4662604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_4662604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662604 prefixEnd_4662604 := by exact prefixLift 4662604
  have htrace : WordTrace (prefixWord ++ tailWord_4662604) baseStart_4662604 baseEnd_4662604 := by
    simpa [prefixWord, tailWord_4662604, baseEnd_4662604] using wordTrace_append hprefix tailTrace_4662604
  have hstable : (prefixWord ++ tailWord_4662604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662604).length < 2 ^ (prefixWord ++ tailWord_4662604).sum := by decide
  have hdescent : baseEnd_4662604 < baseStart_4662604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662606 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_4662606 : Nat := 118140960795 + 4662606 * 2 ^ 59
def prefixEnd_4662606 : Nat := 4983230072969 + 3 ^ 40 * 4662606 * 2
def baseEnd_4662606 : Nat := 798052660179163255427357

theorem tailTrace_4662606 : CollatzResearch.WordTrace tailWord_4662606 prefixEnd_4662606 798052660179163255427357 := by
  unfold tailWord_4662606
  simp only [CollatzResearch.WordTrace]
  refine ⟨21257401468272780819056959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113372807830788164368303781 21257401468272780819056959)
  ·
    refine ⟨31886102202409171228585439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21257401468272780819056959 31886102202409171228585439)
    ·
      refine ⟨47829153303613756842878159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31886102202409171228585439 47829153303613756842878159)
      ·
        refine ⟨71743729955420635264317239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47829153303613756842878159 71743729955420635264317239)
        ·
          refine ⟨107615594933130952896475859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71743729955420635264317239 107615594933130952896475859)
          ·
            refine ⟨161423392399696429344713789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107615594933130952896475859 161423392399696429344713789)
            ·
              refine ⟨60533772149886161004267671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161423392399696429344713789 60533772149886161004267671)
              ·
                refine ⟨90800658224829241506401507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60533772149886161004267671 90800658224829241506401507)
                ·
                  refine ⟨136200987337243862259602261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90800658224829241506401507 136200987337243862259602261)
                  ·
                    refine ⟨798052660179163255427357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 136200987337243862259602261 798052660179163255427357)
                    ·
                      rfl

theorem cell23_4662606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_4662606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662606 prefixEnd_4662606 := by exact prefixLift 4662606
  have htrace : WordTrace (prefixWord ++ tailWord_4662606) baseStart_4662606 baseEnd_4662606 := by
    simpa [prefixWord, tailWord_4662606, baseEnd_4662606] using wordTrace_append hprefix tailTrace_4662606
  have hstable : (prefixWord ++ tailWord_4662606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662606).length < 2 ^ (prefixWord ++ tailWord_4662606).sum := by decide
  have hdescent : baseEnd_4662606 < baseStart_4662606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662638 : List Nat := [4, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4662638 : Nat := 118140960795 + 4662638 * 2 ^ 59
def prefixEnd_4662638 : Nat := 4983230072969 + 3 ^ 40 * 4662638 * 2
def baseEnd_4662638 : Nat := 2394174411918433641081925

theorem tailTrace_4662638 : CollatzResearch.WordTrace tailWord_4662638 prefixEnd_4662638 2394174411918433641081925 := by
  unfold tailWord_4662638
  simp only [CollatzResearch.WordTrace]
  refine ⟨21257547360258289502202571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113373585921377544011747045 21257547360258289502202571)
  ·
    refine ⟨31886321040387434253303857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21257547360258289502202571 31886321040387434253303857)
    ·
      refine ⟨23914740780290575689977893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31886321040387434253303857 23914740780290575689977893)
      ·
        refine ⟨4484013896304482941870855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23914740780290575689977893 4484013896304482941870855)
        ·
          refine ⟨6726020844456724412806283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4484013896304482941870855 6726020844456724412806283)
          ·
            refine ⟨10089031266685086619209425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6726020844456724412806283 10089031266685086619209425)
            ·
              refine ⟨7566773450013814964407069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10089031266685086619209425 7566773450013814964407069)
              ·
                refine ⟨2837540043755180611652651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7566773450013814964407069 2837540043755180611652651)
                ·
                  refine ⟨4256310065632770917478977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837540043755180611652651 4256310065632770917478977)
                  ·
                    refine ⟨3192232549224578188109233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4256310065632770917478977 3192232549224578188109233)
                    ·
                      refine ⟨2394174411918433641081925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192232549224578188109233 2394174411918433641081925)
                      ·
                        rfl

theorem cell23_4662638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4662638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662638 prefixEnd_4662638 := by exact prefixLift 4662638
  have htrace : WordTrace (prefixWord ++ tailWord_4662638) baseStart_4662638 baseEnd_4662638 := by
    simpa [prefixWord, tailWord_4662638, baseEnd_4662638] using wordTrace_append hprefix tailTrace_4662638
  have hstable : (prefixWord ++ tailWord_4662638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662638).length < 2 ^ (prefixWord ++ tailWord_4662638).sum := by decide
  have hdescent : baseEnd_4662638 < baseStart_4662638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662677 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 2, 2, 2]
def baseStart_4662677 : Nat := 118140960795 + 4662677 * 2 ^ 59
def prefixEnd_4662677 : Nat := 4983230072969 + 3 ^ 40 * 4662677 * 2
def baseEnd_4662677 : Nat := 2394194437663958988494245

theorem tailTrace_4662677 : CollatzResearch.WordTrace tailWord_4662677 prefixEnd_4662677 2394194437663958988494245 := by
  unfold tailWord_4662677
  simp only [CollatzResearch.WordTrace]
  refine ⟨170061801328925025678290285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113374534219283350452193523 170061801328925025678290285)
  ·
    refine ⟨63773175498346884629358857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170061801328925025678290285 63773175498346884629358857)
    ·
      refine ⟨47829881623760163472019143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63773175498346884629358857 47829881623760163472019143)
      ·
        refine ⟨71744822435640245208028715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47829881623760163472019143 71744822435640245208028715)
        ·
          refine ⟨107617233653460367812043073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71744822435640245208028715 107617233653460367812043073)
          ·
            refine ⟨80712925240095275859032305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107617233653460367812043073 80712925240095275859032305)
            ·
              refine ⟨60534693930071456894274229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80712925240095275859032305 60534693930071456894274229)
              ·
                refine ⟨5675127555944199083838209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60534693930071456894274229 5675127555944199083838209)
                ·
                  refine ⟨4256345666958149312878657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5675127555944199083838209 4256345666958149312878657)
                  ·
                    refine ⟨3192259250218611984658993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4256345666958149312878657 3192259250218611984658993)
                    ·
                      refine ⟨2394194437663958988494245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192259250218611984658993 2394194437663958988494245)
                      ·
                        rfl

theorem cell23_4662677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_4662677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662677 prefixEnd_4662677 := by exact prefixLift 4662677
  have htrace : WordTrace (prefixWord ++ tailWord_4662677) baseStart_4662677 baseEnd_4662677 := by
    simpa [prefixWord, tailWord_4662677, baseEnd_4662677] using wordTrace_append hprefix tailTrace_4662677
  have hstable : (prefixWord ++ tailWord_4662677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662677).length < 2 ^ (prefixWord ++ tailWord_4662677).sum := by decide
  have hdescent : baseEnd_4662677 < baseStart_4662677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662693 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 4, 3, 3]
def baseStart_4662693 : Nat := 118140960795 + 4662693 * 2 ^ 59
def prefixEnd_4662693 : Nat := 4983230072969 + 3 ^ 40 * 4662693 * 2
def baseEnd_4662693 : Nat := 2394202653354430925894171

theorem tailTrace_4662693 : CollatzResearch.WordTrace tailWord_4662693 prefixEnd_4662693 2394202653354430925894171 := by
  unfold tailWord_4662693
  simp only [CollatzResearch.WordTrace]
  refine ⟨170062384896867060410872733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113374923264578040273915155 170062384896867060410872733)
  ·
    refine ⟨63773394336325147654077275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170062384896867060410872733 63773394336325147654077275)
    ·
      refine ⟨95660091504487721481115913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63773394336325147654077275 95660091504487721481115913)
      ·
        refine ⟨71745068628365791110836935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95660091504487721481115913 71745068628365791110836935)
        ·
          refine ⟨107617602942548686666255403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71745068628365791110836935 107617602942548686666255403)
          ·
            refine ⟨161426404413823029999383105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107617602942548686666255403 161426404413823029999383105)
            ·
              refine ⟨121069803310367272499537329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161426404413823029999383105 121069803310367272499537329)
              ·
                refine ⟨90802352482775454374652997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121069803310367272499537329 90802352482775454374652997)
                ·
                  refine ⟨17025441090520397695247437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90802352482775454374652997 17025441090520397695247437)
                  ·
                    refine ⟨6384540408945149135717789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17025441090520397695247437 6384540408945149135717789)
                    ·
                      refine ⟨2394202653354430925894171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6384540408945149135717789 2394202653354430925894171)
                      ·
                        rfl

theorem cell23_4662693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_4662693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662693 prefixEnd_4662693 := by exact prefixLift 4662693
  have htrace : WordTrace (prefixWord ++ tailWord_4662693) baseStart_4662693 baseEnd_4662693 := by
    simpa [prefixWord, tailWord_4662693, baseEnd_4662693] using wordTrace_append hprefix tailTrace_4662693
  have hstable : (prefixWord ++ tailWord_4662693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662693).length < 2 ^ (prefixWord ++ tailWord_4662693).sum := by decide
  have hdescent : baseEnd_4662693 < baseStart_4662693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662700 : List Nat := [2, 2, 1, 1, 1, 1, 7, 3, 5]
def baseStart_4662700 : Nat := 118140960795 + 4662700 * 2 ^ 59
def prefixEnd_4662700 : Nat := 4983230072969 + 3 ^ 40 * 4662700 * 2
def baseEnd_4662700 : Nat := 266022916413223599834071

theorem tailTrace_4662700 : CollatzResearch.WordTrace tailWord_4662700 prefixEnd_4662700 266022916413223599834071 := by
  unfold tailWord_4662700
  simp only [CollatzResearch.WordTrace]
  refine ⟨85031320103920850303188777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113375093471894467070918369 85031320103920850303188777)
  ·
    refine ⟨63773490077940637727391583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85031320103920850303188777 63773490077940637727391583)
    ·
      refine ⟨95660235116910956591087375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63773490077940637727391583 95660235116910956591087375)
      ·
        refine ⟨143490352675366434886631063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95660235116910956591087375 143490352675366434886631063)
        ·
          refine ⟨215235529013049652329946595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143490352675366434886631063 215235529013049652329946595)
          ·
            refine ⟨322853293519574478494919893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215235529013049652329946595 322853293519574478494919893)
            ·
              refine ⟨7566874066865026839724685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 322853293519574478494919893 7566874066865026839724685)
              ·
                refine ⟨2837577775074385064896757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7566874066865026839724685 2837577775074385064896757)
                ·
                  refine ⟨266022916413223599834071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2837577775074385064896757 266022916413223599834071)
                  ·
                    rfl

theorem cell23_4662700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_4662700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662700 prefixEnd_4662700 := by exact prefixLift 4662700
  have htrace : WordTrace (prefixWord ++ tailWord_4662700) baseStart_4662700 baseEnd_4662700 := by
    simpa [prefixWord, tailWord_4662700, baseEnd_4662700] using wordTrace_append hprefix tailTrace_4662700
  have hstable : (prefixWord ++ tailWord_4662700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662700).length < 2 ^ (prefixWord ++ tailWord_4662700).sum := by decide
  have hdescent : baseEnd_4662700 < baseStart_4662700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662717 : List Nat := [1, 4, 1, 2, 2, 1, 5, 2, 5]
def baseStart_4662717 : Nat := 118140960795 + 4662717 * 2 ^ 59
def prefixEnd_4662717 : Nat := 4983230072969 + 3 ^ 40 * 4662717 * 2
def baseEnd_4662717 : Nat := 266023886321126536888229

theorem tailTrace_4662717 : CollatzResearch.WordTrace tailWord_4662717 prefixEnd_4662717 266023886321126536888229 := by
  unfold tailWord_4662717
  simp only [CollatzResearch.WordTrace]
  refine ⟨170063260248780112509746405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113375506832520075006497603 170063260248780112509746405)
  ·
    refine ⟨31886861296646271095577451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170063260248780112509746405 31886861296646271095577451)
    ·
      refine ⟨47830291944969406643366177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31886861296646271095577451 47830291944969406643366177)
      ·
        refine ⟨35872718958727054982524633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47830291944969406643366177 35872718958727054982524633)
        ·
          refine ⟨26904539219045291236893475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35872718958727054982524633 26904539219045291236893475)
          ·
            refine ⟨40356808828567936855340213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26904539219045291236893475 40356808828567936855340213)
            ·
              refine ⟨3783450827678244080188145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40356808828567936855340213 3783450827678244080188145)
              ·
                refine ⟨2837588120758683060141109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3783450827678244080188145 2837588120758683060141109)
                ·
                  refine ⟨266023886321126536888229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2837588120758683060141109 266023886321126536888229)
                  ·
                    rfl

theorem cell23_4662717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_4662717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662717 prefixEnd_4662717 := by exact prefixLift 4662717
  have htrace : WordTrace (prefixWord ++ tailWord_4662717) baseStart_4662717 baseEnd_4662717 := by
    simpa [prefixWord, tailWord_4662717, baseEnd_4662717] using wordTrace_append hprefix tailTrace_4662717
  have hstable : (prefixWord ++ tailWord_4662717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662717).length < 2 ^ (prefixWord ++ tailWord_4662717).sum := by decide
  have hdescent : baseEnd_4662717 < baseStart_4662717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662722 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_4662722 : Nat := 118140960795 + 4662722 * 2 ^ 59
def prefixEnd_4662722 : Nat := 4983230072969 + 3 ^ 40 * 4662722 * 2
def baseEnd_4662722 : Nat := 2394217544293411312431539

theorem tailTrace_4662722 : CollatzResearch.WordTrace tailWord_4662722 prefixEnd_4662722 2394217544293411312431539 := by
  unfold tailWord_4662722
  simp only [CollatzResearch.WordTrace]
  refine ⟨42515860653440499590919605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113375628409174665575785613 42515860653440499590919605)
  ·
    refine ⟨3985861936260046836648713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42515860653440499590919605 3985861936260046836648713)
    ·
      refine ⟨2989396452195035127486535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3985861936260046836648713 2989396452195035127486535)
      ·
        refine ⟨4484094678292552691229803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2989396452195035127486535 4484094678292552691229803)
        ·
          refine ⟨6726142017438829036844705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4484094678292552691229803 6726142017438829036844705)
          ·
            refine ⟨5044606513079121777633529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6726142017438829036844705 5044606513079121777633529)
            ·
              refine ⟨3783454884809341333225147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5044606513079121777633529 3783454884809341333225147)
              ·
                refine ⟨5675182327214011999837721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3783454884809341333225147 5675182327214011999837721)
                ·
                  refine ⟨4256386745410508999878291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5675182327214011999837721 4256386745410508999878291)
                  ·
                    refine ⟨6384580118115763499817437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4256386745410508999878291 6384580118115763499817437)
                    ·
                      refine ⟨2394217544293411312431539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6384580118115763499817437 2394217544293411312431539)
                      ·
                        rfl

theorem cell23_4662722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_4662722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662722 prefixEnd_4662722 := by exact prefixLift 4662722
  have htrace : WordTrace (prefixWord ++ tailWord_4662722) baseStart_4662722 baseEnd_4662722 := by
    simpa [prefixWord, tailWord_4662722, baseEnd_4662722] using wordTrace_append hprefix tailTrace_4662722
  have hstable : (prefixWord ++ tailWord_4662722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662722).length < 2 ^ (prefixWord ++ tailWord_4662722).sum := by decide
  have hdescent : baseEnd_4662722 < baseStart_4662722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662804 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_4662804 : Nat := 118140960795 + 4662804 * 2 ^ 59
def prefixEnd_4662804 : Nat := 4983230072969 + 3 ^ 40 * 4662804 * 2
def baseEnd_4662804 : Nat := 2394259649707079991606161

theorem tailTrace_4662804 : CollatzResearch.WordTrace tailWord_4662804 prefixEnd_4662804 2394259649707079991606161 := by
  unfold tailWord_4662804
  simp only [CollatzResearch.WordTrace]
  refine ⟨85033216699732463184081733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113377622266309950912108977 85033216699732463184081733)
  ·
    refine ⟨15943728131199836847015325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85033216699732463184081733 15943728131199836847015325)
    ·
      refine ⟨5978898049199938817630747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15943728131199836847015325 5978898049199938817630747)
      ·
        refine ⟨8968347073799908226446121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5978898049199938817630747 8968347073799908226446121)
        ·
          refine ⟨6726260305349931169834591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8968347073799908226446121 6726260305349931169834591)
          ·
            refine ⟨10089390458024896754751887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6726260305349931169834591 10089390458024896754751887)
            ·
              refine ⟨15134085687037345132127831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10089390458024896754751887 15134085687037345132127831)
              ·
                refine ⟨22701128530556017698191747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15134085687037345132127831 22701128530556017698191747)
                ·
                  refine ⟨34051692795834026547287621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22701128530556017698191747 34051692795834026547287621)
                  ·
                    refine ⟨6384692399218879977616429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34051692795834026547287621 6384692399218879977616429)
                    ·
                      refine ⟨2394259649707079991606161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6384692399218879977616429 2394259649707079991606161)
                      ·
                        rfl

theorem cell23_4662804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_4662804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662804 prefixEnd_4662804 := by exact prefixLift 4662804
  have htrace : WordTrace (prefixWord ++ tailWord_4662804) baseStart_4662804 baseEnd_4662804 := by
    simpa [prefixWord, tailWord_4662804, baseEnd_4662804] using wordTrace_append hprefix tailTrace_4662804
  have hstable : (prefixWord ++ tailWord_4662804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662804).length < 2 ^ (prefixWord ++ tailWord_4662804).sum := by decide
  have hdescent : baseEnd_4662804 < baseStart_4662804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662824 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 6]
def baseStart_4662824 : Nat := 118140960795 + 4662824 * 2 ^ 59
def prefixEnd_4662824 : Nat := 4983230072969 + 3 ^ 40 * 4662824 * 2
def baseEnd_4662824 : Nat := 266029991035574434817341

theorem tailTrace_4662824 : CollatzResearch.WordTrace tailWord_4662824 prefixEnd_4662824 266029991035574434817341 := by
  unfold tailWord_4662824
  simp only [CollatzResearch.WordTrace]
  refine ⟨85033581429696234891945763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113378108572928313189261017 85033581429696234891945763)
  ·
    refine ⟨127550372144544352337918645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85033581429696234891945763 127550372144544352337918645)
    ·
      refine ⟨11957847388551033031679873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127550372144544352337918645 11957847388551033031679873)
      ·
        refine ⟨8968385541413274773759905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11957847388551033031679873 8968385541413274773759905)
        ·
          refine ⟨6726289156059956080319929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8968385541413274773759905 6726289156059956080319929)
          ·
            refine ⟨5044716867044967060239947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6726289156059956080319929 5044716867044967060239947)
            ·
              refine ⟨7567075300567450590359921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5044716867044967060239947 7567075300567450590359921)
              ·
                refine ⟨5675306475425587942769941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7567075300567450590359921 5675306475425587942769941)
                ·
                  refine ⟨266029991035574434817341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5675306475425587942769941 266029991035574434817341)
                  ·
                    rfl

theorem cell23_4662824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 6].length) (baseStart_4662824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662824 prefixEnd_4662824 := by exact prefixLift 4662824
  have htrace : WordTrace (prefixWord ++ tailWord_4662824) baseStart_4662824 baseEnd_4662824 := by
    simpa [prefixWord, tailWord_4662824, baseEnd_4662824] using wordTrace_append hprefix tailTrace_4662824
  have hstable : (prefixWord ++ tailWord_4662824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662824).length < 2 ^ (prefixWord ++ tailWord_4662824).sum := by decide
  have hdescent : baseEnd_4662824 < baseStart_4662824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662901 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 2, 4]
def baseStart_4662901 : Nat := 118140960795 + 4662901 * 2 ^ 59
def prefixEnd_4662901 : Nat := 4983230072969 + 3 ^ 40 * 4662901 * 2
def baseEnd_4662901 : Nat := 798103152443522037364405

theorem tailTrace_4662901 : CollatzResearch.WordTrace tailWord_4662901 prefixEnd_4662901 798103152443522037364405 := by
  unfold tailWord_4662901
  simp only [CollatzResearch.WordTrace]
  refine ⟨170069971280113511934444557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113379980853409007956296371 170069971280113511934444557)
  ·
    refine ⟨63776239230042566975416709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170069971280113511934444557 63776239230042566975416709)
    ·
      refine ⟨11958044855632981307890633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63776239230042566975416709 11958044855632981307890633)
      ·
        refine ⟨8968533641724735980917975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11958044855632981307890633 8968533641724735980917975)
        ·
          refine ⟨13452800462587103971376963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8968533641724735980917975 13452800462587103971376963)
          ·
            refine ⟨20179200693880655957065445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13452800462587103971376963 20179200693880655957065445)
            ·
              refine ⟨3783600130102622991949771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20179200693880655957065445 3783600130102622991949771)
              ·
                refine ⟨5675400195153934487924657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3783600130102622991949771 5675400195153934487924657)
                ·
                  refine ⟨4256550146365450865943493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5675400195153934487924657 4256550146365450865943493)
                  ·
                    refine ⟨798103152443522037364405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4256550146365450865943493 798103152443522037364405)
                    ·
                      rfl

theorem cell23_4662901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_4662901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662901 prefixEnd_4662901 := by exact prefixLift 4662901
  have htrace : WordTrace (prefixWord ++ tailWord_4662901) baseStart_4662901 baseEnd_4662901 := by
    simpa [prefixWord, tailWord_4662901, baseEnd_4662901] using wordTrace_append hprefix tailTrace_4662901
  have hstable : (prefixWord ++ tailWord_4662901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662901).length < 2 ^ (prefixWord ++ tailWord_4662901).sum := by decide
  have hdescent : baseEnd_4662901 < baseStart_4662901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662942 : List Nat := [4, 3, 1, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_4662942 : Nat := 118140960795 + 4662942 * 2 ^ 59
def prefixEnd_4662942 : Nat := 4983230072969 + 3 ^ 40 * 4662942 * 2
def baseEnd_4662942 : Nat := 2394330510037400451680527

theorem tailTrace_4662942 : CollatzResearch.WordTrace tailWord_4662942 prefixEnd_4662942 2394330510037400451680527 := by
  unfold tailWord_4662942
  simp only [CollatzResearch.WordTrace]
  refine ⟨21258933334120621992085885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113380977781976650624458053 21258933334120621992085885)
  ·
    refine ⟨7972100000295233247032207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21258933334120621992085885 7972100000295233247032207)
    ·
      refine ⟨11958150000442849870548311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7972100000295233247032207 11958150000442849870548311)
      ·
        refine ⟨17937225000664274805822467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11958150000442849870548311 17937225000664274805822467)
        ·
          refine ⟨26905837500996412208733701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17937225000664274805822467 26905837500996412208733701)
          ·
            refine ⟨5044844531436827289137569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26905837500996412208733701 5044844531436827289137569)
            ·
              refine ⟨3783633398577620466853177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5044844531436827289137569 3783633398577620466853177)
              ·
                refine ⟨2837725048933215350139883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3783633398577620466853177 2837725048933215350139883)
                ·
                  refine ⟨4256587573399823025209825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837725048933215350139883 4256587573399823025209825)
                  ·
                    refine ⟨3192440680049867268907369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4256587573399823025209825 3192440680049867268907369)
                    ·
                      refine ⟨2394330510037400451680527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192440680049867268907369 2394330510037400451680527)
                      ·
                        rfl

theorem cell23_4662942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_4662942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662942 prefixEnd_4662942 := by exact prefixLift 4662942
  have htrace : WordTrace (prefixWord ++ tailWord_4662942) baseStart_4662942 baseEnd_4662942 := by
    simpa [prefixWord, tailWord_4662942, baseEnd_4662942] using wordTrace_append hprefix tailTrace_4662942
  have hstable : (prefixWord ++ tailWord_4662942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662942).length < 2 ^ (prefixWord ++ tailWord_4662942).sum := by decide
  have hdescent : baseEnd_4662942 < baseStart_4662942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662947 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 3, 4, 2]
def baseStart_4662947 : Nat := 118140960795 + 4662947 * 2 ^ 59
def prefixEnd_4662947 : Nat := 4983230072969 + 3 ^ 40 * 4662947 * 2
def baseEnd_4662947 : Nat := 2394333077440672932118003

theorem tailTrace_4662947 : CollatzResearch.WordTrace tailWord_4662947 prefixEnd_4662947 2394333077440672932118003 := by
  unfold tailWord_4662947
  simp only [CollatzResearch.WordTrace]
  refine ⟨170071649037946861790619095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113381099358631241193746063 170071649037946861790619095)
  ·
    refine ⟨255107473556920292685928643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170071649037946861790619095 255107473556920292685928643)
    ·
      refine ⟨382661210335380439028892965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255107473556920292685928643 382661210335380439028892965)
      ·
        refine ⟨71748976937883832317917431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 382661210335380439028892965 71748976937883832317917431)
        ·
          refine ⟨107623465406825748476876147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71748976937883832317917431 107623465406825748476876147)
          ·
            refine ⟨161435198110238622715314221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107623465406825748476876147 161435198110238622715314221)
            ·
              refine ⟨60538199291339483518242833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161435198110238622715314221 60538199291339483518242833)
              ·
                refine ⟨45403649468504612638682125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60538199291339483518242833 45403649468504612638682125)
                ·
                  refine ⟨17026368550689229739505797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45403649468504612638682125 17026368550689229739505797)
                  ·
                    refine ⟨3192444103254230576157337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17026368550689229739505797 3192444103254230576157337)
                    ·
                      refine ⟨2394333077440672932118003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192444103254230576157337 2394333077440672932118003)
                      ·
                        rfl

theorem cell23_4662947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_4662947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662947 prefixEnd_4662947 := by exact prefixLift 4662947
  have htrace : WordTrace (prefixWord ++ tailWord_4662947) baseStart_4662947 baseEnd_4662947 := by
    simpa [prefixWord, tailWord_4662947, baseEnd_4662947] using wordTrace_append hprefix tailTrace_4662947
  have hstable : (prefixWord ++ tailWord_4662947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662947).length < 2 ^ (prefixWord ++ tailWord_4662947).sum := by decide
  have hdescent : baseEnd_4662947 < baseStart_4662947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662957 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_4662957 : Nat := 118140960795 + 4662957 * 2 ^ 59
def prefixEnd_4662957 : Nat := 4983230072969 + 3 ^ 40 * 4662957 * 2
def baseEnd_4662957 : Nat := 798112737415739297664319

theorem tailTrace_4662957 : CollatzResearch.WordTrace tailWord_4662957 prefixEnd_4662957 798112737415739297664319 := by
  unfold tailWord_4662957
  simp only [CollatzResearch.WordTrace]
  refine ⟨170072013767910633498483125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113381342511940422332322083 170072013767910633498483125)
  ·
    refine ⟨15944251290741621890482793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170072013767910633498483125 15944251290741621890482793)
    ·
      refine ⟨11958188468056216417862095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15944251290741621890482793 11958188468056216417862095)
      ·
        refine ⟨17937282702084324626793143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11958188468056216417862095 17937282702084324626793143)
        ·
          refine ⟨26905924053126486940189715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17937282702084324626793143 26905924053126486940189715)
          ·
            refine ⟨40358886079689730410284573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26905924053126486940189715 40358886079689730410284573)
            ·
              refine ⟨15134582279883648903856715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40358886079689730410284573 15134582279883648903856715)
              ·
                refine ⟨22701873419825473355785073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15134582279883648903856715 22701873419825473355785073)
                ·
                  refine ⟨17026405064869105016838805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22701873419825473355785073 17026405064869105016838805)
                  ·
                    refine ⟨798112737415739297664319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17026405064869105016838805 798112737415739297664319)
                    ·
                      rfl

theorem cell23_4662957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_4662957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662957 prefixEnd_4662957 := by exact prefixLift 4662957
  have htrace : WordTrace (prefixWord ++ tailWord_4662957) baseStart_4662957 baseEnd_4662957 := by
    simpa [prefixWord, tailWord_4662957, baseEnd_4662957] using wordTrace_append hprefix tailTrace_4662957
  have hstable : (prefixWord ++ tailWord_4662957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662957).length < 2 ^ (prefixWord ++ tailWord_4662957).sum := by decide
  have hdescent : baseEnd_4662957 < baseStart_4662957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662960 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 4]
def baseStart_4662960 : Nat := 118140960795 + 4662960 * 2 ^ 59
def prefixEnd_4662960 : Nat := 4983230072969 + 3 ^ 40 * 4662960 * 2
def baseEnd_4662960 : Nat := 2394339752689181381255443

theorem tailTrace_4662960 : CollatzResearch.WordTrace tailWord_4662960 prefixEnd_4662960 2394339752689181381255443 := by
  unfold tailWord_4662960
  simp only [CollatzResearch.WordTrace]
  refine ⟨85036061593449882505421167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113381415457933176673894889 85036061593449882505421167)
  ·
    refine ⟨127554092390174823758131751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85036061593449882505421167 127554092390174823758131751)
    ·
      refine ⟨191331138585262235637197627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127554092390174823758131751 191331138585262235637197627)
      ·
        refine ⟨286996707877893353455796441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191331138585262235637197627 286996707877893353455796441)
        ·
          refine ⟨215247530908420015091847331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286996707877893353455796441 215247530908420015091847331)
          ·
            refine ⟨322871296362630022637770997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215247530908420015091847331 322871296362630022637770997)
            ·
              refine ⟨30269184033996564622291031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 322871296362630022637770997 30269184033996564622291031)
              ·
                refine ⟨45403776050994846933436547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30269184033996564622291031 45403776050994846933436547)
                ·
                  refine ⟨68105664076492270400154821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45403776050994846933436547 68105664076492270400154821)
                  ·
                    refine ⟨12769812014342300700029029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68105664076492270400154821 12769812014342300700029029)
                    ·
                      refine ⟨2394339752689181381255443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12769812014342300700029029 2394339752689181381255443)
                      ·
                        rfl

theorem cell23_4662960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_4662960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662960 prefixEnd_4662960 := by exact prefixLift 4662960
  have htrace : WordTrace (prefixWord ++ tailWord_4662960) baseStart_4662960 baseEnd_4662960 := by
    simpa [prefixWord, tailWord_4662960, baseEnd_4662960] using wordTrace_append hprefix tailTrace_4662960
  have hstable : (prefixWord ++ tailWord_4662960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662960).length < 2 ^ (prefixWord ++ tailWord_4662960).sum := by decide
  have hdescent : baseEnd_4662960 < baseStart_4662960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4662970 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 9]
def baseStart_4662970 : Nat := 118140960795 + 4662970 * 2 ^ 59
def prefixEnd_4662970 : Nat := 4983230072969 + 3 ^ 40 * 4662970 * 2
def baseEnd_4662970 : Nat := 266038320832858482458933

theorem tailTrace_4662970 : CollatzResearch.WordTrace tailWord_4662970 prefixEnd_4662970 266038320832858482458933 := by
  unfold tailWord_4662970
  simp only [CollatzResearch.WordTrace]
  refine ⟨42518121979215884179676591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113381658611242357812470909 42518121979215884179676591)
  ·
    refine ⟨63777182968823826269514887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42518121979215884179676591 63777182968823826269514887)
    ·
      refine ⟨95665774453235739404272331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63777182968823826269514887 95665774453235739404272331)
      ·
        refine ⟨143498661679853609106408497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95665774453235739404272331 143498661679853609106408497)
        ·
          refine ⟨107623996259890206829806373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143498661679853609106408497 107623996259890206829806373)
          ·
            refine ⟨20179499298729413780588695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107623996259890206829806373 20179499298729413780588695)
            ·
              refine ⟨30269248948094120670883043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20179499298729413780588695 30269248948094120670883043)
              ·
                refine ⟨45403873422141181006324565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30269248948094120670883043 45403873422141181006324565)
                ·
                  refine ⟨266038320832858482458933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45403873422141181006324565 266038320832858482458933)
                  ·
                    rfl

theorem cell23_4662970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_4662970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4662970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4662970 prefixEnd_4662970 := by exact prefixLift 4662970
  have htrace : WordTrace (prefixWord ++ tailWord_4662970) baseStart_4662970 baseEnd_4662970 := by
    simpa [prefixWord, tailWord_4662970, baseEnd_4662970] using wordTrace_append hprefix tailTrace_4662970
  have hstable : (prefixWord ++ tailWord_4662970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4662970).length < 2 ^ (prefixWord ++ tailWord_4662970).sum := by decide
  have hdescent : baseEnd_4662970 < baseStart_4662970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4662970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663015 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4663015 : Nat := 118140960795 + 4663015 * 2 ^ 59
def prefixEnd_4663015 : Nat := 4983230072969 + 3 ^ 40 * 4663015 * 2
def baseEnd_4663015 : Nat := 2394367994125178666067691

theorem tailTrace_4663015 : CollatzResearch.WordTrace tailWord_4663015 prefixEnd_4663015 2394367994125178666067691 := by
  unfold tailWord_4663015
  simp only [CollatzResearch.WordTrace]
  refine ⟨170074129201700509404094499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113382752801133672936062999 170074129201700509404094499)
  ·
    refine ⟨255111193802550764106141749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170074129201700509404094499 255111193802550764106141749)
    ·
      refine ⟨23916674418989134134950789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 255111193802550764106141749 23916674418989134134950789)
      ·
        refine ⟨4484376453560462650303273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23916674418989134134950789 4484376453560462650303273)
        ·
          refine ⟨3363282340170346987727455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4484376453560462650303273 3363282340170346987727455)
          ·
            refine ⟨5044923510255520481591183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363282340170346987727455 5044923510255520481591183)
            ·
              refine ⟨7567385265383280722386775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5044923510255520481591183 7567385265383280722386775)
              ·
                refine ⟨11351077898074921083580163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7567385265383280722386775 11351077898074921083580163)
                ·
                  refine ⟨17026616847112381625370245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11351077898074921083580163 17026616847112381625370245)
                  ·
                    refine ⟨3192490658833571554756921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17026616847112381625370245 3192490658833571554756921)
                    ·
                      refine ⟨2394367994125178666067691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192490658833571554756921 2394367994125178666067691)
                      ·
                        rfl

theorem cell23_4663015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4663015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663015 prefixEnd_4663015 := by exact prefixLift 4663015
  have htrace : WordTrace (prefixWord ++ tailWord_4663015) baseStart_4663015 baseEnd_4663015 := by
    simpa [prefixWord, tailWord_4663015, baseEnd_4663015] using wordTrace_append hprefix tailTrace_4663015
  have hstable : (prefixWord ++ tailWord_4663015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663015).length < 2 ^ (prefixWord ++ tailWord_4663015).sum := by decide
  have hdescent : baseEnd_4663015 < baseStart_4663015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663038 : List Nat := [4, 2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_4663038 : Nat := 118140960795 + 4663038 * 2 ^ 59
def prefixEnd_4663038 : Nat := 4983230072969 + 3 ^ 40 * 4663038 * 2
def baseEnd_4663038 : Nat := 266042200464470230675565

theorem tailTrace_4663038 : CollatzResearch.WordTrace tailWord_4663038 prefixEnd_4663038 266042200464470230675565 := by
  unfold tailWord_4663038
  simp only [CollatzResearch.WordTrace]
  refine ⟨21259371010077148041522721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113383312053744789554787845 21259371010077148041522721)
  ·
    refine ⟨15944528257557861031142041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21259371010077148041522721 15944528257557861031142041)
    ·
      refine ⟨11958396193168395773356531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15944528257557861031142041 11958396193168395773356531)
      ·
        refine ⟨17937594289752593660034797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11958396193168395773356531 17937594289752593660034797)
        ·
          refine ⟨6726597858657222622513049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17937594289752593660034797 6726597858657222622513049)
          ·
            refine ⟨5044948393992916966884787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6726597858657222622513049 5044948393992916966884787)
            ·
              refine ⟨7567422590989375450327181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5044948393992916966884787 7567422590989375450327181)
              ·
                refine ⟨2837783471621015793872693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7567422590989375450327181 2837783471621015793872693)
                ·
                  refine ⟨266042200464470230675565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2837783471621015793872693 266042200464470230675565)
                  ·
                    rfl

theorem cell23_4663038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_4663038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663038 prefixEnd_4663038 := by exact prefixLift 4663038
  have htrace : WordTrace (prefixWord ++ tailWord_4663038) baseStart_4663038 baseEnd_4663038 := by
    simpa [prefixWord, tailWord_4663038, baseEnd_4663038] using wordTrace_append hprefix tailTrace_4663038
  have hstable : (prefixWord ++ tailWord_4663038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663038).length < 2 ^ (prefixWord ++ tailWord_4663038).sum := by decide
  have hdescent : baseEnd_4663038 < baseStart_4663038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663054 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2]
def baseStart_4663054 : Nat := 118140960795 + 4663054 * 2 ^ 59
def prefixEnd_4663054 : Nat := 4983230072969 + 3 ^ 40 * 4663054 * 2
def baseEnd_4663054 : Nat := 2394388019870704013480011

theorem tailTrace_4663054 : CollatzResearch.WordTrace tailWord_4663054 prefixEnd_4663054 2394388019870704013480011 := by
  unfold tailWord_4663054
  simp only [CollatzResearch.WordTrace]
  refine ⟨21259443956069902383095527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113383701099039479376509477 21259443956069902383095527)
  ·
    refine ⟨31889165934104853574643291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21259443956069902383095527 31889165934104853574643291)
    ·
      refine ⟨47833748901157280361964937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31889165934104853574643291 47833748901157280361964937)
      ·
        refine ⟨35875311675867960271473703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47833748901157280361964937 35875311675867960271473703)
        ·
          refine ⟨53812967513801940407210555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35875311675867960271473703 53812967513801940407210555)
          ·
            refine ⟨80719451270702910610815833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53812967513801940407210555 80719451270702910610815833)
            ·
              refine ⟨60539588453027182958111875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80719451270702910610815833 60539588453027182958111875)
              ·
                refine ⟨90809382679540774437167813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60539588453027182958111875 90809382679540774437167813)
                ·
                  refine ⟨17026759252413895206968965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90809382679540774437167813 17026759252413895206968965)
                  ·
                    refine ⟨3192517359827605351306681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17026759252413895206968965 3192517359827605351306681)
                    ·
                      refine ⟨2394388019870704013480011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192517359827605351306681 2394388019870704013480011)
                      ·
                        rfl

theorem cell23_4663054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_4663054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663054 prefixEnd_4663054 := by exact prefixLift 4663054
  have htrace : WordTrace (prefixWord ++ tailWord_4663054) baseStart_4663054 baseEnd_4663054 := by
    simpa [prefixWord, tailWord_4663054, baseEnd_4663054] using wordTrace_append hprefix tailTrace_4663054
  have hstable : (prefixWord ++ tailWord_4663054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663054).length < 2 ^ (prefixWord ++ tailWord_4663054).sum := by decide
  have hdescent : baseEnd_4663054 < baseStart_4663054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663064 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 3, 4]
def baseStart_4663064 : Nat := 118140960795 + 4663064 * 2 ^ 59
def prefixEnd_4663064 : Nat := 4983230072969 + 3 ^ 40 * 4663064 * 2
def baseEnd_4663064 : Nat := 798131051559082991451655

theorem tailTrace_4663064 : CollatzResearch.WordTrace tailWord_4663064 prefixEnd_4663064 798131051559082991451655 := by
  unfold tailWord_4663064
  simp only [CollatzResearch.WordTrace]
  refine ⟨85037958189261495386314123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113383944252348660515085497 85037958189261495386314123)
  ·
    refine ⟨127556937283892243079471185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85037958189261495386314123 127556937283892243079471185)
    ·
      refine ⟨95667702962919182309603389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127556937283892243079471185 95667702962919182309603389)
      ·
        refine ⟨35875388611094693366101271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95667702962919182309603389 35875388611094693366101271)
        ·
          refine ⟨53813082916642040049151907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35875388611094693366101271 53813082916642040049151907)
          ·
            refine ⟨80719624374963060073727861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53813082916642040049151907 80719624374963060073727861)
            ·
              refine ⟨7567464785152786881911987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80719624374963060073727861 7567464785152786881911987)
              ·
                refine ⟨11351197177729180322867981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7567464785152786881911987 11351197177729180322867981)
                ·
                  refine ⟨4256698941648442621075493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11351197177729180322867981 4256698941648442621075493)
                  ·
                    refine ⟨798131051559082991451655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4256698941648442621075493 798131051559082991451655)
                    ·
                      rfl

theorem cell23_4663064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_4663064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663064 prefixEnd_4663064 := by exact prefixLift 4663064
  have htrace : WordTrace (prefixWord ++ tailWord_4663064) baseStart_4663064 baseEnd_4663064 := by
    simpa [prefixWord, tailWord_4663064, baseEnd_4663064] using wordTrace_append hprefix tailTrace_4663064
  have hstable : (prefixWord ++ tailWord_4663064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663064).length < 2 ^ (prefixWord ++ tailWord_4663064).sum := by decide
  have hdescent : baseEnd_4663064 < baseStart_4663064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663074 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_4663074 : Nat := 118140960795 + 4663074 * 2 ^ 59
def prefixEnd_4663074 : Nat := 4983230072969 + 3 ^ 40 * 4663074 * 2
def baseEnd_4663074 : Nat := 2394398289483793935229919

theorem tailTrace_4663074 : CollatzResearch.WordTrace tailWord_4663074 prefixEnd_4663074 2394398289483793935229919 := by
  unfold tailWord_4663074
  simp only [CollatzResearch.WordTrace]
  refine ⟨42519070277121690620123069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113384187405657841653661517 42519070277121690620123069)
  ·
    refine ⟨15944651353920633982546151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42519070277121690620123069 15944651353920633982546151)
    ·
      refine ⟨23916977030880950973819227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15944651353920633982546151 23916977030880950973819227)
      ·
        refine ⟨35875465546321426460728841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23916977030880950973819227 35875465546321426460728841)
        ·
          refine ⟨26906599159741069845546631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35875465546321426460728841 26906599159741069845546631)
          ·
            refine ⟨40359898739611604768319947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26906599159741069845546631 40359898739611604768319947)
            ·
              refine ⟨60539848109417407152479921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40359898739611604768319947 60539848109417407152479921)
              ·
                refine ⟨45404886082063055364359941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60539848109417407152479921 45404886082063055364359941)
                ·
                  refine ⟨8513416140386822880817489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45404886082063055364359941 8513416140386822880817489)
                  ·
                    refine ⟨6385062105290117160613117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8513416140386822880817489 6385062105290117160613117)
                    ·
                      refine ⟨2394398289483793935229919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6385062105290117160613117 2394398289483793935229919)
                      ·
                        rfl

theorem cell23_4663074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_4663074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663074 prefixEnd_4663074 := by exact prefixLift 4663074
  have htrace : WordTrace (prefixWord ++ tailWord_4663074) baseStart_4663074 baseEnd_4663074 := by
    simpa [prefixWord, tailWord_4663074, baseEnd_4663074] using wordTrace_append hprefix tailTrace_4663074
  have hstable : (prefixWord ++ tailWord_4663074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663074).length < 2 ^ (prefixWord ++ tailWord_4663074).sum := by decide
  have hdescent : baseEnd_4663074 < baseStart_4663074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663091 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 3]
def baseStart_4663091 : Nat := 118140960795 + 4663091 * 2 ^ 59
def prefixEnd_4663091 : Nat := 4983230072969 + 3 ^ 40 * 4663091 * 2
def baseEnd_4663091 : Nat := 2394407018654920368717341

theorem tailTrace_4663091 : CollatzResearch.WordTrace tailWord_4663091 prefixEnd_4663091 2394407018654920368717341 := by
  unfold tailWord_4663091
  simp only [CollatzResearch.WordTrace]
  refine ⟨170076901149425174383861127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113384600766283449589240751 170076901149425174383861127)
  ·
    refine ⟨255115351724137761575791691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170076901149425174383861127 255115351724137761575791691)
    ·
      refine ⟨382673027586206642363687537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255115351724137761575791691 382673027586206642363687537)
      ·
        refine ⟨287004770689654981772765653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382673027586206642363687537 287004770689654981772765653)
        ·
          refine ⟨6726674313038788635299195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 287004770689654981772765653 6726674313038788635299195)
          ·
            refine ⟨10090011469558182952948793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6726674313038788635299195 10090011469558182952948793)
            ·
              refine ⟨7567508602168637214711595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10090011469558182952948793 7567508602168637214711595)
              ·
                refine ⟨11351262903252955822067393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7567508602168637214711595 11351262903252955822067393)
                ·
                  refine ⟨8513447177439716866550545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11351262903252955822067393 8513447177439716866550545)
                  ·
                    refine ⟨6385085383079787649912909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8513447177439716866550545 6385085383079787649912909)
                    ·
                      refine ⟨2394407018654920368717341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6385085383079787649912909 2394407018654920368717341)
                      ·
                        rfl

theorem cell23_4663091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 3].length) (baseStart_4663091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663091 prefixEnd_4663091 := by exact prefixLift 4663091
  have htrace : WordTrace (prefixWord ++ tailWord_4663091) baseStart_4663091 baseEnd_4663091 := by
    simpa [prefixWord, tailWord_4663091, baseEnd_4663091] using wordTrace_append hprefix tailTrace_4663091
  have hstable : (prefixWord ++ tailWord_4663091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663091).length < 2 ^ (prefixWord ++ tailWord_4663091).sum := by decide
  have hdescent : baseEnd_4663091 < baseStart_4663091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663124 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_4663124 : Nat := 118140960795 + 4663124 * 2 ^ 59
def prefixEnd_4663124 : Nat := 4983230072969 + 3 ^ 40 * 4663124 * 2
def baseEnd_4663124 : Nat := 798141321172172913201563

theorem tailTrace_4663124 : CollatzResearch.WordTrace tailWord_4663124 prefixEnd_4663124 798141321172172913201563 := by
  unfold tailWord_4663124
  simp only [CollatzResearch.WordTrace]
  refine ⟨85039052379152810509906213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113385403172203747346541617 85039052379152810509906213)
  ·
    refine ⟨15944822321091151970607415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85039052379152810509906213 15944822321091151970607415)
    ·
      refine ⟨23917233481636727955911123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15944822321091151970607415 23917233481636727955911123)
      ·
        refine ⟨35875850222455091933866685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23917233481636727955911123 35875850222455091933866685)
        ·
          refine ⟨13453443833420659475200007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35875850222455091933866685 13453443833420659475200007)
          ·
            refine ⟨20180165750130989212800011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13453443833420659475200007 20180165750130989212800011)
            ·
              refine ⟨30270248625196483819200017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20180165750130989212800011 30270248625196483819200017)
              ·
                refine ⟨22702686468897362864400013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30270248625196483819200017 22702686468897362864400013)
                ·
                  refine ⟨8513507425836511074150005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22702686468897362864400013 8513507425836511074150005)
                  ·
                    refine ⟨798141321172172913201563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8513507425836511074150005 798141321172172913201563)
                    ·
                      rfl

theorem cell23_4663124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_4663124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663124 prefixEnd_4663124 := by exact prefixLift 4663124
  have htrace : WordTrace (prefixWord ++ tailWord_4663124) baseStart_4663124 baseEnd_4663124 := by
    simpa [prefixWord, tailWord_4663124, baseEnd_4663124] using wordTrace_append hprefix tailTrace_4663124
  have hstable : (prefixWord ++ tailWord_4663124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663124).length < 2 ^ (prefixWord ++ tailWord_4663124).sum := by decide
  have hdescent : baseEnd_4663124 < baseStart_4663124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663138 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_4663138 : Nat := 118140960795 + 4663138 * 2 ^ 59
def prefixEnd_4663138 : Nat := 4983230072969 + 3 ^ 40 * 4663138 * 2
def baseEnd_4663138 : Nat := 2394431152245681684829625

theorem tailTrace_4663138 : CollatzResearch.WordTrace tailWord_4663138 prefixEnd_4663138 2394431152245681684829625 := by
  unfold tailWord_4663138
  simp only [CollatzResearch.WordTrace]
  refine ⟨42519653845063725352705517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113385743586836600940548045 42519653845063725352705517)
  ·
    refine ⟨15944870191898897007264569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42519653845063725352705517 15944870191898897007264569)
    ·
      refine ⟨11958652643924172755448427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15944870191898897007264569 11958652643924172755448427)
      ·
        refine ⟨17937978965886259133172641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11958652643924172755448427 17937978965886259133172641)
        ·
          refine ⟨13453484224414694349879481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17937978965886259133172641 13453484224414694349879481)
          ·
            refine ⟨10090113168311020762409611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13453484224414694349879481 10090113168311020762409611)
            ·
              refine ⟨15135169752466531143614417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10090113168311020762409611 15135169752466531143614417)
              ·
                refine ⟨11351377314349898357710813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15135169752466531143614417 11351377314349898357710813)
                ·
                  refine ⟨4256766492881211884141555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11351377314349898357710813 4256766492881211884141555)
                  ·
                    refine ⟨6385149739321817826212333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4256766492881211884141555 6385149739321817826212333)
                    ·
                      refine ⟨2394431152245681684829625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6385149739321817826212333 2394431152245681684829625)
                      ·
                        rfl

theorem cell23_4663138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_4663138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663138 prefixEnd_4663138 := by exact prefixLift 4663138
  have htrace : WordTrace (prefixWord ++ tailWord_4663138) baseStart_4663138 baseEnd_4663138 := by
    simpa [prefixWord, tailWord_4663138, baseEnd_4663138] using wordTrace_append hprefix tailTrace_4663138
  have hstable : (prefixWord ++ tailWord_4663138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663138).length < 2 ^ (prefixWord ++ tailWord_4663138).sum := by decide
  have hdescent : baseEnd_4663138 < baseStart_4663138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663144 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4663144 : Nat := 118140960795 + 4663144 * 2 ^ 59
def prefixEnd_4663144 : Nat := 4983230072969 + 3 ^ 40 * 4663144 * 2
def baseEnd_4663144 : Nat := 2394434233129608661354597

theorem tailTrace_4663144 : CollatzResearch.WordTrace tailWord_4663144 prefixEnd_4663144 2394434233129608661354597 := by
  unfold tailWord_4663144
  simp only [CollatzResearch.WordTrace]
  refine ⟨85039417109116582217770243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113385889478822109623693657 85039417109116582217770243)
  ·
    refine ⟨127559125663674873326655365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85039417109116582217770243 127559125663674873326655365)
    ·
      refine ⟨23917336061939038748747881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127559125663674873326655365 23917336061939038748747881)
      ·
        refine ⟨17938002046454279061560911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23917336061939038748747881 17938002046454279061560911)
        ·
          refine ⟨26907003069681418592341367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17938002046454279061560911 26907003069681418592341367)
          ·
            refine ⟨40360504604522127888512051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26907003069681418592341367 40360504604522127888512051)
            ·
              refine ⟨60540756906783191832768077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40360504604522127888512051 60540756906783191832768077)
              ·
                refine ⟨22702783840043696937288029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60540756906783191832768077 22702783840043696937288029)
                ·
                  refine ⟨8513543940016386351483011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22702783840043696937288029 8513543940016386351483011)
                  ·
                    refine ⟨12770315910024579527224517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8513543940016386351483011 12770315910024579527224517)
                    ·
                      refine ⟨2394434233129608661354597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12770315910024579527224517 2394434233129608661354597)
                      ·
                        rfl

theorem cell23_4663144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4663144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663144 prefixEnd_4663144 := by exact prefixLift 4663144
  have htrace : WordTrace (prefixWord ++ tailWord_4663144) baseStart_4663144 baseEnd_4663144 := by
    simpa [prefixWord, tailWord_4663144, baseEnd_4663144] using wordTrace_append hprefix tailTrace_4663144
  have hstable : (prefixWord ++ tailWord_4663144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663144).length < 2 ^ (prefixWord ++ tailWord_4663144).sum := by decide
  have hdescent : baseEnd_4663144 < baseStart_4663144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663148 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 2, 3, 2]
def baseStart_4663148 : Nat := 118140960795 + 4663148 * 2 ^ 59
def prefixEnd_4663148 : Nat := 4983230072969 + 3 ^ 40 * 4663148 * 2
def baseEnd_4663148 : Nat := 2394436287052226645704579

theorem tailTrace_4663148 : CollatzResearch.WordTrace tailWord_4663148 prefixEnd_4663148 2394436287052226645704579 := by
  unfold tailWord_4663148
  simp only [CollatzResearch.WordTrace]
  refine ⟨85039490055109336559343049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113385986740145782079124065 85039490055109336559343049)
  ·
    refine ⟨63779617541332002419507287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85039490055109336559343049 63779617541332002419507287)
    ·
      refine ⟨95669426311998003629260931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63779617541332002419507287 95669426311998003629260931)
      ·
        refine ⟨143504139467997005443891397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95669426311998003629260931 143504139467997005443891397)
        ·
          refine ⟨26907026150249438520729637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143504139467997005443891397 26907026150249438520729637)
          ·
            refine ⟨5045067403171769722636807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26907026150249438520729637 5045067403171769722636807)
            ·
              refine ⟨7567601104757654583955211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045067403171769722636807 7567601104757654583955211)
              ·
                refine ⟨11351401657136481875932817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7567601104757654583955211 11351401657136481875932817)
                ·
                  refine ⟨8513551242852361406949613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11351401657136481875932817 8513551242852361406949613)
                  ·
                    refine ⟨3192581716069635527606105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8513551242852361406949613 3192581716069635527606105)
                    ·
                      refine ⟨2394436287052226645704579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192581716069635527606105 2394436287052226645704579)
                      ·
                        rfl

theorem cell23_4663148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 3, 2].length) (baseStart_4663148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663148 prefixEnd_4663148 := by exact prefixLift 4663148
  have htrace : WordTrace (prefixWord ++ tailWord_4663148) baseStart_4663148 baseEnd_4663148 := by
    simpa [prefixWord, tailWord_4663148, baseEnd_4663148] using wordTrace_append hprefix tailTrace_4663148
  have hstable : (prefixWord ++ tailWord_4663148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663148).length < 2 ^ (prefixWord ++ tailWord_4663148).sum := by decide
  have hdescent : baseEnd_4663148 < baseStart_4663148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663154 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_4663154 : Nat := 118140960795 + 4663154 * 2 ^ 59
def prefixEnd_4663154 : Nat := 4983230072969 + 3 ^ 40 * 4663154 * 2
def baseEnd_4663154 : Nat := 798146455978717874076517

theorem tailTrace_4663154 : CollatzResearch.WordTrace tailWord_4663154 prefixEnd_4663154 798146455978717874076517 := by
  unfold tailWord_4663154
  simp only [CollatzResearch.WordTrace]
  refine ⟨42519799737049234035851129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113386132632131290762269677 42519799737049234035851129)
  ·
    refine ⟨31889849802786925526888347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42519799737049234035851129 31889849802786925526888347)
    ·
      refine ⟨47834774704180388290332521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31889849802786925526888347 47834774704180388290332521)
      ·
        refine ⟨35876081028135291217749391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47834774704180388290332521 35876081028135291217749391)
        ·
          refine ⟨53814121542202936826624087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35876081028135291217749391 53814121542202936826624087)
          ·
            refine ⟨80721182313304405239936131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53814121542202936826624087 80721182313304405239936131)
            ·
              refine ⟨121081773469956607859904197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80721182313304405239936131 121081773469956607859904197)
              ·
                refine ⟨22702832525616863973732037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121081773469956607859904197 22702832525616863973732037)
                ·
                  refine ⟨4256781098553161995074757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22702832525616863973732037 4256781098553161995074757)
                  ·
                    refine ⟨798146455978717874076517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4256781098553161995074757 798146455978717874076517)
                    ·
                      rfl

theorem cell23_4663154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_4663154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663154 prefixEnd_4663154 := by exact prefixLift 4663154
  have htrace : WordTrace (prefixWord ++ tailWord_4663154) baseStart_4663154 baseEnd_4663154 := by
    simpa [prefixWord, tailWord_4663154, baseEnd_4663154] using wordTrace_append hprefix tailTrace_4663154
  have hstable : (prefixWord ++ tailWord_4663154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663154).length < 2 ^ (prefixWord ++ tailWord_4663154).sum := by decide
  have hdescent : baseEnd_4663154 < baseStart_4663154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663158 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_4663158 : Nat := 118140960795 + 4663158 * 2 ^ 59
def prefixEnd_4663158 : Nat := 4983230072969 + 3 ^ 40 * 4663158 * 2
def baseEnd_4663158 : Nat := 798147140619590535526511

theorem tailTrace_4663158 : CollatzResearch.WordTrace tailWord_4663158 prefixEnd_4663158 798147140619590535526511 := by
  unfold tailWord_4663158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10629959052511402801659383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113386229893454963217700085 10629959052511402801659383)
  ·
    refine ⟨15944938578767104202489075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10629959052511402801659383 15944938578767104202489075)
    ·
      refine ⟨23917407868150656303733613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15944938578767104202489075 23917407868150656303733613)
      ·
        refine ⟨8969027950556496113900105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23917407868150656303733613 8969027950556496113900105)
        ·
          refine ⟨6726770962917372085425079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8969027950556496113900105 6726770962917372085425079)
          ·
            refine ⟨10090156444376058128137619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6726770962917372085425079 10090156444376058128137619)
            ·
              refine ⟨15135234666564087192206429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10090156444376058128137619 15135234666564087192206429)
              ·
                refine ⟨5675712999961532697077411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15135234666564087192206429 5675712999961532697077411)
                ·
                  refine ⟨8513569499942299045616117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5675712999961532697077411 8513569499942299045616117)
                  ·
                    refine ⟨798147140619590535526511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8513569499942299045616117 798147140619590535526511)
                    ·
                      rfl

theorem cell23_4663158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_4663158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663158 prefixEnd_4663158 := by exact prefixLift 4663158
  have htrace : WordTrace (prefixWord ++ tailWord_4663158) baseStart_4663158 baseEnd_4663158 := by
    simpa [prefixWord, tailWord_4663158, baseEnd_4663158] using wordTrace_append hprefix tailTrace_4663158
  have hstable : (prefixWord ++ tailWord_4663158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663158).length < 2 ^ (prefixWord ++ tailWord_4663158).sum := by decide
  have hdescent : baseEnd_4663158 < baseStart_4663158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663161 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 5, 2, 2]
def baseStart_4663161 : Nat := 118140960795 + 4663161 * 2 ^ 59
def prefixEnd_4663161 : Nat := 4983230072969 + 3 ^ 40 * 4663161 * 2
def baseEnd_4663161 : Nat := 2394442962300735094842019

theorem tailTrace_4663161 : CollatzResearch.WordTrace tailWord_4663161 prefixEnd_4663161 2394442962300735094842019 := by
  unfold tailWord_4663161
  simp only [CollatzResearch.WordTrace]
  refine ⟨170079454259171576338909337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113386302839447717559272891 170079454259171576338909337)
  ·
    refine ⟨127559590694378682254182003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170079454259171576338909337 127559590694378682254182003)
    ·
      refine ⟨191339386041568023381273005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127559590694378682254182003 191339386041568023381273005)
      ·
        refine ⟨71752269765588008767977377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191339386041568023381273005 71752269765588008767977377)
        ·
          refine ⟨53814202324191006575983033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71752269765588008767977377 53814202324191006575983033)
          ·
            refine ⟨40360651743143254931987275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53814202324191006575983033 40360651743143254931987275)
            ·
              refine ⟨60540977614714882397980913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40360651743143254931987275 60540977614714882397980913)
              ·
                refine ⟨45405733211036161798485685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60540977614714882397980913 45405733211036161798485685)
                ·
                  refine ⟨4256787488534640168608033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45405733211036161798485685 4256787488534640168608033)
                  ·
                    refine ⟨3192590616400980126456025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4256787488534640168608033 3192590616400980126456025)
                    ·
                      refine ⟨2394442962300735094842019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192590616400980126456025 2394442962300735094842019)
                      ·
                        rfl

theorem cell23_4663161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_4663161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663161 prefixEnd_4663161 := by exact prefixLift 4663161
  have htrace : WordTrace (prefixWord ++ tailWord_4663161) baseStart_4663161 baseEnd_4663161 := by
    simpa [prefixWord, tailWord_4663161, baseEnd_4663161] using wordTrace_append hprefix tailTrace_4663161
  have hstable : (prefixWord ++ tailWord_4663161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663161).length < 2 ^ (prefixWord ++ tailWord_4663161).sum := by decide
  have hdescent : baseEnd_4663161 < baseStart_4663161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663171 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 2, 4]
def baseStart_4663171 : Nat := 118140960795 + 4663171 * 2 ^ 59
def prefixEnd_4663171 : Nat := 4983230072969 + 3 ^ 40 * 4663171 * 2
def baseEnd_4663171 : Nat := 798149365702426685238991

theorem tailTrace_4663171 : CollatzResearch.WordTrace tailWord_4663171 prefixEnd_4663171 798149365702426685238991 := by
  unfold tailWord_4663171
  simp only [CollatzResearch.WordTrace]
  refine ⟨170079818989135348046773367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113386545992756898697848911 170079818989135348046773367)
  ·
    refine ⟨255119728483703022070160051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170079818989135348046773367 255119728483703022070160051)
    ·
      refine ⟨382679592725554533105240077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255119728483703022070160051 382679592725554533105240077)
      ·
        refine ⟨143504847272082949914465029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 382679592725554533105240077 143504847272082949914465029)
        ·
          refine ⟨26907158863515553108962193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143504847272082949914465029 26907158863515553108962193)
          ·
            refine ⟨20180369147636664831721645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26907158863515553108962193 20180369147636664831721645)
            ·
              refine ⟨7567638430363749311895617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20180369147636664831721645 7567638430363749311895617)
              ·
                refine ⟨5675728822772811983921713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7567638430363749311895617 5675728822772811983921713)
                ·
                  refine ⟨4256796617079608987941285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5675728822772811983921713 4256796617079608987941285)
                  ·
                    refine ⟨798149365702426685238991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4256796617079608987941285 798149365702426685238991)
                    ·
                      rfl

theorem cell23_4663171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 4].length) (baseStart_4663171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663171 prefixEnd_4663171 := by exact prefixLift 4663171
  have htrace : WordTrace (prefixWord ++ tailWord_4663171) baseStart_4663171 baseEnd_4663171 := by
    simpa [prefixWord, tailWord_4663171, baseEnd_4663171] using wordTrace_append hprefix tailTrace_4663171
  have hstable : (prefixWord ++ tailWord_4663171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663171).length < 2 ^ (prefixWord ++ tailWord_4663171).sum := by decide
  have hdescent : baseEnd_4663171 < baseStart_4663171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663191 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 4]
def baseStart_4663191 : Nat := 118140960795 + 4663191 * 2 ^ 59
def prefixEnd_4663191 : Nat := 4983230072969 + 3 ^ 40 * 4663191 * 2
def baseEnd_4663191 : Nat := 2394458366720369977466881

theorem tailTrace_4663191 : CollatzResearch.WordTrace tailWord_4663191 prefixEnd_4663191 2394458366720369977466881 := by
  unfold tailWord_4663191
  simp only [CollatzResearch.WordTrace]
  refine ⟨170080548449062891462501427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113387032299375260975000951 170080548449062891462501427)
  ·
    refine ⟨255120822673594337193752141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170080548449062891462501427 255120822673594337193752141)
    ·
      refine ⟨95670308502597876447657053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255120822673594337193752141 95670308502597876447657053)
      ·
        refine ⟨35876365688474203667871395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95670308502597876447657053 35876365688474203667871395)
        ·
          refine ⟨53814548532711305501807093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35876365688474203667871395 53814548532711305501807093)
          ·
            refine ⟨5045113924941684890794415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53814548532711305501807093 5045113924941684890794415)
            ·
              refine ⟨7567670887412527336191623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045113924941684890794415 7567670887412527336191623)
              ·
                refine ⟨11351506331118791004287435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7567670887412527336191623 11351506331118791004287435)
                ·
                  refine ⟨17027259496678186506431153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11351506331118791004287435 17027259496678186506431153)
                  ·
                    refine ⟨12770444622508639879823365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17027259496678186506431153 12770444622508639879823365)
                    ·
                      refine ⟨2394458366720369977466881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12770444622508639879823365 2394458366720369977466881)
                      ·
                        rfl

theorem cell23_4663191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_4663191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663191 prefixEnd_4663191 := by exact prefixLift 4663191
  have htrace : WordTrace (prefixWord ++ tailWord_4663191) baseStart_4663191 baseEnd_4663191 := by
    simpa [prefixWord, tailWord_4663191, baseEnd_4663191] using wordTrace_append hprefix tailTrace_4663191
  have hstable : (prefixWord ++ tailWord_4663191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663191).length < 2 ^ (prefixWord ++ tailWord_4663191).sum := by decide
  have hdescent : baseEnd_4663191 < baseStart_4663191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663301 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 2, 3, 3]
def baseStart_4663301 : Nat := 118140960795 + 4663301 * 2 ^ 59
def prefixEnd_4663301 : Nat := 4983230072969 + 3 ^ 40 * 4663301 * 2
def baseEnd_4663301 : Nat := 2394514849592364547091375

theorem tailTrace_4663301 : CollatzResearch.WordTrace tailWord_4663301 prefixEnd_4663301 2394514849592364547091375 := by
  unfold tailWord_4663301
  simp only [CollatzResearch.WordTrace]
  refine ⟨170084560478664380249005757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113389706985776253499337171 170084560478664380249005757)
  ·
    refine ⟨63781710179499142593377159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170084560478664380249005757 63781710179499142593377159)
    ·
      refine ⟨95672565269248713890065739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63781710179499142593377159 95672565269248713890065739)
      ·
        refine ⟨143508847903873070835098609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95672565269248713890065739 143508847903873070835098609)
        ·
          refine ⟨107631635927904803126323957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143508847903873070835098609 107631635927904803126323957)
          ·
            refine ⟨10090465868241075293092871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107631635927904803126323957 10090465868241075293092871)
            ·
              refine ⟨15135698802361612939639307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10090465868241075293092871 15135698802361612939639307)
              ·
                refine ⟨22703548203542419409458961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15135698802361612939639307 22703548203542419409458961)
                ·
                  refine ⟨17027661152656814557094221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22703548203542419409458961 17027661152656814557094221)
                  ·
                    refine ⟨6385372932246305458910333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17027661152656814557094221 6385372932246305458910333)
                    ·
                      refine ⟨2394514849592364547091375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6385372932246305458910333 2394514849592364547091375)
                      ·
                        rfl

theorem cell23_4663301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_4663301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663301 prefixEnd_4663301 := by exact prefixLift 4663301
  have htrace : WordTrace (prefixWord ++ tailWord_4663301) baseStart_4663301 baseEnd_4663301 := by
    simpa [prefixWord, tailWord_4663301, baseEnd_4663301] using wordTrace_append hprefix tailTrace_4663301
  have hstable : (prefixWord ++ tailWord_4663301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663301).length < 2 ^ (prefixWord ++ tailWord_4663301).sum := by decide
  have hdescent : baseEnd_4663301 < baseStart_4663301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663304 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 1, 7]
def baseStart_4663304 : Nat := 118140960795 + 4663304 * 2 ^ 59
def prefixEnd_4663304 : Nat := 4983230072969 + 3 ^ 40 * 4663304 * 2
def baseEnd_4663304 : Nat := 798172130011442678451287

theorem tailTrace_4663304 : CollatzResearch.WordTrace tailWord_4663304 prefixEnd_4663304 798172130011442678451287 := by
  unfold tailWord_4663304
  simp only [CollatzResearch.WordTrace]
  refine ⟨85042334948826755880682483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113389779931769007840909977 85042334948826755880682483)
  ·
    refine ⟨127563502423240133821023725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85042334948826755880682483 127563502423240133821023725)
    ·
      refine ⟨47836313408715050182883897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127563502423240133821023725 47836313408715050182883897)
      ·
        refine ⟨35877235056536287637162923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47836313408715050182883897 35877235056536287637162923)
        ·
          refine ⟨53815852584804431455744385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35877235056536287637162923 53815852584804431455744385)
          ·
            refine ⟨40361889438603323591808289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53815852584804431455744385 40361889438603323591808289)
            ·
              refine ⟨30271417078952492693856217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40361889438603323591808289 30271417078952492693856217)
              ·
                refine ⟨22703562809214369520392163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30271417078952492693856217 22703562809214369520392163)
                ·
                  refine ⟨34055344213821554280588245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22703562809214369520392163 34055344213821554280588245)
                  ·
                    refine ⟨798172130011442678451287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34055344213821554280588245 798172130011442678451287)
                    ·
                      rfl

theorem cell23_4663304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_4663304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663304 prefixEnd_4663304 := by exact prefixLift 4663304
  have htrace : WordTrace (prefixWord ++ tailWord_4663304) baseStart_4663304 baseEnd_4663304 := by
    simpa [prefixWord, tailWord_4663304, baseEnd_4663304] using wordTrace_append hprefix tailTrace_4663304
  have hstable : (prefixWord ++ tailWord_4663304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663304).length < 2 ^ (prefixWord ++ tailWord_4663304).sum := by decide
  have hdescent : baseEnd_4663304 < baseStart_4663304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663336 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4663336 : Nat := 118140960795 + 4663336 * 2 ^ 59
def prefixEnd_4663336 : Nat := 4983230072969 + 3 ^ 40 * 4663336 * 2
def baseEnd_4663336 : Nat := 2394532821415271910153715

theorem tailTrace_4663336 : CollatzResearch.WordTrace tailWord_4663336 prefixEnd_4663336 2394532821415271910153715 := by
  unfold tailWord_4663336
  simp only [CollatzResearch.WordTrace]
  refine ⟨85042918516768790613264931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113390558022358387484353241 85042918516768790613264931)
  ·
    refine ⟨127564377775153185919897397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85042918516768790613264931 127564377775153185919897397)
    ·
      refine ⟨11959160416420611179990381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127564377775153185919897397 11959160416420611179990381)
      ·
        refine ⟨4484685156157729192496393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11959160416420611179990381 4484685156157729192496393)
        ·
          refine ⟨3363513867118296894372295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4484685156157729192496393 3363513867118296894372295)
          ·
            refine ⟨5045270800677445341558443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363513867118296894372295 5045270800677445341558443)
            ·
              refine ⟨7567906201016168012337665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045270800677445341558443 7567906201016168012337665)
              ·
                refine ⟨5675929650762126009253249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7567906201016168012337665 5675929650762126009253249)
                ·
                  refine ⟨4256947238071594506939937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5675929650762126009253249 4256947238071594506939937)
                  ·
                    refine ⟨3192710428553695880204953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4256947238071594506939937 3192710428553695880204953)
                    ·
                      refine ⟨2394532821415271910153715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192710428553695880204953 2394532821415271910153715)
                      ·
                        rfl

theorem cell23_4663336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4663336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663336 prefixEnd_4663336 := by exact prefixLift 4663336
  have htrace : WordTrace (prefixWord ++ tailWord_4663336) baseStart_4663336 baseEnd_4663336 := by
    simpa [prefixWord, tailWord_4663336, baseEnd_4663336] using wordTrace_append hprefix tailTrace_4663336
  have hstable : (prefixWord ++ tailWord_4663336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663336).length < 2 ^ (prefixWord ++ tailWord_4663336).sum := by decide
  have hdescent : baseEnd_4663336 < baseStart_4663336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663351 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 3, 4]
def baseStart_4663351 : Nat := 118140960795 + 4663351 * 2 ^ 59
def prefixEnd_4663351 : Nat := 4983230072969 + 3 ^ 40 * 4663351 * 2
def baseEnd_4663351 : Nat := 798180174541696450488715

theorem tailTrace_4663351 : CollatzResearch.WordTrace tailWord_4663351 prefixEnd_4663351 798180174541696450488715 := by
  unfold tailWord_4663351
  simp only [CollatzResearch.WordTrace]
  refine ⟨170086384128483238788325907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113390922752322159192217271 170086384128483238788325907)
  ·
    refine ⟨255129576192724858182488861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170086384128483238788325907 255129576192724858182488861)
    ·
      refine ⟨95673591072271821818433323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255129576192724858182488861 95673591072271821818433323)
      ·
        refine ⟨143510386608407732727649985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95673591072271821818433323 143510386608407732727649985)
        ·
          refine ⟨107632789956305799545737489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143510386608407732727649985 107632789956305799545737489)
          ·
            refine ⟨80724592467229349659303117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107632789956305799545737489 80724592467229349659303117)
            ·
              refine ⟨30271722175211006122238669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80724592467229349659303117 30271722175211006122238669)
              ·
                refine ⟨11351895815704127295839501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30271722175211006122238669 11351895815704127295839501)
                ·
                  refine ⟨4256960930889047735939813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11351895815704127295839501 4256960930889047735939813)
                  ·
                    refine ⟨798180174541696450488715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4256960930889047735939813 798180174541696450488715)
                    ·
                      rfl

theorem cell23_4663351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_4663351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663351 prefixEnd_4663351 := by exact prefixLift 4663351
  have htrace : WordTrace (prefixWord ++ tailWord_4663351) baseStart_4663351 baseEnd_4663351 := by
    simpa [prefixWord, tailWord_4663351, baseEnd_4663351] using wordTrace_append hprefix tailTrace_4663351
  have hstable : (prefixWord ++ tailWord_4663351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663351).length < 2 ^ (prefixWord ++ tailWord_4663351).sum := by decide
  have hdescent : baseEnd_4663351 < baseStart_4663351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663354 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_4663354 : Nat := 118140960795 + 4663354 * 2 ^ 59
def prefixEnd_4663354 : Nat := 4983230072969 + 3 ^ 40 * 4663354 * 2
def baseEnd_4663354 : Nat := 2394542064067052839728631

theorem tailTrace_4663354 : CollatzResearch.WordTrace tailWord_4663354 prefixEnd_4663354 2394542064067052839728631 := by
  unfold tailWord_4663354
  simp only [CollatzResearch.WordTrace]
  refine ⟨42521623386868092575171279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113390995698314913533790077 42521623386868092575171279)
  ·
    refine ⟨63782435080302138862756919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42521623386868092575171279 63782435080302138862756919)
    ·
      refine ⟨95673652620453208294135379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63782435080302138862756919 95673652620453208294135379)
      ·
        refine ⟨143510478930679812441203069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95673652620453208294135379 143510478930679812441203069)
        ·
          refine ⟨53816429599004929665451151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143510478930679812441203069 53816429599004929665451151)
          ·
            refine ⟨80724644398507394498176727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53816429599004929665451151 80724644398507394498176727)
            ·
              refine ⟨121086966597761091747265091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80724644398507394498176727 121086966597761091747265091)
              ·
                refine ⟨181630449896641637620897637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121086966597761091747265091 181630449896641637620897637)
                ·
                  refine ⟨34055709355620307053918307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181630449896641637620897637 34055709355620307053918307)
                  ·
                    refine ⟨51083564033430460580877461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34055709355620307053918307 51083564033430460580877461)
                    ·
                      refine ⟨2394542064067052839728631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51083564033430460580877461 2394542064067052839728631)
                      ·
                        rfl

theorem cell23_4663354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_4663354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663354 prefixEnd_4663354 := by exact prefixLift 4663354
  have htrace : WordTrace (prefixWord ++ tailWord_4663354) baseStart_4663354 baseEnd_4663354 := by
    simpa [prefixWord, tailWord_4663354, baseEnd_4663354] using wordTrace_append hprefix tailTrace_4663354
  have hstable : (prefixWord ++ tailWord_4663354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663354).length < 2 ^ (prefixWord ++ tailWord_4663354).sum := by decide
  have hdescent : baseEnd_4663354 < baseStart_4663354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663402 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 3, 4]
def baseStart_4663402 : Nat := 118140960795 + 4663402 * 2 ^ 59
def prefixEnd_4663402 : Nat := 4983230072969 + 3 ^ 40 * 4663402 * 2
def baseEnd_4663402 : Nat := 798188903712822883976137

theorem tailTrace_4663402 : CollatzResearch.WordTrace tailWord_4663402 prefixEnd_4663402 798188903712822883976137 := by
  unfold tailWord_4663402
  simp only [CollatzResearch.WordTrace]
  refine ⟨42522061062824618624608115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113392162834198982998954973 42522061062824618624608115)
  ·
    refine ⟨63783091594236927936912173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42522061062824618624608115 63783091594236927936912173)
    ·
      refine ⟨23918659347838847976342065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63783091594236927936912173 23918659347838847976342065)
      ·
        refine ⟨17938994510879135982256549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23918659347838847976342065 17938994510879135982256549)
        ·
          refine ⟨3363561470789837996673103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17938994510879135982256549 3363561470789837996673103)
          ·
            refine ⟨5045342206184756995009655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363561470789837996673103 5045342206184756995009655)
            ·
              refine ⟨7568013309277135492514483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045342206184756995009655 7568013309277135492514483)
              ·
                refine ⟨11352019963915703238771725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7568013309277135492514483 11352019963915703238771725)
                ·
                  refine ⟨4257007486468388714539397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11352019963915703238771725 4257007486468388714539397)
                  ·
                    refine ⟨798188903712822883976137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4257007486468388714539397 798188903712822883976137)
                    ·
                      rfl

theorem cell23_4663402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_4663402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663402 prefixEnd_4663402 := by exact prefixLift 4663402
  have htrace : WordTrace (prefixWord ++ tailWord_4663402) baseStart_4663402 baseEnd_4663402 := by
    simpa [prefixWord, tailWord_4663402, baseEnd_4663402] using wordTrace_append hprefix tailTrace_4663402
  have hstable : (prefixWord ++ tailWord_4663402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663402).length < 2 ^ (prefixWord ++ tailWord_4663402).sum := by decide
  have hdescent : baseEnd_4663402 < baseStart_4663402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663442 : List Nat := [3, 2, 3, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_4663442 : Nat := 118140960795 + 4663442 * 2 ^ 59
def prefixEnd_4663442 : Nat := 4983230072969 + 3 ^ 40 * 4663442 * 2
def baseEnd_4663442 : Nat := 2394587250364648495428227

theorem tailTrace_4663442 : CollatzResearch.WordTrace tailWord_4663442 prefixEnd_4663442 2394587250364648495428227 := by
  unfold tailWord_4663442
  simp only [CollatzResearch.WordTrace]
  refine ⟨42522425792788390332472145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113393135447435707553259053 42522425792788390332472145)
  ·
    refine ⟨31891819344591292749354109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42522425792788390332472145 31891819344591292749354109)
    ·
      refine ⟨11959432254221734781007791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31891819344591292749354109 11959432254221734781007791)
      ·
        refine ⟨17939148381332602171511687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11959432254221734781007791 17939148381332602171511687)
        ·
          refine ⟨26908722571998903257267531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17939148381332602171511687 26908722571998903257267531)
          ·
            refine ⟨40363083857998354885901297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26908722571998903257267531 40363083857998354885901297)
            ·
              refine ⟨30272312893498766164425973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40363083857998354885901297 30272312893498766164425973)
              ·
                refine ⟨2838029333765509327914935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30272312893498766164425973 2838029333765509327914935)
                ·
                  refine ⟨4257044000648263991872403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2838029333765509327914935 4257044000648263991872403)
                  ·
                    refine ⟨6385566000972395987808605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4257044000648263991872403 6385566000972395987808605)
                    ·
                      refine ⟨2394587250364648495428227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6385566000972395987808605 2394587250364648495428227)
                      ·
                        rfl

theorem cell23_4663442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_4663442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663442 prefixEnd_4663442 := by exact prefixLift 4663442
  have htrace : WordTrace (prefixWord ++ tailWord_4663442) baseStart_4663442 baseEnd_4663442 := by
    simpa [prefixWord, tailWord_4663442, baseEnd_4663442] using wordTrace_append hprefix tailTrace_4663442
  have hstable : (prefixWord ++ tailWord_4663442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663442).length < 2 ^ (prefixWord ++ tailWord_4663442).sum := by decide
  have hdescent : baseEnd_4663442 < baseStart_4663442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663461 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_4663461 : Nat := 118140960795 + 4663461 * 2 ^ 59
def prefixEnd_4663461 : Nat := 4983230072969 + 3 ^ 40 * 4663461 * 2
def baseEnd_4663461 : Nat := 2394597006497083921090639

theorem tailTrace_4663461 : CollatzResearch.WordTrace tailWord_4663461 prefixEnd_4663461 2394597006497083921090639 := by
  unfold tailWord_4663461
  simp only [CollatzResearch.WordTrace]
  refine ⟨170090396158084727574830237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113393597438723151716553491 170090396158084727574830237)
  ·
    refine ⟨63783898559281772840561339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170090396158084727574830237 63783898559281772840561339)
    ·
      refine ⟨95675847838922659260842009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63783898559281772840561339 95675847838922659260842009)
      ·
        refine ⟨71756885879191994445631507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95675847838922659260842009 71756885879191994445631507)
        ·
          refine ⟨107635328818787991668447261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71756885879191994445631507 107635328818787991668447261)
          ·
            refine ⟨40363248307045496875667723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107635328818787991668447261 40363248307045496875667723)
            ·
              refine ⟨60544872460568245313501585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40363248307045496875667723 60544872460568245313501585)
              ·
                refine ⟨45408654345426183985126189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60544872460568245313501585 45408654345426183985126189)
                ·
                  refine ⟨17028245379534818994422321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45408654345426183985126189 17028245379534818994422321)
                  ·
                    refine ⟨12771184034651114245816741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17028245379534818994422321 12771184034651114245816741)
                    ·
                      refine ⟨2394597006497083921090639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12771184034651114245816741 2394597006497083921090639)
                      ·
                        rfl

theorem cell23_4663461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_4663461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663461 prefixEnd_4663461 := by exact prefixLift 4663461
  have htrace : WordTrace (prefixWord ++ tailWord_4663461) baseStart_4663461 baseEnd_4663461 := by
    simpa [prefixWord, tailWord_4663461, baseEnd_4663461] using wordTrace_append hprefix tailTrace_4663461
  have hstable : (prefixWord ++ tailWord_4663461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663461).length < 2 ^ (prefixWord ++ tailWord_4663461).sum := by decide
  have hdescent : baseEnd_4663461 < baseStart_4663461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663476 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4663476 : Nat := 118140960795 + 4663476 * 2 ^ 59
def prefixEnd_4663476 : Nat := 4983230072969 + 3 ^ 40 * 4663476 * 2
def baseEnd_4663476 : Nat := 2394604708706901362403071

theorem tailTrace_4663476 : CollatzResearch.WordTrace tailWord_4663476 prefixEnd_4663476 2394604708706901362403071 := by
  unfold tailWord_4663476
  simp only [CollatzResearch.WordTrace]
  refine ⟨85045471626515192568313141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113393962168686923424417521 85045471626515192568313141)
  ·
    refine ⟨7973012964985799303279357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85045471626515192568313141 7973012964985799303279357)
    ·
      refine ⟨2989879861869674738729759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7973012964985799303279357 2989879861869674738729759)
      ·
        refine ⟨4484819792804512108094639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2989879861869674738729759 4484819792804512108094639)
        ·
          refine ⟨6727229689206768162141959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4484819792804512108094639 6727229689206768162141959)
          ·
            refine ⟨10090844533810152243212939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6727229689206768162141959 10090844533810152243212939)
            ·
              refine ⟨15136266800715228364819409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10090844533810152243212939 15136266800715228364819409)
              ·
                refine ⟨11352200100536421273614557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15136266800715228364819409 11352200100536421273614557)
                ·
                  refine ⟨4257075037701157977605459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11352200100536421273614557 4257075037701157977605459)
                  ·
                    refine ⟨6385612556551736966408189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4257075037701157977605459 6385612556551736966408189)
                    ·
                      refine ⟨2394604708706901362403071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6385612556551736966408189 2394604708706901362403071)
                      ·
                        rfl

theorem cell23_4663476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4663476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663476 prefixEnd_4663476 := by exact prefixLift 4663476
  have htrace : WordTrace (prefixWord ++ tailWord_4663476) baseStart_4663476 baseEnd_4663476 := by
    simpa [prefixWord, tailWord_4663476, baseEnd_4663476] using wordTrace_append hprefix tailTrace_4663476
  have hstable : (prefixWord ++ tailWord_4663476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663476).length < 2 ^ (prefixWord ++ tailWord_4663476).sum := by decide
  have hdescent : baseEnd_4663476 < baseStart_4663476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663488 : List Nat := [2, 1, 1, 2, 5, 2, 3, 7]
def baseStart_4663488 : Nat := 118140960795 + 4663488 * 2 ^ 59
def prefixEnd_4663488 : Nat := 4983230072969 + 3 ^ 40 * 4663488 * 2
def baseEnd_4663488 : Nat := 88689291499065011683445

theorem tailTrace_4663488 : CollatzResearch.WordTrace tailWord_4663488 prefixEnd_4663488 88689291499065011683445 := by
  unfold tailWord_4663488
  simp only [CollatzResearch.WordTrace]
  refine ⟨85045690464493455593031559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113394253952657940790708745 85045690464493455593031559)
  ·
    refine ⟨127568535696740183389547339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85045690464493455593031559 127568535696740183389547339)
    ·
      refine ⟨191352803545110275084321009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127568535696740183389547339 191352803545110275084321009)
      ·
        refine ⟨143514602658832706313240757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191352803545110275084321009 143514602658832706313240757)
        ·
          refine ⟨13454493999265566216866321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143514602658832706313240757 13454493999265566216866321)
          ·
            refine ⟨10090870499449174662649741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13454493999265566216866321 10090870499449174662649741)
            ·
              refine ⟨3784076437293440498493653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10090870499449174662649741 3784076437293440498493653)
              ·
                refine ⟨88689291499065011683445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3784076437293440498493653 88689291499065011683445)
                ·
                  rfl

theorem cell23_4663488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 7].length) (baseStart_4663488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663488 prefixEnd_4663488 := by exact prefixLift 4663488
  have htrace : WordTrace (prefixWord ++ tailWord_4663488) baseStart_4663488 baseEnd_4663488 := by
    simpa [prefixWord, tailWord_4663488, baseEnd_4663488] using wordTrace_append hprefix tailTrace_4663488
  have hstable : (prefixWord ++ tailWord_4663488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663488).length < 2 ^ (prefixWord ++ tailWord_4663488).sum := by decide
  have hdescent : baseEnd_4663488 < baseStart_4663488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663498 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_4663498 : Nat := 118140960795 + 4663498 * 2 ^ 59
def prefixEnd_4663498 : Nat := 4983230072969 + 3 ^ 40 * 4663498 * 2
def baseEnd_4663498 : Nat := 2394616005281300276327969

theorem tailTrace_4663498 : CollatzResearch.WordTrace tailWord_4663498 prefixEnd_4663498 2394616005281300276327969 := by
  unfold tailWord_4663498
  simp only [CollatzResearch.WordTrace]
  refine ⟨42522936414737670723481787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113394497105967121929284765 42522936414737670723481787)
  ·
    refine ⟨63784404622106506085222681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42522936414737670723481787 63784404622106506085222681)
    ·
      refine ⟨47838303466579879563917011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63784404622106506085222681 47838303466579879563917011)
      ·
        refine ⟨71757455199869819345875517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47838303466579879563917011 71757455199869819345875517)
        ·
          refine ⟨26909045699951182254703319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71757455199869819345875517 26909045699951182254703319)
          ·
            refine ⟨40363568549926773382054979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26909045699951182254703319 40363568549926773382054979)
            ·
              refine ⟨60545352824890160073082469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40363568549926773382054979 60545352824890160073082469)
              ·
                refine ⟨11352253654666905013702963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60545352824890160073082469 11352253654666905013702963)
                ·
                  refine ⟨17028380482000357520554445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11352253654666905013702963 17028380482000357520554445)
                  ·
                    refine ⟨6385642680750134070207917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17028380482000357520554445 6385642680750134070207917)
                    ·
                      refine ⟨2394616005281300276327969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6385642680750134070207917 2394616005281300276327969)
                      ·
                        rfl

theorem cell23_4663498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_4663498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663498 prefixEnd_4663498 := by exact prefixLift 4663498
  have htrace : WordTrace (prefixWord ++ tailWord_4663498) baseStart_4663498 baseEnd_4663498 := by
    simpa [prefixWord, tailWord_4663498, baseEnd_4663498] using wordTrace_append hprefix tailTrace_4663498
  have hstable : (prefixWord ++ tailWord_4663498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663498).length < 2 ^ (prefixWord ++ tailWord_4663498).sum := by decide
  have hdescent : baseEnd_4663498 < baseStart_4663498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663502 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3]
def baseStart_4663502 : Nat := 118140960795 + 4663502 * 2 ^ 59
def prefixEnd_4663502 : Nat := 4983230072969 + 3 ^ 40 * 4663502 * 2
def baseEnd_4663502 : Nat := 2394618059203918260677951

theorem tailTrace_4663502 : CollatzResearch.WordTrace tailWord_4663502 prefixEnd_4663502 2394618059203918260677951 := by
  unfold tailWord_4663502
  simp only [CollatzResearch.WordTrace]
  refine ⟨21261486443867023947134095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113394594367290794384715173 21261486443867023947134095)
  ·
    refine ⟨31892229665800535920701143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21261486443867023947134095 31892229665800535920701143)
    ·
      refine ⟨47838344498700803881051715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31892229665800535920701143 47838344498700803881051715)
      ·
        refine ⟨71757516748051205821577573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47838344498700803881051715 71757516748051205821577573)
        ·
          refine ⟨13454534390259601091545795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71757516748051205821577573 13454534390259601091545795)
          ·
            refine ⟨20181801585389401637318693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13454534390259601091545795 20181801585389401637318693)
            ·
              refine ⟨3784087797260512806997255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20181801585389401637318693 3784087797260512806997255)
              ·
                refine ⟨5676131695890769210495883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784087797260512806997255 5676131695890769210495883)
                ·
                  refine ⟨8514197543836153815743825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5676131695890769210495883 8514197543836153815743825)
                  ·
                    refine ⟨6385648157877115361807869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8514197543836153815743825 6385648157877115361807869)
                    ·
                      refine ⟨2394618059203918260677951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6385648157877115361807869 2394618059203918260677951)
                      ·
                        rfl

theorem cell23_4663502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_4663502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663502 prefixEnd_4663502 := by exact prefixLift 4663502
  have htrace : WordTrace (prefixWord ++ tailWord_4663502) baseStart_4663502 baseEnd_4663502 := by
    simpa [prefixWord, tailWord_4663502, baseEnd_4663502] using wordTrace_append hprefix tailTrace_4663502
  have hstable : (prefixWord ++ tailWord_4663502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663502).length < 2 ^ (prefixWord ++ tailWord_4663502).sum := by decide
  have hdescent : baseEnd_4663502 < baseStart_4663502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663509 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 2, 4]
def baseStart_4663509 : Nat := 118140960795 + 4663509 * 2 ^ 59
def prefixEnd_4663509 : Nat := 4983230072969 + 3 ^ 40 * 4663509 * 2
def baseEnd_4663509 : Nat := 798207217856166577763473

theorem tailTrace_4663509 : CollatzResearch.WordTrace tailWord_4663509 prefixEnd_4663509 798207217856166577763473 := by
  unfold tailWord_4663509
  simp only [CollatzResearch.WordTrace]
  refine ⟨170092146861910831772577581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113394764574607221181718387 170092146861910831772577581)
  ·
    refine ⟨63784555073216561914716593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170092146861910831772577581 63784555073216561914716593)
    ·
      refine ⟨47838416304912421436037445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63784555073216561914716593 47838416304912421436037445)
      ·
        refine ⟨8969703057171079019257021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47838416304912421436037445 8969703057171079019257021)
        ·
          refine ⟨3363638646439154632221383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8969703057171079019257021 3363638646439154632221383)
          ·
            refine ⟨5045457969658731948332075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363638646439154632221383 5045457969658731948332075)
            ·
              refine ⟨7568186954488097922498113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045457969658731948332075 7568186954488097922498113)
              ·
                refine ⟨5676140215866073441873585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7568186954488097922498113 5676140215866073441873585)
                ·
                  refine ⟨4257105161899555081405189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5676140215866073441873585 4257105161899555081405189)
                  ·
                    refine ⟨798207217856166577763473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4257105161899555081405189 798207217856166577763473)
                    ·
                      rfl

theorem cell23_4663509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_4663509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663509 prefixEnd_4663509 := by exact prefixLift 4663509
  have htrace : WordTrace (prefixWord ++ tailWord_4663509) baseStart_4663509 baseEnd_4663509 := by
    simpa [prefixWord, tailWord_4663509, baseEnd_4663509] using wordTrace_append hprefix tailTrace_4663509
  have hstable : (prefixWord ++ tailWord_4663509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663509).length < 2 ^ (prefixWord ++ tailWord_4663509).sum := by decide
  have hdescent : baseEnd_4663509 < baseStart_4663509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663516 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4663516 : Nat := 118140960795 + 4663516 * 2 ^ 59
def prefixEnd_4663516 : Nat := 4983230072969 + 3 ^ 40 * 4663516 * 2
def baseEnd_4663516 : Nat := 2394625247933081205902887

theorem tailTrace_4663516 : CollatzResearch.WordTrace tailWord_4663516 prefixEnd_4663516 2394625247933081205902887 := by
  unfold tailWord_4663516
  simp only [CollatzResearch.WordTrace]
  refine ⟨85046201086442735984041201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113394934781923647978721601 85046201086442735984041201)
  ·
    refine ⟨63784650814832051988030901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85046201086442735984041201 63784650814832051988030901)
    ·
      refine ⟨5979811013890504873877897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63784650814832051988030901 5979811013890504873877897)
      ·
        refine ⟨4484858260417878655408423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5979811013890504873877897 4484858260417878655408423)
        ·
          refine ⟨6727287390626817983112635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4484858260417878655408423 6727287390626817983112635)
          ·
            refine ⟨10090931085940226974668953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6727287390626817983112635 10090931085940226974668953)
            ·
              refine ⟨7568198314455170231001715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10090931085940226974668953 7568198314455170231001715)
              ·
                refine ⟨11352297471682755346502573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7568198314455170231001715 11352297471682755346502573)
                ·
                  refine ⟨4257111551881033254938465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11352297471682755346502573 4257111551881033254938465)
                  ·
                    refine ⟨3192833663910774941203849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257111551881033254938465 3192833663910774941203849)
                    ·
                      refine ⟨2394625247933081205902887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192833663910774941203849 2394625247933081205902887)
                      ·
                        rfl

theorem cell23_4663516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4663516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663516 prefixEnd_4663516 := by exact prefixLift 4663516
  have htrace : WordTrace (prefixWord ++ tailWord_4663516) baseStart_4663516 baseEnd_4663516 := by
    simpa [prefixWord, tailWord_4663516, baseEnd_4663516] using wordTrace_append hprefix tailTrace_4663516
  have hstable : (prefixWord ++ tailWord_4663516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663516).length < 2 ^ (prefixWord ++ tailWord_4663516).sum := by decide
  have hdescent : baseEnd_4663516 < baseStart_4663516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663531 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 2, 6]
def baseStart_4663531 : Nat := 118140960795 + 4663531 * 2 ^ 59
def prefixEnd_4663531 : Nat := 4983230072969 + 3 ^ 40 * 4663531 * 2
def baseEnd_4663531 : Nat := 798210983380966215738439

theorem tailTrace_4663531 : CollatzResearch.WordTrace tailWord_4663531 prefixEnd_4663531 798210983380966215738439 := by
  unfold tailWord_4663531
  simp only [CollatzResearch.WordTrace]
  refine ⟨170092949267831129529878447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113395299511887419686585631 170092949267831129529878447)
  ·
    refine ⟨255139423901746694294817671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170092949267831129529878447 255139423901746694294817671)
    ·
      refine ⟨382709135852620041442226507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255139423901746694294817671 382709135852620041442226507)
      ·
        refine ⟨574063703778930062163339761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382709135852620041442226507 574063703778930062163339761)
        ·
          refine ⟨430547777834197546622504821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 574063703778930062163339761 430547777834197546622504821)
          ·
            refine ⟨40363854171956019995859827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 430547777834197546622504821 40363854171956019995859827)
            ·
              refine ⟨60545781257934029993789741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40363854171956019995859827 60545781257934029993789741)
              ·
                refine ⟨22704667971725261247671153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60545781257934029993789741 22704667971725261247671153)
                ·
                  refine ⟨17028500978793945935753365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22704667971725261247671153 17028500978793945935753365)
                  ·
                    refine ⟨798210983380966215738439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17028500978793945935753365 798210983380966215738439)
                    ·
                      rfl

theorem cell23_4663531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 6].length) (baseStart_4663531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663531 prefixEnd_4663531 := by exact prefixLift 4663531
  have htrace : WordTrace (prefixWord ++ tailWord_4663531) baseStart_4663531 baseEnd_4663531 := by
    simpa [prefixWord, tailWord_4663531, baseEnd_4663531] using wordTrace_append hprefix tailTrace_4663531
  have hstable : (prefixWord ++ tailWord_4663531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663531).length < 2 ^ (prefixWord ++ tailWord_4663531).sum := by decide
  have hdescent : baseEnd_4663531 < baseStart_4663531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663532 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 3]
def baseStart_4663532 : Nat := 118140960795 + 4663532 * 2 ^ 59
def prefixEnd_4663532 : Nat := 4983230072969 + 3 ^ 40 * 4663532 * 2
def baseEnd_4663532 : Nat := 2394633463623553143302813

theorem tailTrace_4663532 : CollatzResearch.WordTrace tailWord_4663532 prefixEnd_4663532 2394633463623553143302813 := by
  unfold tailWord_4663532
  simp only [CollatzResearch.WordTrace]
  refine ⟨85046492870413753350332425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113395323827218337800443233 85046492870413753350332425)
  ·
    refine ⟨63784869652810315012749319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85046492870413753350332425 63784869652810315012749319)
    ·
      refine ⟨95677304479215472519123979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63784869652810315012749319 95677304479215472519123979)
      ·
        refine ⟨143515956718823208778685969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95677304479215472519123979 143515956718823208778685969)
        ·
          refine ⟨107636967539117406584014477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143515956718823208778685969 107636967539117406584014477)
          ·
            refine ⟨40363862827169027469005429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107636967539117406584014477 40363862827169027469005429)
            ·
              refine ⟨3784112140047096325219259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40363862827169027469005429 3784112140047096325219259)
              ·
                refine ⟨5676168210070644487828889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784112140047096325219259 5676168210070644487828889)
                ·
                  refine ⟨4257126157552983365871667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5676168210070644487828889 4257126157552983365871667)
                  ·
                    refine ⟨6385689236329475048807501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4257126157552983365871667 6385689236329475048807501)
                    ·
                      refine ⟨2394633463623553143302813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6385689236329475048807501 2394633463623553143302813)
                      ·
                        rfl

theorem cell23_4663532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 3].length) (baseStart_4663532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663532 prefixEnd_4663532 := by exact prefixLift 4663532
  have htrace : WordTrace (prefixWord ++ tailWord_4663532) baseStart_4663532 baseEnd_4663532 := by
    simpa [prefixWord, tailWord_4663532, baseEnd_4663532] using wordTrace_append hprefix tailTrace_4663532
  have hstable : (prefixWord ++ tailWord_4663532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663532).length < 2 ^ (prefixWord ++ tailWord_4663532).sum := by decide
  have hdescent : baseEnd_4663532 < baseStart_4663532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663542 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_4663542 : Nat := 118140960795 + 4663542 * 2 ^ 59
def prefixEnd_4663542 : Nat := 4983230072969 + 3 ^ 40 * 4663542 * 2
def baseEnd_4663542 : Nat := 2394638598430098104177767

theorem tailTrace_4663542 : CollatzResearch.WordTrace tailWord_4663542 prefixEnd_4663542 2394638598430098104177767 := by
  unfold tailWord_4663542
  simp only [CollatzResearch.WordTrace]
  refine ⟨10630834404424454900533055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113395566980527518939019253 10630834404424454900533055)
  ·
    refine ⟨15946251606636682350799583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10630834404424454900533055 15946251606636682350799583)
    ·
      refine ⟨23919377409955023526199375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15946251606636682350799583 23919377409955023526199375)
      ·
        refine ⟨35879066114932535289299063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23919377409955023526199375 35879066114932535289299063)
        ·
          refine ⟨53818599172398802933948595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35879066114932535289299063 53818599172398802933948595)
          ·
            refine ⟨80727898758598204400922893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53818599172398802933948595 80727898758598204400922893)
            ·
              refine ⟨30272962034474326650346085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80727898758598204400922893 30272962034474326650346085)
              ·
                refine ⟨5676180381463936246939891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30272962034474326650346085 5676180381463936246939891)
                ·
                  refine ⟨8514270572195904370409837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5676180381463936246939891 8514270572195904370409837)
                  ·
                    refine ⟨3192851464573464138903689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8514270572195904370409837 3192851464573464138903689)
                    ·
                      refine ⟨2394638598430098104177767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192851464573464138903689 2394638598430098104177767)
                      ·
                        rfl

theorem cell23_4663542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_4663542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663542 prefixEnd_4663542 := by exact prefixLift 4663542
  have htrace : WordTrace (prefixWord ++ tailWord_4663542) baseStart_4663542 baseEnd_4663542 := by
    simpa [prefixWord, tailWord_4663542, baseEnd_4663542] using wordTrace_append hprefix tailTrace_4663542
  have hstable : (prefixWord ++ tailWord_4663542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663542).length < 2 ^ (prefixWord ++ tailWord_4663542).sum := by decide
  have hdescent : baseEnd_4663542 < baseStart_4663542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663555 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 6, 2, 2]
def baseStart_4663555 : Nat := 118140960795 + 4663555 * 2 ^ 59
def prefixEnd_4663555 : Nat := 4983230072969 + 3 ^ 40 * 4663555 * 2
def baseEnd_4663555 : Nat := 2394645273678606553315207

theorem tailTrace_4663555 : CollatzResearch.WordTrace tailWord_4663555 prefixEnd_4663555 2394645273678606553315207 := by
  unfold tailWord_4663555
  simp only [CollatzResearch.WordTrace]
  refine ⟨170093824619744181628752119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113395883079829454419168079 170093824619744181628752119)
  ·
    refine ⟨255140736929616272443128179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170093824619744181628752119 255140736929616272443128179)
    ·
      refine ⟨382711105394424408664692269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255140736929616272443128179 382711105394424408664692269)
      ·
        refine ⟨143516664522909153249259601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 382711105394424408664692269 143516664522909153249259601)
        ·
          refine ⟨107637498392181864936944701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143516664522909153249259601 107637498392181864936944701)
          ·
            refine ⟨40364061897068199351354263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107637498392181864936944701 40364061897068199351354263)
            ·
              refine ⟨60546092845602299027031395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40364061897068199351354263 60546092845602299027031395)
              ·
                refine ⟨90819139268403448540547093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60546092845602299027031395 90819139268403448540547093)
                ·
                  refine ⟨4257147153206411650338145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90819139268403448540547093 4257147153206411650338145)
                  ·
                    refine ⟨3192860364904808737753609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257147153206411650338145 3192860364904808737753609)
                    ·
                      refine ⟨2394645273678606553315207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192860364904808737753609 2394645273678606553315207)
                      ·
                        rfl

theorem cell23_4663555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 2, 2].length) (baseStart_4663555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663555 prefixEnd_4663555 := by exact prefixLift 4663555
  have htrace : WordTrace (prefixWord ++ tailWord_4663555) baseStart_4663555 baseEnd_4663555 := by
    simpa [prefixWord, tailWord_4663555, baseEnd_4663555] using wordTrace_append hprefix tailTrace_4663555
  have hstable : (prefixWord ++ tailWord_4663555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663555).length < 2 ^ (prefixWord ++ tailWord_4663555).sum := by decide
  have hdescent : baseEnd_4663555 < baseStart_4663555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663589 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 2, 2, 2]
def baseStart_4663589 : Nat := 118140960795 + 4663589 * 2 ^ 59
def prefixEnd_4663589 : Nat := 4983230072969 + 3 ^ 40 * 4663589 * 2
def baseEnd_4663589 : Nat := 2394662732020859420290051

theorem tailTrace_4663589 : CollatzResearch.WordTrace tailWord_4663589 prefixEnd_4663589 2394662732020859420290051 := by
  unfold tailWord_4663589
  simp only [CollatzResearch.WordTrace]
  refine ⟨170095064701621005435489821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113396709801080670290326547 170095064701621005435489821)
  ·
    refine ⟨63785649263107877038308683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170095064701621005435489821 63785649263107877038308683)
    ·
      refine ⟨95678473894661815557463025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63785649263107877038308683 95678473894661815557463025)
      ·
        refine ⟨71758855420996361668097269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95678473894661815557463025 71758855420996361668097269)
        ·
          refine ⟨6727392695718408906384119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71758855420996361668097269 6727392695718408906384119)
          ·
            refine ⟨10091089043577613359576179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6727392695718408906384119 10091089043577613359576179)
            ·
              refine ⟨15136633565366420039364269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10091089043577613359576179 15136633565366420039364269)
              ·
                refine ⟨5676237587012407514761601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15136633565366420039364269 5676237587012407514761601)
                ·
                  refine ⟨4257178190259305636071201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5676237587012407514761601 4257178190259305636071201)
                  ·
                    refine ⟨3192883642694479227053401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257178190259305636071201 3192883642694479227053401)
                    ·
                      refine ⟨2394662732020859420290051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192883642694479227053401 2394662732020859420290051)
                      ·
                        rfl

theorem cell23_4663589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_4663589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663589 prefixEnd_4663589 := by exact prefixLift 4663589
  have htrace : WordTrace (prefixWord ++ tailWord_4663589) baseStart_4663589 baseEnd_4663589 := by
    simpa [prefixWord, tailWord_4663589, baseEnd_4663589] using wordTrace_append hprefix tailTrace_4663589
  have hstable : (prefixWord ++ tailWord_4663589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663589).length < 2 ^ (prefixWord ++ tailWord_4663589).sum := by decide
  have hdescent : baseEnd_4663589 < baseStart_4663589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663608 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 2, 5]
def baseStart_4663608 : Nat := 118140960795 + 4663608 * 2 ^ 59
def prefixEnd_4663608 : Nat := 4983230072969 + 3 ^ 40 * 4663608 * 2
def baseEnd_4663608 : Nat := 798224162717764948650821

theorem tailTrace_4663608 : CollatzResearch.WordTrace tailWord_4663608 prefixEnd_4663608 798224162717764948650821 := by
  unfold tailWord_4663608
  simp only [CollatzResearch.WordTrace]
  refine ⟨85047878844276085840215739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113397171792368114453620985 85047878844276085840215739)
  ·
    refine ⟨127571818266414128760323609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85047878844276085840215739 127571818266414128760323609)
    ·
      refine ⟨95678863699810596570242707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127571818266414128760323609 95678863699810596570242707)
      ·
        refine ⟨143518295549715894855364061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95678863699810596570242707 143518295549715894855364061)
        ·
          refine ⟨53819360831143460570761523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143518295549715894855364061 53819360831143460570761523)
          ·
            refine ⟨80729041246715190856142285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53819360831143460570761523 80729041246715190856142285)
            ·
              refine ⟨30273390467518196571053357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80729041246715190856142285 30273390467518196571053357)
              ·
                refine ⟨11352521425319323714145009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30273390467518196571053357 11352521425319323714145009)
                ·
                  refine ⟨8514391068989492785608757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11352521425319323714145009 8514391068989492785608757)
                  ·
                    refine ⟨798224162717764948650821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8514391068989492785608757 798224162717764948650821)
                    ·
                      rfl

theorem cell23_4663608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_4663608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663608 prefixEnd_4663608 := by exact prefixLift 4663608
  have htrace : WordTrace (prefixWord ++ tailWord_4663608) baseStart_4663608 baseEnd_4663608 := by
    simpa [prefixWord, tailWord_4663608, baseEnd_4663608] using wordTrace_append hprefix tailTrace_4663608
  have hstable : (prefixWord ++ tailWord_4663608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663608).length < 2 ^ (prefixWord ++ tailWord_4663608).sum := by decide
  have hdescent : baseEnd_4663608 < baseStart_4663608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663646 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_4663646 : Nat := 118140960795 + 4663646 * 2 ^ 59
def prefixEnd_4663646 : Nat := 4983230072969 + 3 ^ 40 * 4663646 * 2
def baseEnd_4663646 : Nat := 266076888935351744141921

theorem tailTrace_4663646 : CollatzResearch.WordTrace tailWord_4663646 prefixEnd_4663646 266076888935351744141921 := by
  unfold tailWord_4663646
  simp only [CollatzResearch.WordTrace]
  refine ⟨21262142957801813021289349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113398095774943002780209861 21262142957801813021289349)
  ·
    refine ⟨3986651804587839941491753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21262142957801813021289349 3986651804587839941491753)
    ·
      refine ⟨2989988853440879956118815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3986651804587839941491753 2989988853440879956118815)
      ·
        refine ⟨4484983280161319934178223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2989988853440879956118815 4484983280161319934178223)
        ·
          refine ⟨6727474920241979901267335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4484983280161319934178223 6727474920241979901267335)
          ·
            refine ⟨10091212380362969851901003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6727474920241979901267335 10091212380362969851901003)
            ·
              refine ⟨15136818570544454777851505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10091212380362969851901003 15136818570544454777851505)
              ·
                refine ⟨11352613927908341083388629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15136818570544454777851505 11352613927908341083388629)
                ·
                  refine ⟨266076888935351744141921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11352613927908341083388629 266076888935351744141921)
                  ·
                    rfl

theorem cell23_4663646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_4663646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663646 prefixEnd_4663646 := by exact prefixLift 4663646
  have htrace : WordTrace (prefixWord ++ tailWord_4663646) baseStart_4663646 baseEnd_4663646 := by
    simpa [prefixWord, tailWord_4663646, baseEnd_4663646] using wordTrace_append hprefix tailTrace_4663646
  have hstable : (prefixWord ++ tailWord_4663646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663646).length < 2 ^ (prefixWord ++ tailWord_4663646).sum := by decide
  have hdescent : baseEnd_4663646 < baseStart_4663646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663655 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 5, 4]
def baseStart_4663655 : Nat := 118140960795 + 4663655 * 2 ^ 59
def prefixEnd_4663655 : Nat := 4983230072969 + 3 ^ 40 * 4663655 * 2
def baseEnd_4663655 : Nat := 798232207248018720688249

theorem tailTrace_4663655 : CollatzResearch.WordTrace tailWord_4663655 prefixEnd_4663655 798232207248018720688249 := by
  unfold tailWord_4663655
  simp only [CollatzResearch.WordTrace]
  refine ⟨170097471919381898707392419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113398314612921265804928279 170097471919381898707392419)
  ·
    refine ⟨255146207879072848061088629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170097471919381898707392419 255146207879072848061088629)
    ·
      refine ⟨23919956988663079505727059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 255146207879072848061088629 23919956988663079505727059)
      ·
        refine ⟨35879935482994619258590589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23919956988663079505727059 35879935482994619258590589)
        ·
          refine ⟨13454975806122982221971471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35879935482994619258590589 13454975806122982221971471)
          ·
            refine ⟨20182463709184473332957207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13454975806122982221971471 20182463709184473332957207)
            ·
              refine ⟨30273695563776709999435811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20182463709184473332957207 30273695563776709999435811)
              ·
                refine ⟨45410543345665064999153717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30273695563776709999435811 45410543345665064999153717)
                ·
                  refine ⟨4257238438656099843670661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45410543345665064999153717 4257238438656099843670661)
                  ·
                    refine ⟨798232207248018720688249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4257238438656099843670661 798232207248018720688249)
                    ·
                      rfl

theorem cell23_4663655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_4663655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663655 prefixEnd_4663655 := by exact prefixLift 4663655
  have htrace : WordTrace (prefixWord ++ tailWord_4663655) baseStart_4663655 baseEnd_4663655 := by
    simpa [prefixWord, tailWord_4663655, baseEnd_4663655] using wordTrace_append hprefix tailTrace_4663655
  have hstable : (prefixWord ++ tailWord_4663655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663655).length < 2 ^ (prefixWord ++ tailWord_4663655).sum := by decide
  have hdescent : baseEnd_4663655 < baseStart_4663655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663688 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_4663688 : Nat := 118140960795 + 4663688 * 2 ^ 59
def prefixEnd_4663688 : Nat := 4983230072969 + 3 ^ 40 * 4663688 * 2
def baseEnd_4663688 : Nat := 2394713566605654532952095

theorem tailTrace_4663688 : CollatzResearch.WordTrace tailWord_4663688 prefixEnd_4663688 2394713566605654532952095 := by
  unfold tailWord_4663688
  simp only [CollatzResearch.WordTrace]
  refine ⟨85049337764131172671671859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113399117018841563562229145 85049337764131172671671859)
  ·
    refine ⟨127574006646196759007507789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85049337764131172671671859 127574006646196759007507789)
    ·
      refine ⟨47840252492323784627815421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127574006646196759007507789 47840252492323784627815421)
      ·
        refine ⟨17940094684621419235430783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47840252492323784627815421 17940094684621419235430783)
        ·
          refine ⟨26910142026932128853146175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17940094684621419235430783 26910142026932128853146175)
          ·
            refine ⟨40365213040398193279719263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26910142026932128853146175 40365213040398193279719263)
            ·
              refine ⟨60547819560597289919578895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40365213040398193279719263 60547819560597289919578895)
              ·
                refine ⟨90821729340895934879368343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60547819560597289919578895 90821729340895934879368343)
                ·
                  refine ⟨136232594011343902319052515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90821729340895934879368343 136232594011343902319052515)
                  ·
                    refine ⟨204348891017015853478578773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136232594011343902319052515 204348891017015853478578773)
                    ·
                      refine ⟨2394713566605654532952095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 204348891017015853478578773 2394713566605654532952095)
                      ·
                        rfl

theorem cell23_4663688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_4663688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663688 prefixEnd_4663688 := by exact prefixLift 4663688
  have htrace : WordTrace (prefixWord ++ tailWord_4663688) baseStart_4663688 baseEnd_4663688 := by
    simpa [prefixWord, tailWord_4663688, baseEnd_4663688] using wordTrace_append hprefix tailTrace_4663688
  have hstable : (prefixWord ++ tailWord_4663688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663688).length < 2 ^ (prefixWord ++ tailWord_4663688).sum := by decide
  have hdescent : baseEnd_4663688 < baseStart_4663688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663705 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 3, 5, 2]
def baseStart_4663705 : Nat := 118140960795 + 4663705 * 2 ^ 59
def prefixEnd_4663705 : Nat := 4983230072969 + 3 ^ 40 * 4663705 * 2
def baseEnd_4663705 : Nat := 2394722295776780966439517

theorem tailTrace_4663705 : CollatzResearch.WordTrace tailWord_4663705 prefixEnd_4663705 2394722295776780966439517 := by
  unfold tailWord_4663705
  simp only [CollatzResearch.WordTrace]
  refine ⟨170099295569200757246712569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113399530379467171497808379 170099295569200757246712569)
  ·
    refine ⟨127574471676900567935034427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170099295569200757246712569 127574471676900567935034427)
    ·
      refine ⟨191361707515350851902551641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127574471676900567935034427 191361707515350851902551641)
      ·
        refine ⟨143521280636513138926913731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191361707515350851902551641 143521280636513138926913731)
        ·
          refine ⟨215281920954769708390370597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143521280636513138926913731 215281920954769708390370597)
          ·
            refine ⟨40365360179019320323194487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215281920954769708390370597 40365360179019320323194487)
            ·
              refine ⟨60548040268528980484791731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40365360179019320323194487 60548040268528980484791731)
              ·
                refine ⟨90822060402793470727187597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60548040268528980484791731 90822060402793470727187597)
                ·
                  refine ⟨34058272651047551522695349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90822060402793470727187597 34058272651047551522695349)
                  ·
                    refine ⟨3192963061035707955252689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34058272651047551522695349 3192963061035707955252689)
                    ·
                      refine ⟨2394722295776780966439517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3192963061035707955252689 2394722295776780966439517)
                      ·
                        rfl

theorem cell23_4663705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 5, 2].length) (baseStart_4663705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663705 prefixEnd_4663705 := by exact prefixLift 4663705
  have htrace : WordTrace (prefixWord ++ tailWord_4663705) baseStart_4663705 baseEnd_4663705 := by
    simpa [prefixWord, tailWord_4663705, baseEnd_4663705] using wordTrace_append hprefix tailTrace_4663705
  have hstable : (prefixWord ++ tailWord_4663705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663705).length < 2 ^ (prefixWord ++ tailWord_4663705).sum := by decide
  have hdescent : baseEnd_4663705 < baseStart_4663705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663712 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 3, 1, 3]
def baseStart_4663712 : Nat := 118140960795 + 4663712 * 2 ^ 59
def prefixEnd_4663712 : Nat := 4983230072969 + 3 ^ 40 * 4663712 * 2
def baseEnd_4663712 : Nat := 2394725890141362439051985

theorem tailTrace_4663712 : CollatzResearch.WordTrace tailWord_4663712 prefixEnd_4663712 2394725890141362439051985 := by
  unfold tailWord_4663712
  simp only [CollatzResearch.WordTrace]
  refine ⟨85049775440087698721108695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113399700586783598294811593 85049775440087698721108695)
  ·
    refine ⟨127574663160131548081663043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85049775440087698721108695 127574663160131548081663043)
    ·
      refine ⟨191361994740197322122494565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127574663160131548081663043 191361994740197322122494565)
      ·
        refine ⟨35880374013786997897967731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191361994740197322122494565 35880374013786997897967731)
        ·
          refine ⟨53820561020680496846951597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35880374013786997897967731 53820561020680496846951597)
          ·
            refine ⟨20182710382755186317606849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53820561020680496846951597 20182710382755186317606849)
            ·
              refine ⟨15137032787066389738205137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20182710382755186317606849 15137032787066389738205137)
              ·
                refine ⟨11352774590299792303653853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15137032787066389738205137 11352774590299792303653853)
                ·
                  refine ⟨4257290471362422113870195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11352774590299792303653853 4257290471362422113870195)
                  ·
                    refine ⟨6385935707043633170805293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4257290471362422113870195 6385935707043633170805293)
                    ·
                      refine ⟨2394725890141362439051985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6385935707043633170805293 2394725890141362439051985)
                      ·
                        rfl

theorem cell23_4663712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_4663712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663712 prefixEnd_4663712 := by exact prefixLift 4663712
  have htrace : WordTrace (prefixWord ++ tailWord_4663712) baseStart_4663712 baseEnd_4663712 := by
    simpa [prefixWord, tailWord_4663712, baseEnd_4663712] using wordTrace_append hprefix tailTrace_4663712
  have hstable : (prefixWord ++ tailWord_4663712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663712).length < 2 ^ (prefixWord ++ tailWord_4663712).sum := by decide
  have hdescent : baseEnd_4663712 < baseStart_4663712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663715 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 1, 5]
def baseStart_4663715 : Nat := 118140960795 + 4663715 * 2 ^ 59
def prefixEnd_4663715 : Nat := 4983230072969 + 3 ^ 40 * 4663715 * 2
def baseEnd_4663715 : Nat := 798242476861108642438157

theorem tailTrace_4663715 : CollatzResearch.WordTrace tailWord_4663715 prefixEnd_4663715 798242476861108642438157 := by
  unfold tailWord_4663715
  simp only [CollatzResearch.WordTrace]
  refine ⟨170099660299164528954576599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113399773532776352636384399 170099660299164528954576599)
  ·
    refine ⟨255149490448746793431864899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170099660299164528954576599 255149490448746793431864899)
    ·
      refine ⟨382724235673120190147797349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255149490448746793431864899 382724235673120190147797349)
      ·
        refine ⟨71760794188710035652712003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 382724235673120190147797349 71760794188710035652712003)
        ·
          refine ⟨107641191283065053479068005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71760794188710035652712003 107641191283065053479068005)
          ·
            refine ⟨20182723365574697527325251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107641191283065053479068005 20182723365574697527325251)
            ·
              refine ⟨30274085048362046290987877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20182723365574697527325251 30274085048362046290987877)
              ·
                refine ⟨5676390946567883679560227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30274085048362046290987877 5676390946567883679560227)
                ·
                  refine ⟨8514586419851825519340341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5676390946567883679560227 8514586419851825519340341)
                  ·
                    refine ⟨798242476861108642438157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8514586419851825519340341 798242476861108642438157)
                    ·
                      rfl

theorem cell23_4663715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 5].length) (baseStart_4663715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663715 prefixEnd_4663715 := by exact prefixLift 4663715
  have htrace : WordTrace (prefixWord ++ tailWord_4663715) baseStart_4663715 baseEnd_4663715 := by
    simpa [prefixWord, tailWord_4663715, baseEnd_4663715] using wordTrace_append hprefix tailTrace_4663715
  have hstable : (prefixWord ++ tailWord_4663715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663715).length < 2 ^ (prefixWord ++ tailWord_4663715).sum := by decide
  have hdescent : baseEnd_4663715 < baseStart_4663715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663755 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 3]
def baseStart_4663755 : Nat := 118140960795 + 4663755 * 2 ^ 59
def prefixEnd_4663755 : Nat := 4983230072969 + 3 ^ 40 * 4663755 * 2
def baseEnd_4663755 : Nat := 2394747969809505770814287

theorem tailTrace_4663755 : CollatzResearch.WordTrace tailWord_4663755 prefixEnd_4663755 2394747969809505770814287 := by
  unfold tailWord_4663755
  simp only [CollatzResearch.WordTrace]
  refine ⟨170101119219019615786032719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113400746146013077190688479 170101119219019615786032719)
  ·
    refine ⟨255151678828529423679049079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170101119219019615786032719 255151678828529423679049079)
    ·
      refine ⟨382727518242794135518573619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255151678828529423679049079 382727518242794135518573619)
      ·
        refine ⟨574091277364191203277860429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382727518242794135518573619 574091277364191203277860429)
        ·
          refine ⟨215284229011571701229197661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 574091277364191203277860429 215284229011571701229197661)
          ·
            refine ⟨80731585879339387960949123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215284229011571701229197661 80731585879339387960949123)
            ·
              refine ⟨121097378819009081941423685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80731585879339387960949123 121097378819009081941423685)
              ·
                refine ⟨22705758528564202864016941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121097378819009081941423685 22705758528564202864016941)
                ·
                  refine ⟨8514659448211576074006353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22705758528564202864016941 8514659448211576074006353)
                  ·
                    refine ⟨6385994586158682055504765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8514659448211576074006353 6385994586158682055504765)
                    ·
                      refine ⟨2394747969809505770814287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6385994586158682055504765 2394747969809505770814287)
                      ·
                        rfl

theorem cell23_4663755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 3].length) (baseStart_4663755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663755 prefixEnd_4663755 := by exact prefixLift 4663755
  have htrace : WordTrace (prefixWord ++ tailWord_4663755) baseStart_4663755 baseEnd_4663755 := by
    simpa [prefixWord, tailWord_4663755, baseEnd_4663755] using wordTrace_append hprefix tailTrace_4663755
  have hstable : (prefixWord ++ tailWord_4663755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663755).length < 2 ^ (prefixWord ++ tailWord_4663755).sum := by decide
  have hdescent : baseEnd_4663755 < baseStart_4663755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663765 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4663765 : Nat := 118140960795 + 4663765 * 2 ^ 59
def prefixEnd_4663765 : Nat := 4983230072969 + 3 ^ 40 * 4663765 * 2
def baseEnd_4663765 : Nat := 2394753104616050731689241

theorem tailTrace_4663765 : CollatzResearch.WordTrace tailWord_4663765 prefixEnd_4663765 2394753104616050731689241 := by
  unfold tailWord_4663765
  simp only [CollatzResearch.WordTrace]
  refine ⟨170101483948983387493896749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113400989299322258329264499 170101483948983387493896749)
  ·
    refine ⟨63788056480868770310211281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170101483948983387493896749 63788056480868770310211281)
    ·
      refine ⟨47841042360651577732658461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63788056480868770310211281 47841042360651577732658461)
      ·
        refine ⟨17940390885244341649746923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47841042360651577732658461 17940390885244341649746923)
        ·
          refine ⟨26910586327866512474620385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17940390885244341649746923 26910586327866512474620385)
          ·
            refine ⟨20182939745899884355965289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26910586327866512474620385 20182939745899884355965289)
            ·
              refine ⟨15137204809424913266973967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20182939745899884355965289 15137204809424913266973967)
              ·
                refine ⟨22705807214137369900460951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15137204809424913266973967 22705807214137369900460951)
                ·
                  refine ⟨34058710821206054850691427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22705807214137369900460951 34058710821206054850691427)
                  ·
                    refine ⟨51088066231809082276037141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34058710821206054850691427 51088066231809082276037141)
                    ·
                      refine ⟨2394753104616050731689241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51088066231809082276037141 2394753104616050731689241)
                      ·
                        rfl

theorem cell23_4663765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4663765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663765 prefixEnd_4663765 := by exact prefixLift 4663765
  have htrace : WordTrace (prefixWord ++ tailWord_4663765) baseStart_4663765 baseEnd_4663765 := by
    simpa [prefixWord, tailWord_4663765, baseEnd_4663765] using wordTrace_append hprefix tailTrace_4663765
  have hstable : (prefixWord ++ tailWord_4663765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663765).length < 2 ^ (prefixWord ++ tailWord_4663765).sum := by decide
  have hdescent : baseEnd_4663765 < baseStart_4663765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663789 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_4663789 : Nat := 118140960795 + 4663789 * 2 ^ 59
def prefixEnd_4663789 : Nat := 4983230072969 + 3 ^ 40 * 4663789 * 2
def baseEnd_4663789 : Nat := 2394765428151758637789131

theorem tailTrace_4663789 : CollatzResearch.WordTrace tailWord_4663789 prefixEnd_4663789 2394765428151758637789131 := by
  unfold tailWord_4663789
  simp only [CollatzResearch.WordTrace]
  refine ⟨170102359300896439592770421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113401572867264293061846947 170102359300896439592770421)
  ·
    refine ⟨15947096184459041211822227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170102359300896439592770421 15947096184459041211822227)
    ·
      refine ⟨23920644276688561817733341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15947096184459041211822227 23920644276688561817733341)
      ·
        refine ⟨8970241603758210681650003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23920644276688561817733341 8970241603758210681650003)
        ·
          refine ⟨13455362405637316022475005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8970241603758210681650003 13455362405637316022475005)
          ·
            refine ⟨5045760902113993508428127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13455362405637316022475005 5045760902113993508428127)
            ·
              refine ⟨7568641353170990262642191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045760902113993508428127 7568641353170990262642191)
              ·
                refine ⟨11352962029756485393963287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7568641353170990262642191 11352962029756485393963287)
                ·
                  refine ⟨17029443044634728090944931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11352962029756485393963287 17029443044634728090944931)
                  ·
                    refine ⟨25544164566952092136417397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17029443044634728090944931 25544164566952092136417397)
                    ·
                      refine ⟨2394765428151758637789131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25544164566952092136417397 2394765428151758637789131)
                      ·
                        rfl

theorem cell23_4663789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_4663789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663789 prefixEnd_4663789 := by exact prefixLift 4663789
  have htrace : WordTrace (prefixWord ++ tailWord_4663789) baseStart_4663789 baseEnd_4663789 := by
    simpa [prefixWord, tailWord_4663789, baseEnd_4663789] using wordTrace_append hprefix tailTrace_4663789
  have hstable : (prefixWord ++ tailWord_4663789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663789).length < 2 ^ (prefixWord ++ tailWord_4663789).sum := by decide
  have hdescent : baseEnd_4663789 < baseStart_4663789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663797 : List Nat := [1, 3, 5, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_4663797 : Nat := 118140960795 + 4663797 * 2 ^ 59
def prefixEnd_4663797 : Nat := 4983230072969 + 3 ^ 40 * 4663797 * 2
def baseEnd_4663797 : Nat := 2394769535996994606489095

theorem tailTrace_4663797 : CollatzResearch.WordTrace tailWord_4663797 prefixEnd_4663797 2394769535996994606489095 := by
  unfold tailWord_4663797
  simp only [CollatzResearch.WordTrace]
  refine ⟨170102651084867456959061645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113401767389911637972707763 170102651084867456959061645)
  ·
    refine ⟨63788494156825296359648117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170102651084867456959061645 63788494156825296359648117)
    ·
      refine ⟨5980171327202371533717011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63788494156825296359648117 5980171327202371533717011)
      ·
        refine ⟨8970256990803557300575517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5980171327202371533717011 8970256990803557300575517)
        ·
          refine ⟨3363846371551333987715819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8970256990803557300575517 3363846371551333987715819)
          ·
            refine ⟨5045769557327000981573729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363846371551333987715819 5045769557327000981573729)
            ·
              refine ⟨3784327167995250736180297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5045769557327000981573729 3784327167995250736180297)
              ·
                refine ⟨2838245375996438052135223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3784327167995250736180297 2838245375996438052135223)
                ·
                  refine ⟨4257368063994657078202835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2838245375996438052135223 4257368063994657078202835)
                  ·
                    refine ⟨6386052095991985617304253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4257368063994657078202835 6386052095991985617304253)
                    ·
                      refine ⟨2394769535996994606489095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6386052095991985617304253 2394769535996994606489095)
                      ·
                        rfl

theorem cell23_4663797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_4663797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663797 prefixEnd_4663797 := by exact prefixLift 4663797
  have htrace : WordTrace (prefixWord ++ tailWord_4663797) baseStart_4663797 baseEnd_4663797 := by
    simpa [prefixWord, tailWord_4663797, baseEnd_4663797] using wordTrace_append hprefix tailTrace_4663797
  have hstable : (prefixWord ++ tailWord_4663797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663797).length < 2 ^ (prefixWord ++ tailWord_4663797).sum := by decide
  have hdescent : baseEnd_4663797 < baseStart_4663797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663819 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 2, 1, 3]
def baseStart_4663819 : Nat := 118140960795 + 4663819 * 2 ^ 59
def prefixEnd_4663819 : Nat := 4983230072969 + 3 ^ 40 * 4663819 * 2
def baseEnd_4663819 : Nat := 2394780832571393520413993

theorem tailTrace_4663819 : CollatzResearch.WordTrace tailWord_4663819 prefixEnd_4663819 2394780832571393520413993 := by
  unfold tailWord_4663819
  simp only [CollatzResearch.WordTrace]
  refine ⟨170103453490787754716362511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113402302327191836477575007 170103453490787754716362511)
  ·
    refine ⟨255155180236181632074543767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170103453490787754716362511 255155180236181632074543767)
    ·
      refine ⟨382732770354272448111815651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255155180236181632074543767 382732770354272448111815651)
      ·
        refine ⟨574099155531408672167723477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382732770354272448111815651 574099155531408672167723477)
        ·
          refine ⟨13455448957767390753931019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 574099155531408672167723477 13455448957767390753931019)
          ·
            refine ⟨20183173436651086130896529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13455448957767390753931019 20183173436651086130896529)
            ·
              refine ⟨15137380077488314598172397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20183173436651086130896529 15137380077488314598172397)
              ·
                refine ⟨5676517529058117974314649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15137380077488314598172397 5676517529058117974314649)
                ·
                  refine ⟨4257388146793588480735987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5676517529058117974314649 4257388146793588480735987)
                  ·
                    refine ⟨6386082220190382721103981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4257388146793588480735987 6386082220190382721103981)
                    ·
                      refine ⟨2394780832571393520413993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6386082220190382721103981 2394780832571393520413993)
                      ·
                        rfl

theorem cell23_4663819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 1, 3].length) (baseStart_4663819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663819 prefixEnd_4663819 := by exact prefixLift 4663819
  have htrace : WordTrace (prefixWord ++ tailWord_4663819) baseStart_4663819 baseEnd_4663819 := by
    simpa [prefixWord, tailWord_4663819, baseEnd_4663819] using wordTrace_append hprefix tailTrace_4663819
  have hstable : (prefixWord ++ tailWord_4663819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663819).length < 2 ^ (prefixWord ++ tailWord_4663819).sum := by decide
  have hdescent : baseEnd_4663819 < baseStart_4663819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663829 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 1, 3, 2]
def baseStart_4663829 : Nat := 118140960795 + 4663829 * 2 ^ 59
def prefixEnd_4663829 : Nat := 4983230072969 + 3 ^ 40 * 4663829 * 2
def baseEnd_4663829 : Nat := 2394785967377938481288947

theorem tailTrace_4663829 : CollatzResearch.WordTrace tailWord_4663829 prefixEnd_4663829 2394785967377938481288947 := by
  unfold tailWord_4663829
  simp only [CollatzResearch.WordTrace]
  refine ⟨170103818220751526424226541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113402545480501017616151027 170103818220751526424226541)
  ·
    refine ⟨63788931832781822409084953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170103818220751526424226541 63788931832781822409084953)
    ·
      refine ⟨47841698874586366806813715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63788931832781822409084953 47841698874586366806813715)
      ·
        refine ⟨71762548311879550210220573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47841698874586366806813715 71762548311879550210220573)
        ·
          refine ⟨26910955616954831328832715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71762548311879550210220573 26910955616954831328832715)
          ·
            refine ⟨40366433425432246993249073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26910955616954831328832715 40366433425432246993249073)
            ·
              refine ⟨30274825069074185244936805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40366433425432246993249073 30274825069074185244936805)
              ·
                refine ⟨5676529700451409733425651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30274825069074185244936805 5676529700451409733425651)
                ·
                  refine ⟨8514794550677114600138477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5676529700451409733425651 8514794550677114600138477)
                  ·
                    refine ⟨3193047956503917975051929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8514794550677114600138477 3193047956503917975051929)
                    ·
                      refine ⟨2394785967377938481288947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193047956503917975051929 2394785967377938481288947)
                      ·
                        rfl

theorem cell23_4663829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_4663829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663829 prefixEnd_4663829 := by exact prefixLift 4663829
  have htrace : WordTrace (prefixWord ++ tailWord_4663829) baseStart_4663829 baseEnd_4663829 := by
    simpa [prefixWord, tailWord_4663829, baseEnd_4663829] using wordTrace_append hprefix tailTrace_4663829
  have hstable : (prefixWord ++ tailWord_4663829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663829).length < 2 ^ (prefixWord ++ tailWord_4663829).sum := by decide
  have hdescent : baseEnd_4663829 < baseStart_4663829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663845 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_4663845 : Nat := 118140960795 + 4663845 * 2 ^ 59
def prefixEnd_4663845 : Nat := 4983230072969 + 3 ^ 40 * 4663845 * 2
def baseEnd_4663845 : Nat := 2394794183068410418688873

theorem tailTrace_4663845 : CollatzResearch.WordTrace tailWord_4663845 prefixEnd_4663845 2394794183068410418688873 := by
  unfold tailWord_4663845
  simp only [CollatzResearch.WordTrace]
  refine ⟨170104401788693561156808989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113402934525795707437872659 170104401788693561156808989)
  ·
    refine ⟨63789150670760085433803371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170104401788693561156808989 63789150670760085433803371)
    ·
      refine ⟨95683726006140128150705057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63789150670760085433803371 95683726006140128150705057)
      ·
        refine ⟨71762794504605096113028793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95683726006140128150705057 71762794504605096113028793)
        ·
          refine ⟨53822095878453822084771595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71762794504605096113028793 53822095878453822084771595)
          ·
            refine ⟨80733143817680733127157393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53822095878453822084771595 80733143817680733127157393)
            ·
              refine ⟨60549857863260549845368045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80733143817680733127157393 60549857863260549845368045)
              ·
                refine ⟨22706196698722706192013017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60549857863260549845368045 22706196698722706192013017)
                ·
                  refine ⟨17029647524042029644009763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22706196698722706192013017 17029647524042029644009763)
                  ·
                    refine ⟨25544471286063044466014645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17029647524042029644009763 25544471286063044466014645)
                    ·
                      refine ⟨2394794183068410418688873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25544471286063044466014645 2394794183068410418688873)
                      ·
                        rfl

theorem cell23_4663845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_4663845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663845 prefixEnd_4663845 := by exact prefixLift 4663845
  have htrace : WordTrace (prefixWord ++ tailWord_4663845) baseStart_4663845 baseEnd_4663845 := by
    simpa [prefixWord, tailWord_4663845, baseEnd_4663845] using wordTrace_append hprefix tailTrace_4663845
  have hstable : (prefixWord ++ tailWord_4663845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663845).length < 2 ^ (prefixWord ++ tailWord_4663845).sum := by decide
  have hdescent : baseEnd_4663845 < baseStart_4663845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663859 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 4, 2, 2]
def baseStart_4663859 : Nat := 118140960795 + 4663859 * 2 ^ 59
def prefixEnd_4663859 : Nat := 4983230072969 + 3 ^ 40 * 4663859 * 2
def baseEnd_4663859 : Nat := 2394801371797573363913809

theorem tailTrace_4663859 : CollatzResearch.WordTrace tailWord_4663859 prefixEnd_4663859 2394801371797573363913809 := by
  unfold tailWord_4663859
  simp only [CollatzResearch.WordTrace]
  refine ⟨170104912410642841547818631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113403274940428561031879087 170104912410642841547818631)
  ·
    refine ⟨255157368615964262321727947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170104912410642841547818631 255157368615964262321727947)
    ·
      refine ⟨382736052923946393482591921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255157368615964262321727947 382736052923946393482591921)
      ·
        refine ⟨287052039692959795111943941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382736052923946393482591921 287052039692959795111943941)
        ·
          refine ⟨53822257442429961583489489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 287052039692959795111943941 53822257442429961583489489)
          ·
            refine ⟨40366693081822471187617117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53822257442429961583489489 40366693081822471187617117)
            ·
              refine ⟨15137509905683426695356419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40366693081822471187617117 15137509905683426695356419)
              ·
                refine ⟨22706264858525140043034629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15137509905683426695356419 22706264858525140043034629)
                ·
                  refine ⟨4257424660973463758068993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22706264858525140043034629 4257424660973463758068993)
                  ·
                    refine ⟨3193068495730097818551745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257424660973463758068993 3193068495730097818551745)
                    ·
                      refine ⟨2394801371797573363913809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193068495730097818551745 2394801371797573363913809)
                      ·
                        rfl

theorem cell23_4663859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 2, 2].length) (baseStart_4663859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663859 prefixEnd_4663859 := by exact prefixLift 4663859
  have htrace : WordTrace (prefixWord ++ tailWord_4663859) baseStart_4663859 baseEnd_4663859 := by
    simpa [prefixWord, tailWord_4663859, baseEnd_4663859] using wordTrace_append hprefix tailTrace_4663859
  have hstable : (prefixWord ++ tailWord_4663859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663859).length < 2 ^ (prefixWord ++ tailWord_4663859).sum := by decide
  have hdescent : baseEnd_4663859 < baseStart_4663859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663870 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_4663870 : Nat := 118140960795 + 4663870 * 2 ^ 59
def prefixEnd_4663870 : Nat := 4983230072969 + 3 ^ 40 * 4663870 * 2
def baseEnd_4663870 : Nat := 2394807020084772820876259

theorem tailTrace_4663870 : CollatzResearch.WordTrace tailWord_4663870 prefixEnd_4663870 2394807020084772820876259 := by
  unfold tailWord_4663870
  simp only [CollatzResearch.WordTrace]
  refine ⟨21263164201700373803308633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113403542409068660284312709 21263164201700373803308633)
  ·
    refine ⟨15947373151275280352481475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21263164201700373803308633 15947373151275280352481475)
    ·
      refine ⟨23921059726912920528722213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15947373151275280352481475 23921059726912920528722213)
      ·
        refine ⟨4485198698796172599135415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23921059726912920528722213 4485198698796172599135415)
        ·
          refine ⟨6727798048194258898703123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4485198698796172599135415 6727798048194258898703123)
          ·
            refine ⟨10091697072291388348054685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6727798048194258898703123 10091697072291388348054685)
            ·
              refine ⟨3784386402109270630520507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10091697072291388348054685 3784386402109270630520507)
              ·
                refine ⟨5676579603163905945780761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784386402109270630520507 5676579603163905945780761)
                ·
                  refine ⟨4257434702372929459335571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5676579603163905945780761 4257434702372929459335571)
                  ·
                    refine ⟨6386152053559394189003357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4257434702372929459335571 6386152053559394189003357)
                    ·
                      refine ⟨2394807020084772820876259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6386152053559394189003357 2394807020084772820876259)
                      ·
                        rfl

theorem cell23_4663870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_4663870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663870 prefixEnd_4663870 := by exact prefixLift 4663870
  have htrace : WordTrace (prefixWord ++ tailWord_4663870) baseStart_4663870 baseEnd_4663870 := by
    simpa [prefixWord, tailWord_4663870, baseEnd_4663870] using wordTrace_append hprefix tailTrace_4663870
  have hstable : (prefixWord ++ tailWord_4663870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663870).length < 2 ^ (prefixWord ++ tailWord_4663870).sum := by decide
  have hdescent : baseEnd_4663870 < baseStart_4663870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663895 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 1, 7]
def baseStart_4663895 : Nat := 118140960795 + 4663895 * 2 ^ 59
def prefixEnd_4663895 : Nat := 4983230072969 + 3 ^ 40 * 4663895 * 2
def baseEnd_4663895 : Nat := 798273285700378407687881

theorem tailTrace_4663895 : CollatzResearch.WordTrace tailWord_4663895 prefixEnd_4663895 798273285700378407687881 := by
  unfold tailWord_4663895
  simp only [CollatzResearch.WordTrace]
  refine ⟨170106225438512419696129139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113404150292341613130752759 170106225438512419696129139)
  ·
    refine ⟨255159338157768629544193709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170106225438512419696129139 255159338157768629544193709)
    ·
      refine ⟨95684751809163236079072641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255159338157768629544193709 95684751809163236079072641)
      ·
        refine ⟨71763563856872427059304481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95684751809163236079072641 71763563856872427059304481)
        ·
          refine ⟨53822672892654320294478361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71763563856872427059304481 53822672892654320294478361)
          ·
            refine ⟨40367004669490740220858771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53822672892654320294478361 40367004669490740220858771)
            ·
              refine ⟨60550507004236110331288157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40367004669490740220858771 60550507004236110331288157)
              ·
                refine ⟨22706440126588541374233059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60550507004236110331288157 22706440126588541374233059)
                ·
                  refine ⟨34059660189882812061349589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22706440126588541374233059 34059660189882812061349589)
                  ·
                    refine ⟨798273285700378407687881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34059660189882812061349589 798273285700378407687881)
                    ·
                      rfl

theorem cell23_4663895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_4663895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663895 prefixEnd_4663895 := by exact prefixLift 4663895
  have htrace : WordTrace (prefixWord ++ tailWord_4663895) baseStart_4663895 baseEnd_4663895 := by
    simpa [prefixWord, tailWord_4663895, baseEnd_4663895] using wordTrace_append hprefix tailTrace_4663895
  have hstable : (prefixWord ++ tailWord_4663895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663895).length < 2 ^ (prefixWord ++ tailWord_4663895).sum := by decide
  have hdescent : baseEnd_4663895 < baseStart_4663895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663915 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 4]
def baseStart_4663915 : Nat := 118140960795 + 4663915 * 2 ^ 59
def prefixEnd_4663915 : Nat := 4983230072969 + 3 ^ 40 * 4663915 * 2
def baseEnd_4663915 : Nat := 2394830126714225144813551

theorem tailTrace_4663915 : CollatzResearch.WordTrace tailWord_4663915 prefixEnd_4663915 2394830126714225144813551 := by
  unfold tailWord_4663915
  simp only [CollatzResearch.WordTrace]
  refine ⟨170106954898439963111857199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113404636598959975407904799 170106954898439963111857199)
  ·
    refine ⟨255160432347659944667785799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170106954898439963111857199 255160432347659944667785799)
    ·
      refine ⟨382740648521489917001678699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255160432347659944667785799 382740648521489917001678699)
      ·
        refine ⟨574110972782234875502518049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382740648521489917001678699 574110972782234875502518049)
        ·
          refine ⟨430583229586676156626888537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 574110972782234875502518049 430583229586676156626888537)
          ·
            refine ⟨322937422190007117470166403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430583229586676156626888537 322937422190007117470166403)
            ·
              refine ⟨484406133285010676205249605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322937422190007117470166403 484406133285010676205249605)
              ·
                refine ⟨90826149990939501788484301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 484406133285010676205249605 90826149990939501788484301)
                ·
                  refine ⟨34059806246602313170681613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90826149990939501788484301 34059806246602313170681613)
                  ·
                    refine ⟨12772427342475867439005605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34059806246602313170681613 12772427342475867439005605)
                    ·
                      refine ⟨2394830126714225144813551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12772427342475867439005605 2394830126714225144813551)
                      ·
                        rfl

theorem cell23_4663915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 4].length) (baseStart_4663915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663915 prefixEnd_4663915 := by exact prefixLift 4663915
  have htrace : WordTrace (prefixWord ++ tailWord_4663915) baseStart_4663915 baseEnd_4663915 := by
    simpa [prefixWord, tailWord_4663915, baseEnd_4663915] using wordTrace_append hprefix tailTrace_4663915
  have hstable : (prefixWord ++ tailWord_4663915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663915).length < 2 ^ (prefixWord ++ tailWord_4663915).sum := by decide
  have hdescent : baseEnd_4663915 < baseStart_4663915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663945 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_4663945 : Nat := 118140960795 + 4663945 * 2 ^ 59
def prefixEnd_4663945 : Nat := 4983230072969 + 3 ^ 40 * 4663945 * 2
def baseEnd_4663945 : Nat := 2394845531133860027438413

theorem tailTrace_4663945 : CollatzResearch.WordTrace tailWord_4663945 prefixEnd_4663945 2394845531133860027438413 := by
  unfold tailWord_4663945
  simp only [CollatzResearch.WordTrace]
  refine ⟨170108049088331278235449289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113405366058887518823632859 170108049088331278235449289)
  ·
    refine ⟨127581036816248458676586967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170108049088331278235449289 127581036816248458676586967)
    ·
      refine ⟨191371555224372688014880451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127581036816248458676586967 191371555224372688014880451)
      ·
        refine ⟨287057332836559032022320677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191371555224372688014880451 287057332836559032022320677)
        ·
          refine ⟨53823249906854818504185127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 287057332836559032022320677 53823249906854818504185127)
          ·
            refine ⟨80734874860282227756277691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53823249906854818504185127 80734874860282227756277691)
            ·
              refine ⟨121102312290423341634416537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80734874860282227756277691 121102312290423341634416537)
              ·
                refine ⟨90826734217817506225812403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121102312290423341634416537 90826734217817506225812403)
                ·
                  refine ⟨136240101326726259338718605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90826734217817506225812403 136240101326726259338718605)
                  ·
                    refine ⟨51090037997522347252019477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 136240101326726259338718605 51090037997522347252019477)
                    ·
                      refine ⟨2394845531133860027438413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51090037997522347252019477 2394845531133860027438413)
                      ·
                        rfl

theorem cell23_4663945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_4663945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663945 prefixEnd_4663945 := by exact prefixLift 4663945
  have htrace : WordTrace (prefixWord ++ tailWord_4663945) baseStart_4663945 baseEnd_4663945 := by
    simpa [prefixWord, tailWord_4663945, baseEnd_4663945] using wordTrace_append hprefix tailTrace_4663945
  have hstable : (prefixWord ++ tailWord_4663945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663945).length < 2 ^ (prefixWord ++ tailWord_4663945).sum := by decide
  have hdescent : baseEnd_4663945 < baseStart_4663945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663966 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_4663966 : Nat := 118140960795 + 4663966 * 2 ^ 59
def prefixEnd_4663966 : Nat := 4983230072969 + 3 ^ 40 * 4663966 * 2
def baseEnd_4663966 : Nat := 2394856314227604445275817

theorem tailTrace_4663966 : CollatzResearch.WordTrace tailWord_4663966 prefixEnd_4663966 2394856314227604445275817 := by
  unfold tailWord_4663966
  simp only [CollatzResearch.WordTrace]
  refine ⟨21263601877656899852745469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113405876680836799214642501 21263601877656899852745469)
  ·
    refine ⟨7973850704121337444779551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21263601877656899852745469 7973850704121337444779551)
    ·
      refine ⟨11960776056182006167169327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7973850704121337444779551 11960776056182006167169327)
      ·
        refine ⟨17941164084273009250753991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11960776056182006167169327 17941164084273009250753991)
        ·
          refine ⟨26911746126409513876130987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17941164084273009250753991 26911746126409513876130987)
          ·
            refine ⟨40367619189614270814196481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26911746126409513876130987 40367619189614270814196481)
            ·
              refine ⟨30275714392210703110647361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40367619189614270814196481 30275714392210703110647361)
              ·
                refine ⟨22706785794158027332985521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30275714392210703110647361 22706785794158027332985521)
                ·
                  refine ⟨17030089345618520499739141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22706785794158027332985521 17030089345618520499739141)
                  ·
                    refine ⟨3193141752303472593701089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17030089345618520499739141 3193141752303472593701089)
                    ·
                      refine ⟨2394856314227604445275817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193141752303472593701089 2394856314227604445275817)
                      ·
                        rfl

theorem cell23_4663966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_4663966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663966 prefixEnd_4663966 := by exact prefixLift 4663966
  have htrace : WordTrace (prefixWord ++ tailWord_4663966) baseStart_4663966 baseEnd_4663966 := by
    simpa [prefixWord, tailWord_4663966, baseEnd_4663966] using wordTrace_append hprefix tailTrace_4663966
  have hstable : (prefixWord ++ tailWord_4663966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663966).length < 2 ^ (prefixWord ++ tailWord_4663966).sum := by decide
  have hdescent : baseEnd_4663966 < baseStart_4663966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663989 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 6]
def baseStart_4663989 : Nat := 118140960795 + 4663989 * 2 ^ 59
def prefixEnd_4663989 : Nat := 4983230072969 + 3 ^ 40 * 4663989 * 2
def baseEnd_4663989 : Nat := 266096458253628650587579

theorem tailTrace_4663989 : CollatzResearch.WordTrace tailWord_4663989 prefixEnd_4663989 266096458253628650587579 := by
  unfold tailWord_4663989
  simp only [CollatzResearch.WordTrace]
  refine ⟨170109653900171873750051021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113406435933447915833367347 170109653900171873750051021)
  ·
    refine ⟨63791120212564452656269133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170109653900171873750051021 63791120212564452656269133)
    ·
      refine ⟨23921670079711669746100925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63791120212564452656269133 23921670079711669746100925)
      ·
        refine ⟨8970626279891876154787847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23921670079711669746100925 8970626279891876154787847)
        ·
          refine ⟨13455939419837814232181771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8970626279891876154787847 13455939419837814232181771)
          ·
            refine ⟨20183909129756721348272657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13455939419837814232181771 20183909129756721348272657)
            ·
              refine ⟨15137931847317541011204493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20183909129756721348272657 15137931847317541011204493)
              ·
                refine ⟨5676724442744077879201685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15137931847317541011204493 5676724442744077879201685)
                ·
                  refine ⟨266096458253628650587579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5676724442744077879201685 266096458253628650587579)
                  ·
                    rfl

theorem cell23_4663989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_4663989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663989 prefixEnd_4663989 := by exact prefixLift 4663989
  have htrace : WordTrace (prefixWord ++ tailWord_4663989) baseStart_4663989 baseEnd_4663989 := by
    simpa [prefixWord, tailWord_4663989, baseEnd_4663989] using wordTrace_append hprefix tailTrace_4663989
  have hstable : (prefixWord ++ tailWord_4663989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663989).length < 2 ^ (prefixWord ++ tailWord_4663989).sum := by decide
  have hdescent : baseEnd_4663989 < baseStart_4663989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4663999 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 5, 1, 3]
def baseStart_4663999 : Nat := 118140960795 + 4663999 * 2 ^ 59
def prefixEnd_4663999 : Nat := 4983230072969 + 3 ^ 40 * 4663999 * 2
def baseEnd_4663999 : Nat := 2394873259089202816163165

theorem tailTrace_4663999 : CollatzResearch.WordTrace tailWord_4663999 prefixEnd_4663999 2394873259089202816163165 := by
  unfold tailWord_4663999
  simp only [CollatzResearch.WordTrace]
  refine ⟨170110018630135645457915051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113406679086757096971943367 170110018630135645457915051)
  ·
    refine ⟨255165027945203468186872577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170110018630135645457915051 255165027945203468186872577)
    ·
      refine ⟨191373770958902601140154433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255165027945203468186872577 191373770958902601140154433)
      ·
        refine ⟨143530328219176950855115825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191373770958902601140154433 143530328219176950855115825)
        ·
          refine ⟨107647746164382713141336869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143530328219176950855115825 107647746164382713141336869)
          ·
            refine ⟨20183952405821758714000663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107647746164382713141336869 20183952405821758714000663)
            ·
              refine ⟨30275928608732638071000995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20183952405821758714000663 30275928608732638071000995)
              ·
                refine ⟨45413892913098957106501493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30275928608732638071000995 45413892913098957106501493)
                ·
                  refine ⟨4257552460603027228734515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45413892913098957106501493 4257552460603027228734515)
                  ·
                    refine ⟨6386328690904540843101773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4257552460603027228734515 6386328690904540843101773)
                    ·
                      refine ⟨2394873259089202816163165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6386328690904540843101773 2394873259089202816163165)
                      ·
                        rfl

theorem cell23_4663999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_4663999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4663999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4663999 prefixEnd_4663999 := by exact prefixLift 4663999
  have htrace : WordTrace (prefixWord ++ tailWord_4663999) baseStart_4663999 baseEnd_4663999 := by
    simpa [prefixWord, tailWord_4663999, baseEnd_4663999] using wordTrace_append hprefix tailTrace_4663999
  have hstable : (prefixWord ++ tailWord_4663999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4663999).length < 2 ^ (prefixWord ++ tailWord_4663999).sum := by decide
  have hdescent : baseEnd_4663999 < baseStart_4663999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4663999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664033 : List Nat := [1, 2, 3, 1, 4, 1, 2, 4, 1, 1, 3]
def baseStart_4664033 : Nat := 118140960795 + 4664033 * 2 ^ 59
def prefixEnd_4664033 : Nat := 4983230072969 + 3 ^ 40 * 4664033 * 2
def baseEnd_4664033 : Nat := 2394890717431455683138009

theorem tailTrace_4664033 : CollatzResearch.WordTrace tailWord_4664033 prefixEnd_4664033 2394890717431455683138009 := by
  unfold tailWord_4664033
  simp only [CollatzResearch.WordTrace]
  refine ⟨170111258712012469264652753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113407505808008312843101835 170111258712012469264652753)
  ·
    refine ⟨127583444034009351948489565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170111258712012469264652753 127583444034009351948489565)
    ·
      refine ⟨47843791512753506980683587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127583444034009351948489565 47843791512753506980683587)
      ·
        refine ⟨71765687269130260471025381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47843791512753506980683587 71765687269130260471025381)
        ·
          refine ⟨13456066362961923838317259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71765687269130260471025381 13456066362961923838317259)
          ·
            refine ⟨20184099544442885757475889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13456066362961923838317259 20184099544442885757475889)
            ·
              refine ⟨15138074658332164318106917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20184099544442885757475889 15138074658332164318106917)
              ·
                refine ⟨2838388998437280809645047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15138074658332164318106917 2838388998437280809645047)
                ·
                  refine ⟨4257583497655921214467571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2838388998437280809645047 4257583497655921214467571)
                  ·
                    refine ⟨6386375246483881821701357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4257583497655921214467571 6386375246483881821701357)
                    ·
                      refine ⟨2394890717431455683138009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6386375246483881821701357 2394890717431455683138009)
                      ·
                        rfl

theorem cell23_4664033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_4664033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664033 prefixEnd_4664033 := by exact prefixLift 4664033
  have htrace : WordTrace (prefixWord ++ tailWord_4664033) baseStart_4664033 baseEnd_4664033 := by
    simpa [prefixWord, tailWord_4664033, baseEnd_4664033] using wordTrace_append hprefix tailTrace_4664033
  have hstable : (prefixWord ++ tailWord_4664033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664033).length < 2 ^ (prefixWord ++ tailWord_4664033).sum := by decide
  have hdescent : baseEnd_4664033 < baseStart_4664033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664056 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 3, 2, 2]
def baseStart_4664056 : Nat := 118140960795 + 4664056 * 2 ^ 59
def prefixEnd_4664056 : Nat := 4983230072969 + 3 ^ 40 * 4664056 * 2
def baseEnd_4664056 : Nat := 2394902527486509093150403

theorem tailTrace_4664056 : CollatzResearch.WordTrace tailWord_4664056 prefixEnd_4664056 2394902527486509093150403 := by
  unfold tailWord_4664056
  simp only [CollatzResearch.WordTrace]
  refine ⟨85056048795464572096370011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113408065060619429461826681 85056048795464572096370011)
  ·
    refine ⟨127584073193196858144555017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85056048795464572096370011 127584073193196858144555017)
    ·
      refine ⟨95688054894897643608416263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127584073193196858144555017 95688054894897643608416263)
      ·
        refine ⟨143532082342346465412624395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95688054894897643608416263 143532082342346465412624395)
        ·
          refine ⟨215298123513519698118936593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143532082342346465412624395 215298123513519698118936593)
          ·
            refine ⟨161473592635139773589202445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215298123513519698118936593 161473592635139773589202445)
            ·
              refine ⟨60552597238177415095950917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161473592635139773589202445 60552597238177415095950917)
              ·
                refine ⟨11353611982158265330490797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60552597238177415095950917 11353611982158265330490797)
                ·
                  refine ⟨4257604493309349498934049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11353611982158265330490797 4257604493309349498934049)
                  ·
                    refine ⟨3193203369982012124200537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257604493309349498934049 3193203369982012124200537)
                    ·
                      refine ⟨2394902527486509093150403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193203369982012124200537 2394902527486509093150403)
                      ·
                        rfl

theorem cell23_4664056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3, 2, 2].length) (baseStart_4664056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664056 prefixEnd_4664056 := by exact prefixLift 4664056
  have htrace : WordTrace (prefixWord ++ tailWord_4664056) baseStart_4664056 baseEnd_4664056 := by
    simpa [prefixWord, tailWord_4664056, baseEnd_4664056] using wordTrace_append hprefix tailTrace_4664056
  have hstable : (prefixWord ++ tailWord_4664056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664056).length < 2 ^ (prefixWord ++ tailWord_4664056).sum := by decide
  have hdescent : baseEnd_4664056 < baseStart_4664056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664066 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_4664066 : Nat := 118140960795 + 4664066 * 2 ^ 59
def prefixEnd_4664066 : Nat := 4983230072969 + 3 ^ 40 * 4664066 * 2
def baseEnd_4664066 : Nat := 798302554097684684675119

theorem tailTrace_4664066 : CollatzResearch.WordTrace tailWord_4664066 prefixEnd_4664066 798302554097684684675119 := by
  unfold tailWord_4664066
  simp only [CollatzResearch.WordTrace]
  refine ⟨42528115580223228975151013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113408308213928610600402701 42528115580223228975151013)
  ·
    refine ⟨7974021671291855432840815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42528115580223228975151013 7974021671291855432840815)
    ·
      refine ⟨11961032506937783149261223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7974021671291855432840815 11961032506937783149261223)
      ·
        refine ⟨17941548760406674723891835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11961032506937783149261223 17941548760406674723891835)
        ·
          refine ⟨26912323140610012085837753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17941548760406674723891835 26912323140610012085837753)
          ·
            refine ⟨20184242355457509064378315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26912323140610012085837753 20184242355457509064378315)
            ·
              refine ⟨30276363533186263596567473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20184242355457509064378315 30276363533186263596567473)
              ·
                refine ⟨22707272649889697697425605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30276363533186263596567473 22707272649889697697425605)
                ·
                  refine ⟨4257613621854318318267301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22707272649889697697425605 4257613621854318318267301)
                  ·
                    refine ⟨798302554097684684675119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4257613621854318318267301 798302554097684684675119)
                    ·
                      rfl

theorem cell23_4664066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_4664066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664066 prefixEnd_4664066 := by exact prefixLift 4664066
  have htrace : WordTrace (prefixWord ++ tailWord_4664066) baseStart_4664066 baseEnd_4664066 := by
    simpa [prefixWord, tailWord_4664066, baseEnd_4664066] using wordTrace_append hprefix tailTrace_4664066
  have hstable : (prefixWord ++ tailWord_4664066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664066).length < 2 ^ (prefixWord ++ tailWord_4664066).sum := by decide
  have hdescent : baseEnd_4664066 < baseStart_4664066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664099 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 2, 7, 2]
def baseStart_4664099 : Nat := 118140960795 + 4664099 * 2 ^ 59
def prefixEnd_4664099 : Nat := 4983230072969 + 3 ^ 40 * 4664099 * 2
def baseEnd_4664099 : Nat := 2394924607154652424912705

theorem tailTrace_4664099 : CollatzResearch.WordTrace tailWord_4664099 prefixEnd_4664099 2394924607154652424912705 := by
  unfold tailWord_4664099
  simp only [CollatzResearch.WordTrace]
  refine ⟨170113665929773362536555351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113409110619848908357703567 170113665929773362536555351)
  ·
    refine ⟨255170498894660043804833027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170113665929773362536555351 255170498894660043804833027)
    ·
      refine ⟨382755748341990065707249541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255170498894660043804833027 382755748341990065707249541)
      ·
        refine ⟨71766702814123137320109289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 382755748341990065707249541 71766702814123137320109289)
        ·
          refine ⟨53825027110592352990081967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71766702814123137320109289 53825027110592352990081967)
          ·
            refine ⟨80737540665888529485122951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53825027110592352990081967 80737540665888529485122951)
            ·
              refine ⟨121106310998832794227684427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80737540665888529485122951 121106310998832794227684427)
              ·
                refine ⟨181659466498249191341526641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121106310998832794227684427 181659466498249191341526641)
                ·
                  refine ⟨136244599873686893506144981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181659466498249191341526641 136244599873686893506144981)
                  ·
                    refine ⟨3193232809539536566550273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 136244599873686893506144981 3193232809539536566550273)
                    ·
                      refine ⟨2394924607154652424912705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193232809539536566550273 2394924607154652424912705)
                      ·
                        rfl

theorem cell23_4664099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_4664099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664099 prefixEnd_4664099 := by exact prefixLift 4664099
  have htrace : WordTrace (prefixWord ++ tailWord_4664099) baseStart_4664099 baseEnd_4664099 := by
    simpa [prefixWord, tailWord_4664099, baseEnd_4664099] using wordTrace_append hprefix tailTrace_4664099
  have hstable : (prefixWord ++ tailWord_4664099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664099).length < 2 ^ (prefixWord ++ tailWord_4664099).sum := by decide
  have hdescent : baseEnd_4664099 < baseStart_4664099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664100 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_4664100 : Nat := 118140960795 + 4664100 * 2 ^ 59
def prefixEnd_4664100 : Nat := 4983230072969 + 3 ^ 40 * 4664100 * 2
def baseEnd_4664100 : Nat := 798308373545102307000067

theorem tailTrace_4664100 : CollatzResearch.WordTrace tailWord_4664100 prefixEnd_4664100 798308373545102307000067 := by
  unfold tailWord_4664100
  simp only [CollatzResearch.WordTrace]
  refine ⟨85056851201384869853670877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113409134935179826471561169 85056851201384869853670877)
  ·
    refine ⟨31896319200519326195126579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85056851201384869853670877 31896319200519326195126579)
    ·
      refine ⟨47844478800778989292689869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31896319200519326195126579 47844478800778989292689869)
      ·
        refine ⟨17941679550292120984758701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47844478800778989292689869 17941679550292120984758701)
        ·
          refine ⟨6728129831359545369284513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17941679550292120984758701 6728129831359545369284513)
          ·
            refine ⟨5046097373519659026963385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6728129831359545369284513 5046097373519659026963385)
            ·
              refine ⟨3784573030139744270222539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5046097373519659026963385 3784573030139744270222539)
              ·
                refine ⟨5676859545209616405333809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784573030139744270222539 5676859545209616405333809)
                ·
                  refine ⟨4257644658907212304000357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5676859545209616405333809 4257644658907212304000357)
                  ·
                    refine ⟨798308373545102307000067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4257644658907212304000357 798308373545102307000067)
                    ·
                      rfl

theorem cell23_4664100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_4664100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664100 prefixEnd_4664100 := by exact prefixLift 4664100
  have htrace : WordTrace (prefixWord ++ tailWord_4664100) baseStart_4664100 baseEnd_4664100 := by
    simpa [prefixWord, tailWord_4664100, baseEnd_4664100] using wordTrace_append hprefix tailTrace_4664100
  have hstable : (prefixWord ++ tailWord_4664100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664100).length < 2 ^ (prefixWord ++ tailWord_4664100).sum := by decide
  have hdescent : baseEnd_4664100 < baseStart_4664100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664110 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4664110 : Nat := 118140960795 + 4664110 * 2 ^ 59
def prefixEnd_4664110 : Nat := 4983230072969 + 3 ^ 40 * 4664110 * 2
def baseEnd_4664110 : Nat := 2394930255441851881875155

theorem tailTrace_4664110 : CollatzResearch.WordTrace tailWord_4664110 prefixEnd_4664110 2394930255441851881875155 := by
  unfold tailWord_4664110
  simp only [CollatzResearch.WordTrace]
  refine ⟨21264258391591688926900723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113409378088489007610137189 21264258391591688926900723)
  ·
    refine ⟨31896387587387533390351085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21264258391591688926900723 31896387587387533390351085)
    ·
      refine ⟨11961145345270325021381657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31896387587387533390351085 11961145345270325021381657)
      ·
        refine ⟨8970859008952743766036243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11961145345270325021381657 8970859008952743766036243)
        ·
          refine ⟨13456288513429115649054365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8970859008952743766036243 13456288513429115649054365)
          ·
            refine ⟨5046108192535918368395387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13456288513429115649054365 5046108192535918368395387)
            ·
              refine ⟨7569162288803877552593081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5046108192535918368395387 7569162288803877552593081)
              ·
                refine ⟨5676871716602908164444811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7569162288803877552593081 5676871716602908164444811)
                ·
                  refine ⟨8515307574904362246667217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5676871716602908164444811 8515307574904362246667217)
                  ·
                    refine ⟨6386480681178271685000413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8515307574904362246667217 6386480681178271685000413)
                    ·
                      refine ⟨2394930255441851881875155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6386480681178271685000413 2394930255441851881875155)
                      ·
                        rfl

theorem cell23_4664110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4664110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664110 prefixEnd_4664110 := by exact prefixLift 4664110
  have htrace : WordTrace (prefixWord ++ tailWord_4664110) baseStart_4664110 baseEnd_4664110 := by
    simpa [prefixWord, tailWord_4664110, baseEnd_4664110] using wordTrace_append hprefix tailTrace_4664110
  have hstable : (prefixWord ++ tailWord_4664110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664110).length < 2 ^ (prefixWord ++ tailWord_4664110).sum := by decide
  have hdescent : baseEnd_4664110 < baseStart_4664110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664141 : List Nat := [1, 6, 1, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_4664141 : Nat := 118140960795 + 4664141 * 2 ^ 59
def prefixEnd_4664141 : Nat := 4983230072969 + 3 ^ 40 * 4664141 * 2
def baseEnd_4664141 : Nat := 2394946173342141260587513

theorem tailTrace_4664141 : CollatzResearch.WordTrace tailWord_4664141 prefixEnd_4664141 2394946173342141260587513 := by
  unfold tailWord_4664141
  simp only [CollatzResearch.WordTrace]
  refine ⟨170115197795621203709584277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113410131863747469139722851 170115197795621203709584277)
  ·
    refine ⟨7974149896669743923886763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 170115197795621203709584277 7974149896669743923886763)
    ·
      refine ⟨11961224845004615885830145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7974149896669743923886763 11961224845004615885830145)
      ·
        refine ⟨8970918633753461914372609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11961224845004615885830145 8970918633753461914372609)
        ·
          refine ⟨6728188975315096435779457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8970918633753461914372609 6728188975315096435779457)
          ·
            refine ⟨5046141731486322326834593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6728188975315096435779457 5046141731486322326834593)
            ·
              refine ⟨3784606298614741745125945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5046141731486322326834593 3784606298614741745125945)
              ·
                refine ⟨2838454723961056308844459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3784606298614741745125945 2838454723961056308844459)
                ·
                  refine ⟨4257682085941584463266689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2838454723961056308844459 4257682085941584463266689)
                  ·
                    refine ⟨3193261564456188347450017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257682085941584463266689 3193261564456188347450017)
                    ·
                      refine ⟨2394946173342141260587513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193261564456188347450017 2394946173342141260587513)
                      ·
                        rfl

theorem cell23_4664141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_4664141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664141 prefixEnd_4664141 := by exact prefixLift 4664141
  have htrace : WordTrace (prefixWord ++ tailWord_4664141) baseStart_4664141 baseEnd_4664141 := by
    simpa [prefixWord, tailWord_4664141, baseEnd_4664141] using wordTrace_append hprefix tailTrace_4664141
  have hstable : (prefixWord ++ tailWord_4664141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664141).length < 2 ^ (prefixWord ++ tailWord_4664141).sum := by decide
  have hdescent : baseEnd_4664141 < baseStart_4664141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664146 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_4664146 : Nat := 118140960795 + 4664146 * 2 ^ 59
def prefixEnd_4664146 : Nat := 4983230072969 + 3 ^ 40 * 4664146 * 2
def baseEnd_4664146 : Nat := 2394948740745413741024989

theorem tailTrace_4664146 : CollatzResearch.WordTrace tailWord_4664146 prefixEnd_4664146 2394948740745413741024989 := by
  unfold tailWord_4664146
  simp only [CollatzResearch.WordTrace]
  refine ⟨42528845040150772390879073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113410253440402059709010861 42528845040150772390879073)
  ·
    refine ⟨31896633780113079293159305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42528845040150772390879073 31896633780113079293159305)
    ·
      refine ⟨23922475335084809469869479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31896633780113079293159305 23922475335084809469869479)
      ·
        refine ⟨35883713002627214204804219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23922475335084809469869479 35883713002627214204804219)
        ·
          refine ⟨53825569503940821307206329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35883713002627214204804219 53825569503940821307206329)
          ·
            refine ⟨40369177127955615980404747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53825569503940821307206329 40369177127955615980404747)
            ·
              refine ⟨60553765691933423970607121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40369177127955615980404747 60553765691933423970607121)
              ·
                refine ⟨45415324268950067977955341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60553765691933423970607121 45415324268950067977955341)
                ·
                  refine ⟨17030746600856275491733253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45415324268950067977955341 17030746600856275491733253)
                  ·
                    refine ⟨3193264987660551654699985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17030746600856275491733253 3193264987660551654699985)
                    ·
                      refine ⟨2394948740745413741024989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193264987660551654699985 2394948740745413741024989)
                      ·
                        rfl

theorem cell23_4664146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_4664146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664146 prefixEnd_4664146 := by exact prefixLift 4664146
  have htrace : WordTrace (prefixWord ++ tailWord_4664146) baseStart_4664146 baseEnd_4664146 := by
    simpa [prefixWord, tailWord_4664146, baseEnd_4664146] using wordTrace_append hprefix tailTrace_4664146
  have hstable : (prefixWord ++ tailWord_4664146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664146).length < 2 ^ (prefixWord ++ tailWord_4664146).sum := by decide
  have hdescent : baseEnd_4664146 < baseStart_4664146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664149 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_4664149 : Nat := 118140960795 + 4664149 * 2 ^ 59
def prefixEnd_4664149 : Nat := 4983230072969 + 3 ^ 40 * 4664149 * 2
def baseEnd_4664149 : Nat := 2394950281187377229287475

theorem tailTrace_4664149 : CollatzResearch.WordTrace tailWord_4664149 prefixEnd_4664149 2394950281187377229287475 := by
  unfold tailWord_4664149
  simp only [CollatzResearch.WordTrace]
  refine ⟨170115489579592221075875501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113410326386394814050583667 170115489579592221075875501)
  ·
    refine ⟨63793308592347082903453313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170115489579592221075875501 63793308592347082903453313)
    ·
      refine ⟨47844981444260312177589985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63793308592347082903453313 47844981444260312177589985)
      ·
        refine ⟨35883736083195234133192489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47844981444260312177589985 35883736083195234133192489)
        ·
          refine ⟨26912802062396425599894367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35883736083195234133192489 26912802062396425599894367)
          ·
            refine ⟨40369203093594638399841551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26912802062396425599894367 40369203093594638399841551)
            ·
              refine ⟨60553804640391957599762327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40369203093594638399841551 60553804640391957599762327)
              ·
                refine ⟨90830706960587936399643491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60553804640391957599762327 90830706960587936399643491)
                ·
                  refine ⟨136246060440881904599465237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90830706960587936399643491 136246060440881904599465237)
                  ·
                    refine ⟨6386534083166339278099933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 136246060440881904599465237 6386534083166339278099933)
                    ·
                      refine ⟨2394950281187377229287475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6386534083166339278099933 2394950281187377229287475)
                      ·
                        rfl

theorem cell23_4664149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_4664149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664149 prefixEnd_4664149 := by exact prefixLift 4664149
  have htrace : WordTrace (prefixWord ++ tailWord_4664149) baseStart_4664149 baseEnd_4664149 := by
    simpa [prefixWord, tailWord_4664149, baseEnd_4664149] using wordTrace_append hprefix tailTrace_4664149
  have hstable : (prefixWord ++ tailWord_4664149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664149).length < 2 ^ (prefixWord ++ tailWord_4664149).sum := by decide
  have hdescent : baseEnd_4664149 < baseStart_4664149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664152 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 11]
def baseStart_4664152 : Nat := 118140960795 + 4664152 * 2 ^ 59
def prefixEnd_4664152 : Nat := 4983230072969 + 3 ^ 40 * 4664152 * 2
def baseEnd_4664152 : Nat := 266105757958815635283329

theorem tailTrace_4664152 : CollatzResearch.WordTrace tailWord_4664152 prefixEnd_4664152 266105757958815635283329 := by
  unfold tailWord_4664152
  simp only [CollatzResearch.WordTrace]
  refine ⟨85057799499290676294117355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113410399332387568392156473 85057799499290676294117355)
  ·
    refine ⟨127586699248936014441176033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85057799499290676294117355 127586699248936014441176033)
    ·
      refine ⟨95690024436702010830882025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127586699248936014441176033 95690024436702010830882025)
      ·
        refine ⟨71767518327526508123161519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95690024436702010830882025 71767518327526508123161519)
        ·
          refine ⟨107651277491289762184742279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71767518327526508123161519 107651277491289762184742279)
          ·
            refine ⟨161476916236934643277113419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107651277491289762184742279 161476916236934643277113419)
            ·
              refine ⟨242215374355401964915670129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161476916236934643277113419 242215374355401964915670129)
              ·
                refine ⟨181661530766551473686752597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242215374355401964915670129 181661530766551473686752597)
                ·
                  refine ⟨266105757958815635283329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 181661530766551473686752597 266105757958815635283329)
                  ·
                    rfl

theorem cell23_4664152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 11].length) (baseStart_4664152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664152 prefixEnd_4664152 := by exact prefixLift 4664152
  have htrace : WordTrace (prefixWord ++ tailWord_4664152) baseStart_4664152 baseEnd_4664152 := by
    simpa [prefixWord, tailWord_4664152, baseEnd_4664152] using wordTrace_append hprefix tailTrace_4664152
  have hstable : (prefixWord ++ tailWord_4664152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664152).length < 2 ^ (prefixWord ++ tailWord_4664152).sum := by decide
  have hdescent : baseEnd_4664152 < baseStart_4664152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664156 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_4664156 : Nat := 118140960795 + 4664156 * 2 ^ 59
def prefixEnd_4664156 : Nat := 4983230072969 + 3 ^ 40 * 4664156 * 2
def baseEnd_4664156 : Nat := 798317958517319567299981

theorem tailTrace_4664156 : CollatzResearch.WordTrace tailWord_4664156 prefixEnd_4664156 798317958517319567299981 := by
  unfold tailWord_4664156
  simp only [CollatzResearch.WordTrace]
  refine ⟨85057872445283430635690161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113410496593711240847586881 85057872445283430635690161)
  ·
    refine ⟨63793404333962572976767621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85057872445283430635690161 63793404333962572976767621)
    ·
      refine ⟨11961263312617982433143929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63793404333962572976767621 11961263312617982433143929)
      ·
        refine ⟨8970947484463486824857947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11961263312617982433143929 8970947484463486824857947)
        ·
          refine ⟨13456421226695230237286921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8970947484463486824857947 13456421226695230237286921)
          ·
            refine ⟨10092315920021422677965191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13456421226695230237286921 10092315920021422677965191)
            ·
              refine ⟨15138473880032134016947787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10092315920021422677965191 15138473880032134016947787)
              ·
                refine ⟨22707710820048201025421681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15138473880032134016947787 22707710820048201025421681)
                ·
                  refine ⟨17030783115036150769066261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22707710820048201025421681 17030783115036150769066261)
                  ·
                    refine ⟨798317958517319567299981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17030783115036150769066261 798317958517319567299981)
                    ·
                      rfl

theorem cell23_4664156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_4664156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664156 prefixEnd_4664156 := by exact prefixLift 4664156
  have htrace : WordTrace (prefixWord ++ tailWord_4664156) baseStart_4664156 baseEnd_4664156 := by
    simpa [prefixWord, tailWord_4664156, baseEnd_4664156] using wordTrace_append hprefix tailTrace_4664156
  have hstable : (prefixWord ++ tailWord_4664156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664156).length < 2 ^ (prefixWord ++ tailWord_4664156).sum := by decide
  have hdescent : baseEnd_4664156 < baseStart_4664156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664159 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 4]
def baseStart_4664159 : Nat := 118140960795 + 4664159 * 2 ^ 59
def prefixEnd_4664159 : Nat := 4983230072969 + 3 ^ 40 * 4664159 * 2
def baseEnd_4664159 : Nat := 2394955415993922190162429

theorem tailTrace_4664159 : CollatzResearch.WordTrace tailWord_4664159 prefixEnd_4664159 2394955415993922190162429 := by
  unfold tailWord_4664159
  simp only [CollatzResearch.WordTrace]
  refine ⟨170115854309555992783739531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113410569539703995189159687 170115854309555992783739531)
  ·
    refine ⟨255173781464333989175609297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170115854309555992783739531 255173781464333989175609297)
    ·
      refine ⟨191380336098250491881706973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255173781464333989175609297 191380336098250491881706973)
      ·
        refine ⟨71767626036843934455640115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191380336098250491881706973 71767626036843934455640115)
        ·
          refine ⟨107651439055265901683460173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71767626036843934455640115 107651439055265901683460173)
          ·
            refine ⟨40369289645724713131297565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107651439055265901683460173 40369289645724713131297565)
            ·
              refine ⟨15138483617146767424236587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40369289645724713131297565 15138483617146767424236587)
              ·
                refine ⟨22707725425720151136354881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15138483617146767424236587 22707725425720151136354881)
                ·
                  refine ⟨17030794069290113352266161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22707725425720151136354881 17030794069290113352266161)
                  ·
                    refine ⟨12773095551967585014199621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17030794069290113352266161 12773095551967585014199621)
                    ·
                      refine ⟨2394955415993922190162429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12773095551967585014199621 2394955415993922190162429)
                      ·
                        rfl

theorem cell23_4664159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_4664159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664159 prefixEnd_4664159 := by exact prefixLift 4664159
  have htrace : WordTrace (prefixWord ++ tailWord_4664159) baseStart_4664159 baseEnd_4664159 := by
    simpa [prefixWord, tailWord_4664159, baseEnd_4664159] using wordTrace_append hprefix tailTrace_4664159
  have hstable : (prefixWord ++ tailWord_4664159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664159).length < 2 ^ (prefixWord ++ tailWord_4664159).sum := by decide
  have hdescent : baseEnd_4664159 < baseStart_4664159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664163 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 1, 4, 2]
def baseStart_4664163 : Nat := 118140960795 + 4664163 * 2 ^ 59
def prefixEnd_4664163 : Nat := 4983230072969 + 3 ^ 40 * 4664163 * 2
def baseEnd_4664163 : Nat := 2394957469916540174512411

theorem tailTrace_4664163 : CollatzResearch.WordTrace tailWord_4664163 prefixEnd_4664163 2394957469916540174512411 := by
  unfold tailWord_4664163
  simp only [CollatzResearch.WordTrace]
  refine ⟨170116000201541501466885143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113410666801027667644590095 170116000201541501466885143)
  ·
    refine ⟨255174000302312252200327715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170116000201541501466885143 255174000302312252200327715)
    ·
      refine ⟨382761000453468378300491573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255174000302312252200327715 382761000453468378300491573)
      ·
        refine ⟨35883843792512660465671085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 382761000453468378300491573 35883843792512660465671085)
        ·
          refine ⟨13456441422192247674626657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35883843792512660465671085 13456441422192247674626657)
          ·
            refine ⟨10092331066644185755969993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13456441422192247674626657 10092331066644185755969993)
            ·
              refine ⟨7569248299983139316977495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10092331066644185755969993 7569248299983139316977495)
              ·
                refine ⟨11353872449974708975466243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7569248299983139316977495 11353872449974708975466243)
                ·
                  refine ⟨17030808674962063463199365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11353872449974708975466243 17030808674962063463199365)
                  ·
                    refine ⟨3193276626555386899349881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17030808674962063463199365 3193276626555386899349881)
                    ·
                      refine ⟨2394957469916540174512411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193276626555386899349881 2394957469916540174512411)
                      ·
                        rfl

theorem cell23_4664163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_4664163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664163 prefixEnd_4664163 := by exact prefixLift 4664163
  have htrace : WordTrace (prefixWord ++ tailWord_4664163) baseStart_4664163 baseEnd_4664163 := by
    simpa [prefixWord, tailWord_4664163, baseEnd_4664163] using wordTrace_append hprefix tailTrace_4664163
  have hstable : (prefixWord ++ tailWord_4664163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664163).length < 2 ^ (prefixWord ++ tailWord_4664163).sum := by decide
  have hdescent : baseEnd_4664163 < baseStart_4664163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664214 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4664214 : Nat := 118140960795 + 4664214 * 2 ^ 59
def prefixEnd_4664214 : Nat := 4983230072969 + 3 ^ 40 * 4664214 * 2
def baseEnd_4664214 : Nat := 2394983657429919474974677

theorem tailTrace_4664214 : CollatzResearch.WordTrace tailWord_4664214 prefixEnd_4664214 2394983657429919474974677 := by
  unfold tailWord_4664214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10632366270272296073561981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113411906882904491451327797 10632366270272296073561981)
  ·
    refine ⟨3987137351352111027585743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10632366270272296073561981 3987137351352111027585743)
    ·
      refine ⟨5980706027028166541378615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3987137351352111027585743 5980706027028166541378615)
      ·
        refine ⟨8971059040542249812067923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5980706027028166541378615 8971059040542249812067923)
        ·
          refine ⟨13456588560813374718101885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8971059040542249812067923 13456588560813374718101885)
          ·
            refine ⟨5046220710305015519288207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13456588560813374718101885 5046220710305015519288207)
            ·
              refine ⟨7569331065457523278932311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5046220710305015519288207 7569331065457523278932311)
              ·
                refine ⟨11353996598186284918398467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7569331065457523278932311 11353996598186284918398467)
                ·
                  refine ⟨17030994897279427377597701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11353996598186284918398467 17030994897279427377597701)
                  ·
                    refine ⟨3193311543239892633299569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17030994897279427377597701 3193311543239892633299569)
                    ·
                      refine ⟨2394983657429919474974677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193311543239892633299569 2394983657429919474974677)
                      ·
                        rfl

theorem cell23_4664214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4664214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664214 prefixEnd_4664214 := by exact prefixLift 4664214
  have htrace : WordTrace (prefixWord ++ tailWord_4664214) baseStart_4664214 baseEnd_4664214 := by
    simpa [prefixWord, tailWord_4664214, baseEnd_4664214] using wordTrace_append hprefix tailTrace_4664214
  have hstable : (prefixWord ++ tailWord_4664214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664214).length < 2 ^ (prefixWord ++ tailWord_4664214).sum := by decide
  have hdescent : baseEnd_4664214 < baseStart_4664214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664237 : List Nat := [1, 5, 2, 3, 1, 2, 1, 3, 5]
def baseStart_4664237 : Nat := 118140960795 + 4664237 * 2 ^ 59
def prefixEnd_4664237 : Nat := 4983230072969 + 3 ^ 40 * 4664237 * 2
def baseEnd_4664237 : Nat := 266110607498330320554119

theorem tailTrace_4664237 : CollatzResearch.WordTrace tailWord_4664237 prefixEnd_4664237 266110607498330320554119 := by
  unfold tailWord_4664237
  simp only [CollatzResearch.WordTrace]
  refine ⟨170118699203273412105078965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113412466135515608070052643 170118699203273412105078965)
  ·
    refine ⟨15948628050306882384851153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170118699203273412105078965 15948628050306882384851153)
    ·
      refine ⟨11961471037730161788638365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15948628050306882384851153 11961471037730161788638365)
      ·
        refine ⟨4485551639148810670739387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11961471037730161788638365 4485551639148810670739387)
        ·
          refine ⟨6728327458723216006109081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4485551639148810670739387 6728327458723216006109081)
          ·
            refine ⟨5046245594042412004581811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6728327458723216006109081 5046245594042412004581811)
            ·
              refine ⟨7569368391063618006872717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5046245594042412004581811 7569368391063618006872717)
              ·
                refine ⟨2838513146648856752577269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7569368391063618006872717 2838513146648856752577269)
                ·
                  refine ⟨266110607498330320554119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2838513146648856752577269 266110607498330320554119)
                  ·
                    rfl

theorem cell23_4664237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_4664237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664237 prefixEnd_4664237 := by exact prefixLift 4664237
  have htrace : WordTrace (prefixWord ++ tailWord_4664237) baseStart_4664237 baseEnd_4664237 := by
    simpa [prefixWord, tailWord_4664237, baseEnd_4664237] using wordTrace_append hprefix tailTrace_4664237
  have hstable : (prefixWord ++ tailWord_4664237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664237).length < 2 ^ (prefixWord ++ tailWord_4664237).sum := by decide
  have hdescent : baseEnd_4664237 < baseStart_4664237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664253 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_4664253 : Nat := 118140960795 + 4664253 * 2 ^ 59
def prefixEnd_4664253 : Nat := 4983230072969 + 3 ^ 40 * 4664253 * 2
def baseEnd_4664253 : Nat := 2395003683175444822386997

theorem tailTrace_4664253 : CollatzResearch.WordTrace tailWord_4664253 prefixEnd_4664253 2395003683175444822386997 := by
  unfold tailWord_4664253
  simp only [CollatzResearch.WordTrace]
  refine ⟨170119282771215446837661413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113412855180810297891774275 170119282771215446837661413)
  ·
    refine ⟨31897365519602896282061515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170119282771215446837661413 31897365519602896282061515)
    ·
      refine ⟨47846048279404344423092273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31897365519602896282061515 47846048279404344423092273)
      ·
        refine ⟨35884536209553258317319205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47846048279404344423092273 35884536209553258317319205)
        ·
          refine ⟨6728350539291235934497351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35884536209553258317319205 6728350539291235934497351)
          ·
            refine ⟨10092525808936853901746027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6728350539291235934497351 10092525808936853901746027)
            ·
              refine ⟨15138788713405280852619041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10092525808936853901746027 15138788713405280852619041)
              ·
                refine ⟨11354091535053960639464281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15138788713405280852619041 11354091535053960639464281)
                ·
                  refine ⟨8515568651290470479598211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11354091535053960639464281 8515568651290470479598211)
                  ·
                    refine ⟨12773352976935705719397317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8515568651290470479598211 12773352976935705719397317)
                    ·
                      refine ⟨2395003683175444822386997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12773352976935705719397317 2395003683175444822386997)
                      ·
                        rfl

theorem cell23_4664253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_4664253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664253 prefixEnd_4664253 := by exact prefixLift 4664253
  have htrace : WordTrace (prefixWord ++ tailWord_4664253) baseStart_4664253 baseEnd_4664253 := by
    simpa [prefixWord, tailWord_4664253, baseEnd_4664253] using wordTrace_append hprefix tailTrace_4664253
  have hstable : (prefixWord ++ tailWord_4664253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664253).length < 2 ^ (prefixWord ++ tailWord_4664253).sum := by decide
  have hdescent : baseEnd_4664253 < baseStart_4664253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664256 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 3]
def baseStart_4664256 : Nat := 118140960795 + 4664256 * 2 ^ 59
def prefixEnd_4664256 : Nat := 4983230072969 + 3 ^ 40 * 4664256 * 2
def baseEnd_4664256 : Nat := 2395005223617408310649483

theorem tailTrace_4664256 : CollatzResearch.WordTrace tailWord_4664256 prefixEnd_4664256 2395005223617408310649483 := by
  unfold tailWord_4664256
  simp only [CollatzResearch.WordTrace]
  refine ⟨85059696095102289175010311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113412928126803052233347081 85059696095102289175010311)
  ·
    refine ⟨127589544142653433762515467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85059696095102289175010311 127589544142653433762515467)
    ·
      refine ⟨191384316213980150643773201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127589544142653433762515467 191384316213980150643773201)
      ·
        refine ⟨143538237160485112982829901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191384316213980150643773201 143538237160485112982829901)
        ·
          refine ⟨53826838935181917368561213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143538237160485112982829901 53826838935181917368561213)
          ·
            refine ⟨20185064600693219013210455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53826838935181917368561213 20185064600693219013210455)
            ·
              refine ⟨30277596901039828519815683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20185064600693219013210455 30277596901039828519815683)
              ·
                refine ⟨45416395351559742779723525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30277596901039828519815683 45416395351559742779723525)
                ·
                  refine ⟨8515574128417451771198161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45416395351559742779723525 8515574128417451771198161)
                  ·
                    refine ⟨6386680596313088828398621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8515574128417451771198161 6386680596313088828398621)
                    ·
                      refine ⟨2395005223617408310649483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6386680596313088828398621 2395005223617408310649483)
                      ·
                        rfl

theorem cell23_4664256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_4664256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664256 prefixEnd_4664256 := by exact prefixLift 4664256
  have htrace : WordTrace (prefixWord ++ tailWord_4664256) baseStart_4664256 baseEnd_4664256 := by
    simpa [prefixWord, tailWord_4664256, baseEnd_4664256] using wordTrace_append hprefix tailTrace_4664256
  have hstable : (prefixWord ++ tailWord_4664256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664256).length < 2 ^ (prefixWord ++ tailWord_4664256).sum := by decide
  have hdescent : baseEnd_4664256 < baseStart_4664256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664263 : List Nat := [1, 1, 4, 1, 1, 2, 2, 6, 1, 4]
def baseStart_4664263 : Nat := 118140960795 + 4664263 * 2 ^ 59
def prefixEnd_4664263 : Nat := 4983230072969 + 3 ^ 40 * 4664263 * 2
def baseEnd_4664263 : Nat := 798336272660663261087317

theorem tailTrace_4664263 : CollatzResearch.WordTrace tailWord_4664263 prefixEnd_4664263 798336272660663261087317 := by
  unfold tailWord_4664263
  simp only [CollatzResearch.WordTrace]
  refine ⟨170119647501179218545525443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113413098334119479030350295 170119647501179218545525443)
  ·
    refine ⟨255179471251768827818288165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170119647501179218545525443 255179471251768827818288165)
    ·
      refine ⟨47846150859706655215929031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255179471251768827818288165 47846150859706655215929031)
      ·
        refine ⟨71769226289559982823893547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47846150859706655215929031 71769226289559982823893547)
        ·
          refine ⟨107653839434339974235840321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71769226289559982823893547 107653839434339974235840321)
          ·
            refine ⟨80740379575754980676880241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107653839434339974235840321 80740379575754980676880241)
            ·
              refine ⟨60555284681816235507660181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80740379575754980676880241 60555284681816235507660181)
              ·
                refine ⟨2838528969460136039421571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60555284681816235507660181 2838528969460136039421571)
                ·
                  refine ⟨4257793454190204059132357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2838528969460136039421571 4257793454190204059132357)
                  ·
                    refine ⟨798336272660663261087317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4257793454190204059132357 798336272660663261087317)
                    ·
                      rfl

theorem cell23_4664263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_4664263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664263 prefixEnd_4664263 := by exact prefixLift 4664263
  have htrace : WordTrace (prefixWord ++ tailWord_4664263) baseStart_4664263 baseEnd_4664263 := by
    simpa [prefixWord, tailWord_4664263, baseEnd_4664263] using wordTrace_append hprefix tailTrace_4664263
  have hstable : (prefixWord ++ tailWord_4664263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664263).length < 2 ^ (prefixWord ++ tailWord_4664263).sum := by decide
  have hdescent : baseEnd_4664263 < baseStart_4664263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664290 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_4664290 : Nat := 118140960795 + 4664290 * 2 ^ 59
def prefixEnd_4664290 : Nat := 4983230072969 + 3 ^ 40 * 4664290 * 2
def baseEnd_4664290 : Nat := 2395022681959661177624327

theorem tailTrace_4664290 : CollatzResearch.WordTrace tailWord_4664290 prefixEnd_4664290 2395022681959661177624327 := by
  unfold tailWord_4664290
  simp only [CollatzResearch.WordTrace]
  refine ⟨42530158068020350539189581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113413754848054268104505549 42530158068020350539189581)
  ·
    refine ⟨15948809275507631452196093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42530158068020350539189581 15948809275507631452196093)
    ·
      refine ⟨5980803478315361794573535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15948809275507631452196093 5980803478315361794573535)
      ·
        refine ⟨8971205217473042691860303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5980803478315361794573535 8971205217473042691860303)
        ·
          refine ⟨13456807826209564037790455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8971205217473042691860303 13456807826209564037790455)
          ·
            refine ⟨20185211739314346056685683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13456807826209564037790455 20185211739314346056685683)
            ·
              refine ⟨30277817608971519085028525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20185211739314346056685683 30277817608971519085028525)
              ·
                refine ⟨11354181603364319656885697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30277817608971519085028525 11354181603364319656885697)
                ·
                  refine ⟨8515636202523239742664273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11354181603364319656885697 8515636202523239742664273)
                  ·
                    refine ⟨6386727151892429806998205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8515636202523239742664273 6386727151892429806998205)
                    ·
                      refine ⟨2395022681959661177624327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6386727151892429806998205 2395022681959661177624327)
                      ·
                        rfl

theorem cell23_4664290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_4664290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664290 prefixEnd_4664290 := by exact prefixLift 4664290
  have htrace : WordTrace (prefixWord ++ tailWord_4664290) baseStart_4664290 baseEnd_4664290 := by
    simpa [prefixWord, tailWord_4664290, baseEnd_4664290] using wordTrace_append hprefix tailTrace_4664290
  have hstable : (prefixWord ++ tailWord_4664290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664290).length < 2 ^ (prefixWord ++ tailWord_4664290).sum := by decide
  have hdescent : baseEnd_4664290 < baseStart_4664290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664313 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 2, 3, 2]
def baseStart_4664313 : Nat := 118140960795 + 4664313 * 2 ^ 59
def prefixEnd_4664313 : Nat := 4983230072969 + 3 ^ 40 * 4664313 * 2
def baseEnd_4664313 : Nat := 2395034492014714587636721

theorem tailTrace_4664313 : CollatzResearch.WordTrace tailWord_4664313 prefixEnd_4664313 2395034492014714587636721 := by
  unfold tailWord_4664313
  simp only [CollatzResearch.WordTrace]
  refine ⟨170121471150998077084845593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113414314100665384723230395 170121471150998077084845593)
  ·
    refine ⟨127591103363248557813634195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170121471150998077084845593 127591103363248557813634195)
    ·
      refine ⟨191386655044872836720451293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127591103363248557813634195 191386655044872836720451293)
      ·
        refine ⟨71769995641827313770169235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191386655044872836720451293 71769995641827313770169235)
        ·
          refine ⟨107654993462740970655253853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71769995641827313770169235 107654993462740970655253853)
          ·
            refine ⟨40370622548527863995720195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107654993462740970655253853 40370622548527863995720195)
            ·
              refine ⟨60555933822791795993580293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40370622548527863995720195 60555933822791795993580293)
              ·
                refine ⟨11354237591773461748796305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60555933822791795993580293 11354237591773461748796305)
                ·
                  refine ⟨8515678193830096311597229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11354237591773461748796305 8515678193830096311597229)
                  ·
                    refine ⟨3193379322686286116848961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8515678193830096311597229 3193379322686286116848961)
                    ·
                      refine ⟨2395034492014714587636721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193379322686286116848961 2395034492014714587636721)
                      ·
                        rfl

theorem cell23_4664313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_4664313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664313 prefixEnd_4664313 := by exact prefixLift 4664313
  have htrace : WordTrace (prefixWord ++ tailWord_4664313) baseStart_4664313 baseEnd_4664313 := by
    simpa [prefixWord, tailWord_4664313, baseEnd_4664313] using wordTrace_append hprefix tailTrace_4664313
  have hstable : (prefixWord ++ tailWord_4664313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664313).length < 2 ^ (prefixWord ++ tailWord_4664313).sum := by decide
  have hdescent : baseEnd_4664313 < baseStart_4664313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664343 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4664343 : Nat := 118140960795 + 4664343 * 2 ^ 59
def prefixEnd_4664343 : Nat := 4983230072969 + 3 ^ 40 * 4664343 * 2
def baseEnd_4664343 : Nat := 2395049896434349470261583

theorem tailTrace_4664343 : CollatzResearch.WordTrace tailWord_4664343 prefixEnd_4664343 2395049896434349470261583 := by
  unfold tailWord_4664343
  simp only [CollatzResearch.WordTrace]
  refine ⟨170122565340889392208437683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113415043560592928138958455 170122565340889392208437683)
  ·
    refine ⟨255183848011334088312656525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170122565340889392208437683 255183848011334088312656525)
    ·
      refine ⟨95693943004250283117246197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255183848011334088312656525 95693943004250283117246197)
      ·
        refine ⟨8971307156648464042241831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95693943004250283117246197 8971307156648464042241831)
        ·
          refine ⟨13456960734972696063362747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8971307156648464042241831 13456960734972696063362747)
          ·
            refine ⟨20185441102459044095044121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13456960734972696063362747 20185441102459044095044121)
            ·
              refine ⟨15139080826844283071283091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20185441102459044095044121 15139080826844283071283091)
              ·
                refine ⟨22708621240266424606924637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15139080826844283071283091 22708621240266424606924637)
                ·
                  refine ⟨8515732965099909227596739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22708621240266424606924637 8515732965099909227596739)
                  ·
                    refine ⟨12773599447649863841395109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8515732965099909227596739 12773599447649863841395109)
                    ·
                      refine ⟨2395049896434349470261583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12773599447649863841395109 2395049896434349470261583)
                      ·
                        rfl

theorem cell23_4664343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4664343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664343 prefixEnd_4664343 := by exact prefixLift 4664343
  have htrace : WordTrace (prefixWord ++ tailWord_4664343) baseStart_4664343 baseEnd_4664343 := by
    simpa [prefixWord, tailWord_4664343, baseEnd_4664343] using wordTrace_append hprefix tailTrace_4664343
  have hstable : (prefixWord ++ tailWord_4664343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664343).length < 2 ^ (prefixWord ++ tailWord_4664343).sum := by decide
  have hdescent : baseEnd_4664343 < baseStart_4664343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664363 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 1, 2, 3]
def baseStart_4664363 : Nat := 118140960795 + 4664363 * 2 ^ 59
def prefixEnd_4664363 : Nat := 4983230072969 + 3 ^ 40 * 4664363 * 2
def baseEnd_4664363 : Nat := 2395060166047439392011491

theorem tailTrace_4664363 : CollatzResearch.WordTrace tailWord_4664363 prefixEnd_4664363 2395060166047439392011491 := by
  unfold tailWord_4664363
  simp only [CollatzResearch.WordTrace]
  refine ⟨170123294800816935624165743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113415529867211290416110495 170123294800816935624165743)
  ·
    refine ⟨255184942201225403436248615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170123294800816935624165743 255184942201225403436248615)
    ·
      refine ⟨382777413301838105154372923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255184942201225403436248615 382777413301838105154372923)
      ·
        refine ⟨574166119952757157731559385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382777413301838105154372923 574166119952757157731559385)
        ·
          refine ⟨430624589964567868298669539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 574166119952757157731559385 430624589964567868298669539)
          ·
            refine ⟨645936884946851802448004309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430624589964567868298669539 645936884946851802448004309)
            ·
              refine ⟨15139145740941839119875101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 645936884946851802448004309 15139145740941839119875101)
              ·
                refine ⟨5677179652853189669953163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15139145740941839119875101 5677179652853189669953163)
                ·
                  refine ⟨8515769479279784504929745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5677179652853189669953163 8515769479279784504929745)
                  ·
                    refine ⟨6386827109459838378697309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8515769479279784504929745 6386827109459838378697309)
                    ·
                      refine ⟨2395060166047439392011491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6386827109459838378697309 2395060166047439392011491)
                      ·
                        rfl

theorem cell23_4664363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 2, 3].length) (baseStart_4664363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664363 prefixEnd_4664363 := by exact prefixLift 4664363
  have htrace : WordTrace (prefixWord ++ tailWord_4664363) baseStart_4664363 baseEnd_4664363 := by
    simpa [prefixWord, tailWord_4664363, baseEnd_4664363] using wordTrace_append hprefix tailTrace_4664363
  have hstable : (prefixWord ++ tailWord_4664363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664363).length < 2 ^ (prefixWord ++ tailWord_4664363).sum := by decide
  have hdescent : baseEnd_4664363 < baseStart_4664363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664366 : List Nat := [4, 1, 3, 1, 1, 1, 12]
def baseStart_4664366 : Nat := 118140960795 + 4664366 * 2 ^ 59
def prefixEnd_4664366 : Nat := 4983230072969 + 3 ^ 40 * 4664366 * 2
def baseEnd_4664366 : Nat := 29568663043079047904617

theorem tailTrace_4664366 : CollatzResearch.WordTrace tailWord_4664366 prefixEnd_4664366 29568663043079047904617 := by
  unfold tailWord_4664366
  simp only [CollatzResearch.WordTrace]
  refine ⟨21265425527475758392065619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113415602813204044757683301 21265425527475758392065619)
  ·
    refine ⟨31898138291213637588098429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21265425527475758392065619 31898138291213637588098429)
    ·
      refine ⟨11961801859205114095536911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31898138291213637588098429 11961801859205114095536911)
      ·
        refine ⟨17942702788807671143305367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11961801859205114095536911 17942702788807671143305367)
        ·
          refine ⟨26914054183211506714958051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17942702788807671143305367 26914054183211506714958051)
          ·
            refine ⟨40371081274817260072437077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26914054183211506714958051 40371081274817260072437077)
            ·
              refine ⟨29568663043079047904617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 40371081274817260072437077 29568663043079047904617)
              ·
                rfl

theorem cell23_4664366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 12].length) (baseStart_4664366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664366 prefixEnd_4664366 := by exact prefixLift 4664366
  have htrace : WordTrace (prefixWord ++ tailWord_4664366) baseStart_4664366 baseEnd_4664366 := by
    simpa [prefixWord, tailWord_4664366, baseEnd_4664366] using wordTrace_append hprefix tailTrace_4664366
  have hstable : (prefixWord ++ tailWord_4664366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664366).length < 2 ^ (prefixWord ++ tailWord_4664366).sum := by decide
  have hdescent : baseEnd_4664366 < baseStart_4664366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664377 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 3, 2, 2]
def baseStart_4664377 : Nat := 118140960795 + 4664377 * 2 ^ 59
def prefixEnd_4664377 : Nat := 4983230072969 + 3 ^ 40 * 4664377 * 2
def baseEnd_4664377 : Nat := 2395067354776602337236427

theorem tailTrace_4664377 : CollatzResearch.WordTrace tailWord_4664377 prefixEnd_4664377 2395067354776602337236427 := by
  unfold tailWord_4664377
  simp only [CollatzResearch.WordTrace]
  refine ⟨170123805422766216015175385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113415870281844144010116923 170123805422766216015175385)
  ·
    refine ⟨127592854067074662011381539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170123805422766216015175385 127592854067074662011381539)
    ·
      refine ⟨191389281100611993017072309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127592854067074662011381539 191389281100611993017072309)
      ·
        refine ⟨17942745103182374345350529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191389281100611993017072309 17942745103182374345350529)
        ·
          refine ⟨13457058827386780759012897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17942745103182374345350529 13457058827386780759012897)
          ·
            refine ⟨10092794120540085569259673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13457058827386780759012897 10092794120540085569259673)
            ·
              refine ⟨7569595590405064176944755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10092794120540085569259673 7569595590405064176944755)
              ·
                refine ⟨11354393385607596265417133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7569595590405064176944755 11354393385607596265417133)
                ·
                  refine ⟨4257897519602848599531425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11354393385607596265417133 4257897519602848599531425)
                  ·
                    refine ⟨3193423139702136449648569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257897519602848599531425 3193423139702136449648569)
                    ·
                      refine ⟨2395067354776602337236427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193423139702136449648569 2395067354776602337236427)
                      ·
                        rfl

theorem cell23_4664377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_4664377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664377 prefixEnd_4664377 := by exact prefixLift 4664377
  have htrace : WordTrace (prefixWord ++ tailWord_4664377) baseStart_4664377 baseEnd_4664377 := by
    simpa [prefixWord, tailWord_4664377, baseEnd_4664377] using wordTrace_append hprefix tailTrace_4664377
  have hstable : (prefixWord ++ tailWord_4664377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664377).length < 2 ^ (prefixWord ++ tailWord_4664377).sum := by decide
  have hdescent : baseEnd_4664377 < baseStart_4664377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664390 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_4664390 : Nat := 118140960795 + 4664390 * 2 ^ 59
def prefixEnd_4664390 : Nat := 4983230072969 + 3 ^ 40 * 4664390 * 2
def baseEnd_4664390 : Nat := 2395074030025110786373867

theorem tailTrace_4664390 : CollatzResearch.WordTrace tailWord_4664390 prefixEnd_4664390 2395074030025110786373867 := by
  unfold tailWord_4664390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5316383736616222476106207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113416186381146079490265749 5316383736616222476106207)
  ·
    refine ⟨7974575604924333714159311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5316383736616222476106207 7974575604924333714159311)
    ·
      refine ⟨11961863407386500571238967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7974575604924333714159311 11961863407386500571238967)
      ·
        refine ⟨17942795111079750856858451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11961863407386500571238967 17942795111079750856858451)
        ·
          refine ⟨26914192666619626285287677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17942795111079750856858451 26914192666619626285287677)
          ·
            refine ⟨10092822249982359856982879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26914192666619626285287677 10092822249982359856982879)
            ·
              refine ⟨15139233374973539785474319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10092822249982359856982879 15139233374973539785474319)
              ·
                refine ⟨22708850062460309678211479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15139233374973539785474319 22708850062460309678211479)
                ·
                  refine ⟨34063275093690464517317219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22708850062460309678211479 34063275093690464517317219)
                  ·
                    refine ⟨51094912640535696775975829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34063275093690464517317219 51094912640535696775975829)
                    ·
                      refine ⟨2395074030025110786373867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51094912640535696775975829 2395074030025110786373867)
                      ·
                        rfl

theorem cell23_4664390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_4664390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664390 prefixEnd_4664390 := by exact prefixLift 4664390
  have htrace : WordTrace (prefixWord ++ tailWord_4664390) baseStart_4664390 baseEnd_4664390 := by
    simpa [prefixWord, tailWord_4664390, baseEnd_4664390] using wordTrace_append hprefix tailTrace_4664390
  have hstable : (prefixWord ++ tailWord_4664390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664390).length < 2 ^ (prefixWord ++ tailWord_4664390).sum := by decide
  have hdescent : baseEnd_4664390 < baseStart_4664390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664397 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_4664397 : Nat := 118140960795 + 4664397 * 2 ^ 59
def prefixEnd_4664397 : Nat := 4983230072969 + 3 ^ 40 * 4664397 * 2
def baseEnd_4664397 : Nat := 2395077624389692258986335

theorem tailTrace_4664397 : CollatzResearch.WordTrace tailWord_4664397 prefixEnd_4664397 2395077624389692258986335 := by
  unfold tailWord_4664397
  simp only [CollatzResearch.WordTrace]
  refine ⟨170124534882693759430903445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113416356588462506287268963 170124534882693759430903445)
  ·
    refine ⟨7974587572626269973323599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 170124534882693759430903445 7974587572626269973323599)
    ·
      refine ⟨11961881358939404959985399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7974587572626269973323599 11961881358939404959985399)
      ·
        refine ⟨17942822038409107439978099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11961881358939404959985399 17942822038409107439978099)
        ·
          refine ⟨26914233057613661159967149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17942822038409107439978099 26914233057613661159967149)
          ·
            refine ⟨10092837396605122934987681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26914233057613661159967149 10092837396605122934987681)
            ·
              refine ⟨7569628047453842201240761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10092837396605122934987681 7569628047453842201240761)
              ·
                refine ⟨5677221035590381650930571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7569628047453842201240761 5677221035590381650930571)
                ·
                  refine ⟨8515831553385572476395857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5677221035590381650930571 8515831553385572476395857)
                  ·
                    refine ⟨6386873665039179357296893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8515831553385572476395857 6386873665039179357296893)
                    ·
                      refine ⟨2395077624389692258986335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6386873665039179357296893 2395077624389692258986335)
                      ·
                        rfl

theorem cell23_4664397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_4664397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664397 prefixEnd_4664397 := by exact prefixLift 4664397
  have htrace : WordTrace (prefixWord ++ tailWord_4664397) baseStart_4664397 baseEnd_4664397 := by
    simpa [prefixWord, tailWord_4664397, baseEnd_4664397] using wordTrace_append hprefix tailTrace_4664397
  have hstable : (prefixWord ++ tailWord_4664397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664397).length < 2 ^ (prefixWord ++ tailWord_4664397).sum := by decide
  have hdescent : baseEnd_4664397 < baseStart_4664397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664414 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_4664414 : Nat := 118140960795 + 4664414 * 2 ^ 59
def prefixEnd_4664414 : Nat := 4983230072969 + 3 ^ 40 * 4664414 * 2
def baseEnd_4664414 : Nat := 2395086353560818692473757

theorem tailTrace_4664414 : CollatzResearch.WordTrace tailWord_4664414 prefixEnd_4664414 2395086353560818692473757 := by
  unfold tailWord_4664414
  simp only [CollatzResearch.WordTrace]
  refine ⟨21265644365454021416784037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113416769949088114222848197 21265644365454021416784037)
  ·
    refine ⟨3987308318522629015647007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21265644365454021416784037 3987308318522629015647007)
    ·
      refine ⟨5980962477783943523470511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3987308318522629015647007 5980962477783943523470511)
      ·
        refine ⟨8971443716675915285205767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5980962477783943523470511 8971443716675915285205767)
        ·
          refine ⟨13457165575013872927808651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8971443716675915285205767 13457165575013872927808651)
          ·
            refine ⟨20185748362520809391712977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13457165575013872927808651 20185748362520809391712977)
            ·
              refine ⟨15139311271890607043784733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20185748362520809391712977 15139311271890607043784733)
              ·
                refine ⟨5677241726958977641419275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15139311271890607043784733 5677241726958977641419275)
                ·
                  refine ⟨8515862590438466462128913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5677241726958977641419275 8515862590438466462128913)
                  ·
                    refine ⟨6386896942828849846596685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8515862590438466462128913 6386896942828849846596685)
                    ·
                      refine ⟨2395086353560818692473757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6386896942828849846596685 2395086353560818692473757)
                      ·
                        rfl

theorem cell23_4664414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_4664414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664414 prefixEnd_4664414 := by exact prefixLift 4664414
  have htrace : WordTrace (prefixWord ++ tailWord_4664414) baseStart_4664414 baseEnd_4664414 := by
    simpa [prefixWord, tailWord_4664414, baseEnd_4664414] using wordTrace_append hprefix tailTrace_4664414
  have hstable : (prefixWord ++ tailWord_4664414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664414).length < 2 ^ (prefixWord ++ tailWord_4664414).sum := by decide
  have hdescent : baseEnd_4664414 < baseStart_4664414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664433 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 5, 4, 2]
def baseStart_4664433 : Nat := 118140960795 + 4664433 * 2 ^ 59
def prefixEnd_4664433 : Nat := 4983230072969 + 3 ^ 40 * 4664433 * 2
def baseEnd_4664433 : Nat := 2395096109693254118136169

theorem tailTrace_4664433 : CollatzResearch.WordTrace tailWord_4664433 prefixEnd_4664433 2395096109693254118136169 := by
  unfold tailWord_4664433
  simp only [CollatzResearch.WordTrace]
  refine ⟨170125847910563337579213953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113417231940375558386142635 170125847910563337579213953)
  ·
    refine ⟨127594385932922503184410465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170125847910563337579213953 127594385932922503184410465)
    ·
      refine ⟨95695789449691877388307849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127594385932922503184410465 95695789449691877388307849)
      ·
        refine ⟨71771842087268908041230887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95695789449691877388307849 71771842087268908041230887)
        ·
          refine ⟨107657763130903362061846331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71771842087268908041230887 107657763130903362061846331)
          ·
            refine ⟨161486644696355043092769497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107657763130903362061846331 161486644696355043092769497)
            ·
              refine ⟨121114983522266282319577123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161486644696355043092769497 121114983522266282319577123)
              ·
                refine ⟨181672475283399423479365685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121114983522266282319577123 181672475283399423479365685)
                ·
                  refine ⟨17031794557818695951190533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 181672475283399423479365685 17031794557818695951190533)
                  ·
                    refine ⟨3193461479591005490848225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17031794557818695951190533 3193461479591005490848225)
                    ·
                      refine ⟨2395096109693254118136169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193461479591005490848225 2395096109693254118136169)
                      ·
                        rfl

theorem cell23_4664433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_4664433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664433 prefixEnd_4664433 := by exact prefixLift 4664433
  have htrace : WordTrace (prefixWord ++ tailWord_4664433) baseStart_4664433 baseEnd_4664433 := by
    simpa [prefixWord, tailWord_4664433, baseEnd_4664433] using wordTrace_append hprefix tailTrace_4664433
  have hstable : (prefixWord ++ tailWord_4664433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664433).length < 2 ^ (prefixWord ++ tailWord_4664433).sum := by decide
  have hdescent : baseEnd_4664433 < baseStart_4664433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664484 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 2, 2, 2]
def baseStart_4664484 : Nat := 118140960795 + 4664484 * 2 ^ 59
def prefixEnd_4664484 : Nat := 4983230072969 + 3 ^ 40 * 4664484 * 2
def baseEnd_4664484 : Nat := 2395122297206633418598435

theorem tailTrace_4664484 : CollatzResearch.WordTrace tailWord_4664484 prefixEnd_4664484 2395122297206633418598435 := by
  unfold tailWord_4664484
  simp only [CollatzResearch.WordTrace]
  refine ⟨85063854016689286644660253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113418472022252382192880337 85063854016689286644660253)
  ·
    refine ⟨31898945256258482491747595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85063854016689286644660253 31898945256258482491747595)
    ·
      refine ⟨47848417884387723737621393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31898945256258482491747595 47848417884387723737621393)
      ·
        refine ⟨35886313413290792803216045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47848417884387723737621393 35886313413290792803216045)
        ·
          refine ⟨13457367529984047301206017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35886313413290792803216045 13457367529984047301206017)
          ·
            refine ⟨10093025647488035475904513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13457367529984047301206017 10093025647488035475904513)
            ·
              refine ⟨7569769235616026606928385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10093025647488035475904513 7569769235616026606928385)
              ·
                refine ⟨5677326926712019955196289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7569769235616026606928385 5677326926712019955196289)
                ·
                  refine ⟨4257995195034014966397217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5677326926712019955196289 4257995195034014966397217)
                  ·
                    refine ⟨3193496396275511224797913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257995195034014966397217 3193496396275511224797913)
                    ·
                      refine ⟨2395122297206633418598435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193496396275511224797913 2395122297206633418598435)
                      ·
                        rfl

theorem cell23_4664484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_4664484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664484 prefixEnd_4664484 := by exact prefixLift 4664484
  have htrace : WordTrace (prefixWord ++ tailWord_4664484) baseStart_4664484 baseEnd_4664484 := by
    simpa [prefixWord, tailWord_4664484, baseEnd_4664484] using wordTrace_append hprefix tailTrace_4664484
  have hstable : (prefixWord ++ tailWord_4664484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664484).length < 2 ^ (prefixWord ++ tailWord_4664484).sum := by decide
  have hdescent : baseEnd_4664484 < baseStart_4664484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664523 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 4]
def baseStart_4664523 : Nat := 118140960795 + 4664523 * 2 ^ 59
def prefixEnd_4664523 : Nat := 4983230072969 + 3 ^ 40 * 4664523 * 2
def baseEnd_4664523 : Nat := 2395142322952158766010755

theorem tailTrace_4664523 : CollatzResearch.WordTrace tailWord_4664523 prefixEnd_4664523 2395142322952158766010755 := by
  unfold tailWord_4664523
  simp only [CollatzResearch.WordTrace]
  refine ⟨170129130480237282949990223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113419420320158188633326815 170129130480237282949990223)
  ·
    refine ⟨255193695720355924424985335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170129130480237282949990223 255193695720355924424985335)
    ·
      refine ⟨382790543580533886637478003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255193695720355924424985335 382790543580533886637478003)
      ·
        refine ⟨574185815370800829956217005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382790543580533886637478003 574185815370800829956217005)
        ·
          refine ⟨215319680764050311233581377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 574185815370800829956217005 215319680764050311233581377)
          ·
            refine ⟨161489760573037733425186033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215319680764050311233581377 161489760573037733425186033)
            ·
              refine ⟨121117320429778300068889525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161489760573037733425186033 121117320429778300068889525)
              ·
                refine ⟨11354748790291715631458393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121117320429778300068889525 11354748790291715631458393)
                ·
                  refine ⟨8516061592718786723593795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11354748790291715631458393 8516061592718786723593795)
                  ·
                    refine ⟨12774092389078180085390693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8516061592718786723593795 12774092389078180085390693)
                    ·
                      refine ⟨2395142322952158766010755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12774092389078180085390693 2395142322952158766010755)
                      ·
                        rfl

theorem cell23_4664523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 4].length) (baseStart_4664523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664523 prefixEnd_4664523 := by exact prefixLift 4664523
  have htrace : WordTrace (prefixWord ++ tailWord_4664523) baseStart_4664523 baseEnd_4664523 := by
    simpa [prefixWord, tailWord_4664523, baseEnd_4664523] using wordTrace_append hprefix tailTrace_4664523
  have hstable : (prefixWord ++ tailWord_4664523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664523).length < 2 ^ (prefixWord ++ tailWord_4664523).sum := by decide
  have hdescent : baseEnd_4664523 < baseStart_4664523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664557 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_4664557 : Nat := 118140960795 + 4664557 * 2 ^ 59
def prefixEnd_4664557 : Nat := 4983230072969 + 3 ^ 40 * 4664557 * 2
def baseEnd_4664557 : Nat := 2395159781294411632985599

theorem tailTrace_4664557 : CollatzResearch.WordTrace tailWord_4664557 prefixEnd_4664557 2395159781294411632985599 := by
  unfold tailWord_4664557
  simp only [CollatzResearch.WordTrace]
  refine ⟨170130370562114106756727925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113420247041409404504485283 170130370562114106756727925)
  ·
    refine ⟨15949722240198197508443243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170130370562114106756727925 15949722240198197508443243)
    ·
      refine ⟨23924583360297296262664865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15949722240198197508443243 23924583360297296262664865)
      ·
        refine ⟨17943437520222972196998649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23924583360297296262664865 17943437520222972196998649)
        ·
          refine ⟨13457578140167229147748987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17943437520222972196998649 13457578140167229147748987)
          ·
            refine ⟨20186367210250843721623481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13457578140167229147748987 20186367210250843721623481)
            ·
              refine ⟨15139775407688132791217611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20186367210250843721623481 15139775407688132791217611)
              ·
                refine ⟨22709663111532199186826417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15139775407688132791217611 22709663111532199186826417)
                ·
                  refine ⟨17032247333649149390119813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22709663111532199186826417 17032247333649149390119813)
                  ·
                    refine ⟨3193546375059215510647465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17032247333649149390119813 3193546375059215510647465)
                    ·
                      refine ⟨2395159781294411632985599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193546375059215510647465 2395159781294411632985599)
                      ·
                        rfl

theorem cell23_4664557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_4664557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664557 prefixEnd_4664557 := by exact prefixLift 4664557
  have htrace : WordTrace (prefixWord ++ tailWord_4664557) baseStart_4664557 baseEnd_4664557 := by
    simpa [prefixWord, tailWord_4664557, baseEnd_4664557] using wordTrace_append hprefix tailTrace_4664557
  have hstable : (prefixWord ++ tailWord_4664557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664557).length < 2 ^ (prefixWord ++ tailWord_4664557).sum := by decide
  have hdescent : baseEnd_4664557 < baseStart_4664557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664623 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 1, 6]
def baseStart_4664623 : Nat := 118140960795 + 4664623 * 2 ^ 59
def prefixEnd_4664623 : Nat := 4983230072969 + 3 ^ 40 * 4664623 * 2
def baseEnd_4664623 : Nat := 798397890339202791586765

theorem tailTrace_4664623 : CollatzResearch.WordTrace tailWord_4664623 prefixEnd_4664623 798397890339202791586765 := by
  unfold tailWord_4664623
  simp only [CollatzResearch.WordTrace]
  refine ⟨170132777779875000028630523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113421851853250000019087015 170132777779875000028630523)
  ·
    refine ⟨255199166669812500042945785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170132777779875000028630523 255199166669812500042945785)
    ·
      refine ⟨191399375002359375032209339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255199166669812500042945785 191399375002359375032209339)
      ·
        refine ⟨287099062503539062548314009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191399375002359375032209339 287099062503539062548314009)
        ·
          refine ⟨215324296877654296911235507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287099062503539062548314009 215324296877654296911235507)
          ·
            refine ⟨322986445316481445366853261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215324296877654296911235507 322986445316481445366853261)
            ·
              refine ⟨121119916993680542012569973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 322986445316481445366853261 121119916993680542012569973)
              ·
                refine ⟨11354992218157550813678435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121119916993680542012569973 11354992218157550813678435)
                ·
                  refine ⟨17032488327236326220517653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11354992218157550813678435 17032488327236326220517653)
                  ·
                    refine ⟨798397890339202791586765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17032488327236326220517653 798397890339202791586765)
                    ·
                      rfl

theorem cell23_4664623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_4664623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664623 prefixEnd_4664623 := by exact prefixLift 4664623
  have htrace : WordTrace (prefixWord ++ tailWord_4664623) baseStart_4664623 baseEnd_4664623 := by
    simpa [prefixWord, tailWord_4664623, baseEnd_4664623] using wordTrace_append hprefix tailTrace_4664623
  have hstable : (prefixWord ++ tailWord_4664623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664623).length < 2 ^ (prefixWord ++ tailWord_4664623).sum := by decide
  have hdescent : baseEnd_4664623 < baseStart_4664623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664627 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 1, 5]
def baseStart_4664627 : Nat := 118140960795 + 4664627 * 2 ^ 59
def prefixEnd_4664627 : Nat := 4983230072969 + 3 ^ 40 * 4664627 * 2
def baseEnd_4664627 : Nat := 798398574980075453036759

theorem tailTrace_4664627 : CollatzResearch.WordTrace tailWord_4664627 prefixEnd_4664627 798398574980075453036759 := by
  unfold tailWord_4664627
  simp only [CollatzResearch.WordTrace]
  refine ⟨170132923671860508711776135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113421949114573672474517423 170132923671860508711776135)
  ·
    refine ⟨255199385507790763067664203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170132923671860508711776135 255199385507790763067664203)
    ·
      refine ⟨382799078261686144601496305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255199385507790763067664203 382799078261686144601496305)
      ·
        refine ⟨287099308696264608451122229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382799078261686144601496305 287099308696264608451122229)
        ·
          refine ⟨26915560190274807042292709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 287099308696264608451122229 26915560190274807042292709)
          ·
            refine ⟨5046667535676526320429883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26915560190274807042292709 5046667535676526320429883)
            ·
              refine ⟨7570001303514789480644825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5046667535676526320429883 7570001303514789480644825)
              ·
                refine ⟨5677500977636092110483619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7570001303514789480644825 5677500977636092110483619)
                ·
                  refine ⟨8516251466454138165725429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5677500977636092110483619 8516251466454138165725429)
                  ·
                    refine ⟨798398574980075453036759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8516251466454138165725429 798398574980075453036759)
                    ·
                      rfl

theorem cell23_4664627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 5].length) (baseStart_4664627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664627 prefixEnd_4664627 := by exact prefixLift 4664627
  have htrace : WordTrace (prefixWord ++ tailWord_4664627) baseStart_4664627 baseEnd_4664627 := by
    simpa [prefixWord, tailWord_4664627, baseEnd_4664627] using wordTrace_append hprefix tailTrace_4664627
  have hstable : (prefixWord ++ tailWord_4664627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664627).length < 2 ^ (prefixWord ++ tailWord_4664627).sum := by decide
  have hdescent : baseEnd_4664627 < baseStart_4664627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664657 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 2, 4]
def baseStart_4664657 : Nat := 118140960795 + 4664657 * 2 ^ 59
def prefixEnd_4664657 : Nat := 4983230072969 + 3 ^ 40 * 4664657 * 2
def baseEnd_4664657 : Nat := 798403709786620413911713

theorem tailTrace_4664657 : CollatzResearch.WordTrace tailWord_4664657 prefixEnd_4664657 798403709786620413911713 := by
  unfold tailWord_4664657
  simp only [CollatzResearch.WordTrace]
  refine ⟨170134017861751823835368225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113422678574501215890245483 170134017861751823835368225)
  ·
    refine ⟨127600513396313867876526169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170134017861751823835368225 127600513396313867876526169)
    ·
      refine ⟨95700385047235400907394627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127600513396313867876526169 95700385047235400907394627)
      ·
        refine ⟨143550577570853101361091941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95700385047235400907394627 143550577570853101361091941)
        ·
          refine ⟨26915733294534956505204739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143550577570853101361091941 26915733294534956505204739)
          ·
            refine ⟨40373599941802434757807109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26915733294534956505204739 40373599941802434757807109)
            ·
              refine ⟨7570049989087956517088833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40373599941802434757807109 7570049989087956517088833)
              ·
                refine ⟨5677537491815967387816625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7570049989087956517088833 5677537491815967387816625)
                ·
                  refine ⟨4258153118861975540862469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5677537491815967387816625 4258153118861975540862469)
                  ·
                    refine ⟨798403709786620413911713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4258153118861975540862469 798403709786620413911713)
                    ·
                      rfl

theorem cell23_4664657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_4664657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664657 prefixEnd_4664657 := by exact prefixLift 4664657
  have htrace : WordTrace (prefixWord ++ tailWord_4664657) baseStart_4664657 baseEnd_4664657 := by
    simpa [prefixWord, tailWord_4664657, baseEnd_4664657] using wordTrace_append hprefix tailTrace_4664657
  have hstable : (prefixWord ++ tailWord_4664657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664657).length < 2 ^ (prefixWord ++ tailWord_4664657).sum := by decide
  have hdescent : baseEnd_4664657 < baseStart_4664657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664660 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_4664660 : Nat := 118140960795 + 4664660 * 2 ^ 59
def prefixEnd_4664660 : Nat := 4983230072969 + 3 ^ 40 * 4664660 * 2
def baseEnd_4664660 : Nat := 2395212669801824729997625

theorem tailTrace_4664660 : CollatzResearch.WordTrace tailWord_4664660 prefixEnd_4664660 2395212669801824729997625 := by
  unfold tailWord_4664660
  simp only [CollatzResearch.WordTrace]
  refine ⟨85067063640370477673863717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113422751520493970231818289 85067063640370477673863717)
  ·
    refine ⟨15950074432569464563849447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85067063640370477673863717 15950074432569464563849447)
    ·
      refine ⟨23925111648854196845774171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15950074432569464563849447 23925111648854196845774171)
      ·
        refine ⟨35887667473281295268661257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23925111648854196845774171 35887667473281295268661257)
        ·
          refine ⟨26915750604960971451495943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35887667473281295268661257 26915750604960971451495943)
          ·
            refine ⟨40373625907441457177243915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26915750604960971451495943 40373625907441457177243915)
            ·
              refine ⟨60560438861162185765865873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40373625907441457177243915 60560438861162185765865873)
              ·
                refine ⟨45420329145871639324399405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60560438861162185765865873 45420329145871639324399405)
                ·
                  refine ⟨17032623429701864746649777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45420329145871639324399405 17032623429701864746649777)
                  ·
                    refine ⟨12774467572276398559987333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17032623429701864746649777 12774467572276398559987333)
                    ·
                      refine ⟨2395212669801824729997625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12774467572276398559987333 2395212669801824729997625)
                      ·
                        rfl

theorem cell23_4664660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_4664660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664660 prefixEnd_4664660 := by exact prefixLift 4664660
  have htrace : WordTrace (prefixWord ++ tailWord_4664660) baseStart_4664660 baseEnd_4664660 := by
    simpa [prefixWord, tailWord_4664660, baseEnd_4664660] using wordTrace_append hprefix tailTrace_4664660
  have hstable : (prefixWord ++ tailWord_4664660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664660).length < 2 ^ (prefixWord ++ tailWord_4664660).sum := by decide
  have hdescent : baseEnd_4664660 < baseStart_4664660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664673 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_4664673 : Nat := 118140960795 + 4664673 * 2 ^ 59
def prefixEnd_4664673 : Nat := 4983230072969 + 3 ^ 40 * 4664673 * 2
def baseEnd_4664673 : Nat := 2395219345050333179135065

theorem tailTrace_4664673 : CollatzResearch.WordTrace tailWord_4664673 prefixEnd_4664673 2395219345050333179135065 := by
  unfold tailWord_4664673
  simp only [CollatzResearch.WordTrace]
  refine ⟨170134601429693858567950673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113423067619795905711967115 170134601429693858567950673)
  ·
    refine ⟨127600951072270393925963005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170134601429693858567950673 127600951072270393925963005)
    ·
      refine ⟨47850356652101397722236127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127600951072270393925963005 47850356652101397722236127)
      ·
        refine ⟨71775534978152096583354191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47850356652101397722236127 71775534978152096583354191)
        ·
          refine ⟨107663302467228144875031287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71775534978152096583354191 107663302467228144875031287)
          ·
            refine ⟨161494953700842217312546931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107663302467228144875031287 161494953700842217312546931)
            ·
              refine ⟨242242430551263325968820397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161494953700842217312546931 242242430551263325968820397)
              ·
                refine ⟨90840911456723747238307649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242242430551263325968820397 90840911456723747238307649)
                ·
                  refine ⟨68130683592542810428730737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90840911456723747238307649 68130683592542810428730737)
                  ·
                    refine ⟨51098012694407107821548053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68130683592542810428730737 51098012694407107821548053)
                    ·
                      refine ⟨2395219345050333179135065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51098012694407107821548053 2395219345050333179135065)
                      ·
                        rfl

theorem cell23_4664673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_4664673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664673 prefixEnd_4664673 := by exact prefixLift 4664673
  have htrace : WordTrace (prefixWord ++ tailWord_4664673) baseStart_4664673 baseEnd_4664673 := by
    simpa [prefixWord, tailWord_4664673, baseEnd_4664673] using wordTrace_append hprefix tailTrace_4664673
  have hstable : (prefixWord ++ tailWord_4664673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664673).length < 2 ^ (prefixWord ++ tailWord_4664673).sum := by decide
  have hdescent : baseEnd_4664673 < baseStart_4664673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664730 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_4664730 : Nat := 118140960795 + 4664730 * 2 ^ 59
def prefixEnd_4664730 : Nat := 4983230072969 + 3 ^ 40 * 4664730 * 2
def baseEnd_4664730 : Nat := 798416204482546485374101

theorem tailTrace_4664730 : CollatzResearch.WordTrace tailWord_4664730 prefixEnd_4664730 798416204482546485374101 := by
  unfold tailWord_4664730
  simp only [CollatzResearch.WordTrace]
  refine ⟨42534170097621839325693911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113424453593658238201850429 42534170097621839325693911)
  ·
    refine ⟨63801255146432758988540867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42534170097621839325693911 63801255146432758988540867)
    ·
      refine ⟨95701882719649138482811301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63801255146432758988540867 95701882719649138482811301)
      ·
        refine ⟨17944103009934213465527119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95701882719649138482811301 17944103009934213465527119)
        ·
          refine ⟨26916154514901320198290679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17944103009934213465527119 26916154514901320198290679)
          ·
            refine ⟨40374231772351980297436019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26916154514901320198290679 40374231772351980297436019)
            ·
              refine ⟨60561347658527970446154029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40374231772351980297436019 60561347658527970446154029)
              ·
                refine ⟨22710505371947988917307761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60561347658527970446154029 22710505371947988917307761)
                ·
                  refine ⟨17032879028960991687980821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22710505371947988917307761 17032879028960991687980821)
                  ·
                    refine ⟨798416204482546485374101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17032879028960991687980821 798416204482546485374101)
                    ·
                      rfl

theorem cell23_4664730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_4664730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664730 prefixEnd_4664730 := by exact prefixLift 4664730
  have htrace : WordTrace (prefixWord ++ tailWord_4664730) baseStart_4664730 baseEnd_4664730 := by
    simpa [prefixWord, tailWord_4664730, baseEnd_4664730] using wordTrace_append hprefix tailTrace_4664730
  have hstable : (prefixWord ++ tailWord_4664730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664730).length < 2 ^ (prefixWord ++ tailWord_4664730).sum := by decide
  have hdescent : baseEnd_4664730 < baseStart_4664730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664740 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_4664740 : Nat := 118140960795 + 4664740 * 2 ^ 59
def prefixEnd_4664740 : Nat := 4983230072969 + 3 ^ 40 * 4664740 * 2
def baseEnd_4664740 : Nat := 2395253748254184416997257

theorem tailTrace_4664740 : CollatzResearch.WordTrace tailWord_4664740 prefixEnd_4664740 2395253748254184416997257 := by
  unfold tailWord_4664740
  simp only [CollatzResearch.WordTrace]
  refine ⟨85068522560225564505319837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113424696746967419340426449 85068522560225564505319837)
  ·
    refine ⟨31900695960084586689494939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85068522560225564505319837 31900695960084586689494939)
    ·
      refine ⟨47851043940126880034242409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31900695960084586689494939 47851043940126880034242409)
      ·
        refine ⟨35888282955095160025681807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47851043940126880034242409 35888282955095160025681807)
        ·
          refine ⟨53832424432642740038522711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35888282955095160025681807 53832424432642740038522711)
          ·
            refine ⟨80748636648964110057784067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53832424432642740038522711 80748636648964110057784067)
            ·
              refine ⟨121122954973446165086676101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80748636648964110057784067 121122954973446165086676101)
              ·
                refine ⟨22710554057521155953751769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121122954973446165086676101 22710554057521155953751769)
                ·
                  refine ⟨17032915543140866965313827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22710554057521155953751769 17032915543140866965313827)
                  ·
                    refine ⟨25549373314711300447970741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17032915543140866965313827 25549373314711300447970741)
                    ·
                      refine ⟨2395253748254184416997257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25549373314711300447970741 2395253748254184416997257)
                      ·
                        rfl

theorem cell23_4664740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_4664740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664740 prefixEnd_4664740 := by exact prefixLift 4664740
  have htrace : WordTrace (prefixWord ++ tailWord_4664740) baseStart_4664740 baseEnd_4664740 := by
    simpa [prefixWord, tailWord_4664740, baseEnd_4664740] using wordTrace_append hprefix tailTrace_4664740
  have hstable : (prefixWord ++ tailWord_4664740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664740).length < 2 ^ (prefixWord ++ tailWord_4664740).sum := by decide
  have hdescent : baseEnd_4664740 < baseStart_4664740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664757 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4664757 : Nat := 118140960795 + 4664757 * 2 ^ 59
def prefixEnd_4664757 : Nat := 4983230072969 + 3 ^ 40 * 4664757 * 2
def baseEnd_4664757 : Nat := 2395262477425310850484679

theorem tailTrace_4664757 : CollatzResearch.WordTrace tailWord_4664757 prefixEnd_4664757 2395262477425310850484679 := by
  unfold tailWord_4664757
  simp only [CollatzResearch.WordTrace]
  refine ⟨170137665161389540914008525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113425110107593027276005683 170137665161389540914008525)
  ·
    refine ⟨63801624435521077842753197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170137665161389540914008525 63801624435521077842753197)
    ·
      refine ⟨23925609163320404191032449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63801624435521077842753197 23925609163320404191032449)
      ·
        refine ⟨17944206872490303143274337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23925609163320404191032449 17944206872490303143274337)
        ·
          refine ⟨13458155154367727357455753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17944206872490303143274337 13458155154367727357455753)
          ·
            refine ⟨10093616365775795518091815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13458155154367727357455753 10093616365775795518091815)
            ·
              refine ⟨15140424548663693277137723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10093616365775795518091815 15140424548663693277137723)
              ·
                refine ⟨22710636822995539915706585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15140424548663693277137723 22710636822995539915706585)
                ·
                  refine ⟨17032977617246654936779939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22710636822995539915706585 17032977617246654936779939)
                  ·
                    refine ⟨25549466425869982405169909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17032977617246654936779939 25549466425869982405169909)
                    ·
                      refine ⟨2395262477425310850484679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25549466425869982405169909 2395262477425310850484679)
                      ·
                        rfl

theorem cell23_4664757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4664757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664757 prefixEnd_4664757 := by exact prefixLift 4664757
  have htrace : WordTrace (prefixWord ++ tailWord_4664757) baseStart_4664757 baseEnd_4664757 := by
    simpa [prefixWord, tailWord_4664757, baseEnd_4664757] using wordTrace_append hprefix tailTrace_4664757
  have hstable : (prefixWord ++ tailWord_4664757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664757).length < 2 ^ (prefixWord ++ tailWord_4664757).sum := by decide
  have hdescent : baseEnd_4664757 < baseStart_4664757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664788 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_4664788 : Nat := 118140960795 + 4664788 * 2 ^ 59
def prefixEnd_4664788 : Nat := 4983230072969 + 3 ^ 40 * 4664788 * 2
def baseEnd_4664788 : Nat := 2395278395325600229197037

theorem tailTrace_4664788 : CollatzResearch.WordTrace tailWord_4664788 prefixEnd_4664788 2395278395325600229197037 := by
  unfold tailWord_4664788
  simp only [CollatzResearch.WordTrace]
  refine ⟨85069397912138616604193509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113425863882851488805591345 85069397912138616604193509)
  ·
    refine ⟨15950512108525990613286283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85069397912138616604193509 15950512108525990613286283)
    ·
      refine ⟨23925768162788985919929425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15950512108525990613286283 23925768162788985919929425)
      ·
        refine ⟨17944326122091739439947069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23925768162788985919929425 17944326122091739439947069)
        ·
          refine ⟨6729122295784402289980151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17944326122091739439947069 6729122295784402289980151)
          ·
            refine ⟨10093683443676603434970227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6729122295784402289980151 10093683443676603434970227)
            ·
              refine ⟨15140525165514905152455341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10093683443676603434970227 15140525165514905152455341)
              ·
                refine ⟨5677696937068089432170753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15140525165514905152455341 5677696937068089432170753)
                ·
                  refine ⟨4258272702801067074128065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5677696937068089432170753 4258272702801067074128065)
                  ·
                    refine ⟨3193704527100800305596049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4258272702801067074128065 3193704527100800305596049)
                    ·
                      refine ⟨2395278395325600229197037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193704527100800305596049 2395278395325600229197037)
                      ·
                        rfl

theorem cell23_4664788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_4664788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664788 prefixEnd_4664788 := by exact prefixLift 4664788
  have htrace : WordTrace (prefixWord ++ tailWord_4664788) baseStart_4664788 baseEnd_4664788 := by
    simpa [prefixWord, tailWord_4664788, baseEnd_4664788] using wordTrace_append hprefix tailTrace_4664788
  have hstable : (prefixWord ++ tailWord_4664788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664788).length < 2 ^ (prefixWord ++ tailWord_4664788).sum := by decide
  have hdescent : baseEnd_4664788 < baseStart_4664788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664807 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 2, 5]
def baseStart_4664807 : Nat := 118140960795 + 4664807 * 2 ^ 59
def prefixEnd_4664807 : Nat := 4983230072969 + 3 ^ 40 * 4664807 * 2
def baseEnd_4664807 : Nat := 798429383819345218286483

theorem tailTrace_4664807 : CollatzResearch.WordTrace tailWord_4664807 prefixEnd_4664807 798429383819345218286483 := by
  unfold tailWord_4664807
  simp only [CollatzResearch.WordTrace]
  refine ⟨170139488811208399453328675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113426325874138932968885783 170139488811208399453328675)
  ·
    refine ⟨255209233216812599179993013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170139488811208399453328675 255209233216812599179993013)
    ·
      refine ⟨23925865614076181173124345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 255209233216812599179993013 23925865614076181173124345)
      ·
        refine ⟨17944399210557135879843259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23925865614076181173124345 17944399210557135879843259)
        ·
          refine ⟨26916598815835703819764889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17944399210557135879843259 26916598815835703819764889)
          ·
            refine ⟨20187449111876777864823667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26916598815835703819764889 20187449111876777864823667)
            ·
              refine ⟨30281173667815166797235501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20187449111876777864823667 30281173667815166797235501)
              ·
                refine ⟨11355440125430687548963313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30281173667815166797235501 11355440125430687548963313)
                ·
                  refine ⟨8516580094073015661722485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11355440125430687548963313 8516580094073015661722485)
                  ·
                    refine ⟨798429383819345218286483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8516580094073015661722485 798429383819345218286483)
                    ·
                      rfl

theorem cell23_4664807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_4664807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664807 prefixEnd_4664807 := by exact prefixLift 4664807
  have htrace : WordTrace (prefixWord ++ tailWord_4664807) baseStart_4664807 baseEnd_4664807 := by
    simpa [prefixWord, tailWord_4664807, baseEnd_4664807] using wordTrace_append hprefix tailTrace_4664807
  have hstable : (prefixWord ++ tailWord_4664807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664807).length < 2 ^ (prefixWord ++ tailWord_4664807).sum := by decide
  have hdescent : baseEnd_4664807 < baseStart_4664807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664827 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 4, 4, 2]
def baseStart_4664827 : Nat := 118140960795 + 4664827 * 2 ^ 59
def prefixEnd_4664827 : Nat := 4983230072969 + 3 ^ 40 * 4664827 * 2
def baseEnd_4664827 : Nat := 2395298421071125576609357

theorem tailTrace_4664827 : CollatzResearch.WordTrace tailWord_4664827 prefixEnd_4664827 2395298421071125576609357 := by
  unfold tailWord_4664827
  simp only [CollatzResearch.WordTrace]
  refine ⟨170140218271135942869056735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113426812180757295246037823 170140218271135942869056735)
  ·
    refine ⟨255210327406703914303585103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170140218271135942869056735 255210327406703914303585103)
    ·
      refine ⟨382815491110055871455377655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255210327406703914303585103 382815491110055871455377655)
      ·
        refine ⟨574223236665083807183066483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382815491110055871455377655 574223236665083807183066483)
        ·
          refine ⟨861334854997625710774599725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574223236665083807183066483 861334854997625710774599725)
          ·
            refine ⟨323000570624109641540474897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 861334854997625710774599725 323000570624109641540474897)
            ·
              refine ⟨242250427968082231155356173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323000570624109641540474897 242250427968082231155356173)
              ·
                refine ⟨90843910488030836683258565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242250427968082231155356173 90843910488030836683258565)
                ·
                  refine ⟨17033233216505781878110981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90843910488030836683258565 17033233216505781878110981)
                  ·
                    refine ⟨3193731228094834102145809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17033233216505781878110981 3193731228094834102145809)
                    ·
                      refine ⟨2395298421071125576609357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193731228094834102145809 2395298421071125576609357)
                      ·
                        rfl

theorem cell23_4664827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 4, 2].length) (baseStart_4664827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664827 prefixEnd_4664827 := by exact prefixLift 4664827
  have htrace : WordTrace (prefixWord ++ tailWord_4664827) baseStart_4664827 baseEnd_4664827 := by
    simpa [prefixWord, tailWord_4664827, baseEnd_4664827] using wordTrace_append hprefix tailTrace_4664827
  have hstable : (prefixWord ++ tailWord_4664827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664827).length < 2 ^ (prefixWord ++ tailWord_4664827).sum := by decide
  have hdescent : baseEnd_4664827 < baseStart_4664827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664834 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4664834 : Nat := 118140960795 + 4664834 * 2 ^ 59
def prefixEnd_4664834 : Nat := 4983230072969 + 3 ^ 40 * 4664834 * 2
def baseEnd_4664834 : Nat := 2395302015435707049221825

theorem tailTrace_4664834 : CollatzResearch.WordTrace tailWord_4664834 prefixEnd_4664834 2395302015435707049221825 := by
  unfold tailWord_4664834
  simp only [CollatzResearch.WordTrace]
  refine ⟨42535118395527645766140389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113426982388073722043041037 42535118395527645766140389)
  ·
    refine ⟨7975334699161433581151323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42535118395527645766140389 7975334699161433581151323)
    ·
      refine ⟨11963002048742150371726985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7975334699161433581151323 11963002048742150371726985)
      ·
        refine ⟨8972251536556612778795239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11963002048742150371726985 8972251536556612778795239)
        ·
          refine ⟨13458377304834919168192859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8972251536556612778795239 13458377304834919168192859)
          ·
            refine ⟨20187565957252378752289289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13458377304834919168192859 20187565957252378752289289)
            ·
              refine ⟨15140674467939284064216967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20187565957252378752289289 15140674467939284064216967)
              ·
                refine ⟨22711011701908926096325451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15140674467939284064216967 22711011701908926096325451)
                ·
                  refine ⟨34066517552863389144488177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22711011701908926096325451 34066517552863389144488177)
                  ·
                    refine ⟨25549888164647541858366133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34066517552863389144488177 25549888164647541858366133)
                    ·
                      refine ⟨2395302015435707049221825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25549888164647541858366133 2395302015435707049221825)
                      ·
                        rfl

theorem cell23_4664834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4664834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664834 prefixEnd_4664834 := by exact prefixLift 4664834
  have htrace : WordTrace (prefixWord ++ tailWord_4664834) baseStart_4664834 baseEnd_4664834 := by
    simpa [prefixWord, tailWord_4664834, baseEnd_4664834] using wordTrace_append hprefix tailTrace_4664834
  have hstable : (prefixWord ++ tailWord_4664834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664834).length < 2 ^ (prefixWord ++ tailWord_4664834).sum := by decide
  have hdescent : baseEnd_4664834 < baseStart_4664834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664837 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 3, 4]
def baseStart_4664837 : Nat := 118140960795 + 4664837 * 2 ^ 59
def prefixEnd_4664837 : Nat := 4983230072969 + 3 ^ 40 * 4664837 * 2
def baseEnd_4664837 : Nat := 798434518625890179161437

theorem tailTrace_4664837 : CollatzResearch.WordTrace tailWord_4664837 prefixEnd_4664837 798434518625890179161437 := by
  unfold tailWord_4664837
  simp only [CollatzResearch.WordTrace]
  refine ⟨170140583001099714576920765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113427055334066476384613843 170140583001099714576920765)
  ·
    refine ⟨63802718625412392966345287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170140583001099714576920765 63802718625412392966345287)
    ·
      refine ⟨95704077938118589449517931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63802718625412392966345287 95704077938118589449517931)
      ·
        refine ⟨143556116907177884174276897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95704077938118589449517931 143556116907177884174276897)
        ·
          refine ⟨107667087680383413130707673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143556116907177884174276897 107667087680383413130707673)
          ·
            refine ⟨80750315760287559848030755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107667087680383413130707673 80750315760287559848030755)
            ·
              refine ⟨121125473640431339772046133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80750315760287559848030755 121125473640431339772046133)
              ·
                refine ⟨11355513153790438103629325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121125473640431339772046133 11355513153790438103629325)
                ·
                  refine ⟨4258317432671414288860997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11355513153790438103629325 4258317432671414288860997)
                  ·
                    refine ⟨798434518625890179161437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4258317432671414288860997 798434518625890179161437)
                    ·
                      rfl

theorem cell23_4664837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_4664837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664837 prefixEnd_4664837 := by exact prefixLift 4664837
  have htrace : WordTrace (prefixWord ++ tailWord_4664837) baseStart_4664837 baseEnd_4664837 := by
    simpa [prefixWord, tailWord_4664837, baseEnd_4664837] using wordTrace_append hprefix tailTrace_4664837
  have hstable : (prefixWord ++ tailWord_4664837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664837).length < 2 ^ (prefixWord ++ tailWord_4664837).sum := by decide
  have hdescent : baseEnd_4664837 < baseStart_4664837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664864 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4664864 : Nat := 118140960795 + 4664864 * 2 ^ 59
def prefixEnd_4664864 : Nat := 4983230072969 + 3 ^ 40 * 4664864 * 2
def baseEnd_4664864 : Nat := 2395317419855341931846687

theorem tailTrace_4664864 : CollatzResearch.WordTrace tailWord_4664864 prefixEnd_4664864 2395317419855341931846687 := by
  unfold tailWord_4664864
  simp only [CollatzResearch.WordTrace]
  refine ⟨85070783886000949094076823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113427711848001265458769097 85070783886000949094076823)
  ·
    refine ⟨127606175829001423641115235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85070783886000949094076823 127606175829001423641115235)
    ·
      refine ⟨191409263743502135461672853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127606175829001423641115235 191409263743502135461672853)
      ·
        refine ⟨8972309237976662599765915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 191409263743502135461672853 8972309237976662599765915)
        ·
          refine ⟨13458463856964993899648873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8972309237976662599765915 13458463856964993899648873)
          ·
            refine ⟨10093847892723745424736655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13458463856964993899648873 10093847892723745424736655)
            ·
              refine ⟨15140771839085618137104983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10093847892723745424736655 15140771839085618137104983)
              ·
                refine ⟨22711157758628427205657475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15140771839085618137104983 22711157758628427205657475)
                ·
                  refine ⟨34066736637942640808486213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22711157758628427205657475 34066736637942640808486213)
                  ·
                    refine ⟨6387513119614245151591165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34066736637942640808486213 6387513119614245151591165)
                    ·
                      refine ⟨2395317419855341931846687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6387513119614245151591165 2395317419855341931846687)
                      ·
                        rfl

theorem cell23_4664864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4664864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664864 prefixEnd_4664864 := by exact prefixLift 4664864
  have htrace : WordTrace (prefixWord ++ tailWord_4664864) baseStart_4664864 baseEnd_4664864 := by
    simpa [prefixWord, tailWord_4664864, baseEnd_4664864] using wordTrace_append hprefix tailTrace_4664864
  have hstable : (prefixWord ++ tailWord_4664864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664864).length < 2 ^ (prefixWord ++ tailWord_4664864).sum := by decide
  have hdescent : baseEnd_4664864 < baseStart_4664864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664914 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_4664914 : Nat := 118140960795 + 4664914 * 2 ^ 59
def prefixEnd_4664914 : Nat := 4983230072969 + 3 ^ 40 * 4664914 * 2
def baseEnd_4664914 : Nat := 798447697962688912073819

theorem tailTrace_4664914 : CollatzResearch.WordTrace tailWord_4664914 prefixEnd_4664914 798447697962688912073819 := by
  unfold tailWord_4664914
  simp only [CollatzResearch.WordTrace]
  refine ⟨42535847855455189181868449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113428927614547171151649197 42535847855455189181868449)
  ·
    refine ⟨31901885891591391886401337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42535847855455189181868449 31901885891591391886401337)
    ·
      refine ⟨23926414418693543914801003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31901885891591391886401337 23926414418693543914801003)
      ·
        refine ⟨35889621628040315872201505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23926414418693543914801003 35889621628040315872201505)
        ·
          refine ⟨26917216221030236904151129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35889621628040315872201505 26917216221030236904151129)
          ·
            refine ⟨20187912165772677678113347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26917216221030236904151129 20187912165772677678113347)
            ·
              refine ⟨30281868248659016517170021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20187912165772677678113347 30281868248659016517170021)
              ·
                refine ⟨5677850296623565596969379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30281868248659016517170021 5677850296623565596969379)
                ·
                  refine ⟨8516775444935348395454069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5677850296623565596969379 8516775444935348395454069)
                  ·
                    refine ⟨798447697962688912073819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8516775444935348395454069 798447697962688912073819)
                    ·
                      rfl

theorem cell23_4664914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_4664914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664914 prefixEnd_4664914 := by exact prefixLift 4664914
  have htrace : WordTrace (prefixWord ++ tailWord_4664914) baseStart_4664914 baseEnd_4664914 := by
    simpa [prefixWord, tailWord_4664914, baseEnd_4664914] using wordTrace_append hprefix tailTrace_4664914
  have hstable : (prefixWord ++ tailWord_4664914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664914).length < 2 ^ (prefixWord ++ tailWord_4664914).sum := by decide
  have hdescent : baseEnd_4664914 < baseStart_4664914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664937 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 5]
def baseStart_4664937 : Nat := 118140960795 + 4664937 * 2 ^ 59
def prefixEnd_4664937 : Nat := 4983230072969 + 3 ^ 40 * 4664937 * 2
def baseEnd_4664937 : Nat := 2395354903943120146233851

theorem tailTrace_4664937 : CollatzResearch.WordTrace tailWord_4664937 prefixEnd_4664937 2395354903943120146233851 := by
  unfold tailWord_4664937
  simp only [CollatzResearch.WordTrace]
  refine ⟨170144230300737431655561065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113429486867158287770374043 170144230300737431655561065)
  ·
    refine ⟨127608172725553073741670799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170144230300737431655561065 127608172725553073741670799)
    ·
      refine ⟨191412259088329610612506199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127608172725553073741670799 191412259088329610612506199)
      ·
        refine ⟨287118388632494415918759299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191412259088329610612506199 287118388632494415918759299)
        ·
          refine ⟨430677582948741623878138949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287118388632494415918759299 430677582948741623878138949)
          ·
            refine ⟨80752046802889054477151053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 430677582948741623878138949 80752046802889054477151053)
            ·
              refine ⟨30282017551083395428931645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80752046802889054477151053 30282017551083395428931645)
              ·
                refine ⟨11355756581656273285849367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30282017551083395428931645 11355756581656273285849367)
                ·
                  refine ⟨17033634872484409928774051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11355756581656273285849367 17033634872484409928774051)
                  ·
                    refine ⟨25550452308726614893161077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17033634872484409928774051 25550452308726614893161077)
                    ·
                      refine ⟨2395354903943120146233851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25550452308726614893161077 2395354903943120146233851)
                      ·
                        rfl

theorem cell23_4664937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_4664937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664937 prefixEnd_4664937 := by exact prefixLift 4664937
  have htrace : WordTrace (prefixWord ++ tailWord_4664937) baseStart_4664937 baseEnd_4664937 := by
    simpa [prefixWord, tailWord_4664937, baseEnd_4664937] using wordTrace_append hprefix tailTrace_4664937
  have hstable : (prefixWord ++ tailWord_4664937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664937).length < 2 ^ (prefixWord ++ tailWord_4664937).sum := by decide
  have hdescent : baseEnd_4664937 < baseStart_4664937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664944 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 4, 4]
def baseStart_4664944 : Nat := 118140960795 + 4664944 * 2 ^ 59
def prefixEnd_4664944 : Nat := 4983230072969 + 3 ^ 40 * 4664944 * 2
def baseEnd_4664944 : Nat := 798452832769233872948773

theorem tailTrace_4664944 : CollatzResearch.WordTrace tailWord_4664944 prefixEnd_4664944 798452832769233872948773 := by
  unfold tailWord_4664944
  simp only [CollatzResearch.WordTrace]
  refine ⟨85072242805856035925532943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113429657074474714567377257 85072242805856035925532943)
  ·
    refine ⟨127608364208784053888299415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85072242805856035925532943 127608364208784053888299415)
    ·
      refine ⟨191412546313176080832449123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127608364208784053888299415 191412546313176080832449123)
      ·
        refine ⟨287118819469764121248673685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191412546313176080832449123 287118819469764121248673685)
        ·
          refine ⟨13458694662645193183531579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 287118819469764121248673685 13458694662645193183531579)
          ·
            refine ⟨20188041993967789775297369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13458694662645193183531579 20188041993967789775297369)
            ·
              refine ⟨15141031495475842331473027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20188041993967789775297369 15141031495475842331473027)
              ·
                refine ⟨22711547243213763497209541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15141031495475842331473027 22711547243213763497209541)
                ·
                  refine ⟨4258415108102580655726789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22711547243213763497209541 4258415108102580655726789)
                  ·
                    refine ⟨798452832769233872948773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4258415108102580655726789 798452832769233872948773)
                    ·
                      rfl

theorem cell23_4664944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4, 4].length) (baseStart_4664944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664944 prefixEnd_4664944 := by exact prefixLift 4664944
  have htrace : WordTrace (prefixWord ++ tailWord_4664944) baseStart_4664944 baseEnd_4664944 := by
    simpa [prefixWord, tailWord_4664944, baseEnd_4664944] using wordTrace_append hprefix tailTrace_4664944
  have hstable : (prefixWord ++ tailWord_4664944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664944).length < 2 ^ (prefixWord ++ tailWord_4664944).sum := by decide
  have hdescent : baseEnd_4664944 < baseStart_4664944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664957 : List Nat := [1, 4, 1, 1, 4, 1, 1, 10]
def baseStart_4664957 : Nat := 118140960795 + 4664957 * 2 ^ 59
def prefixEnd_4664957 : Nat := 4983230072969 + 3 ^ 40 * 4664957 * 2
def baseEnd_4664957 : Nat := 88717228650230002517917

theorem tailTrace_4664957 : CollatzResearch.WordTrace tailWord_4664957 prefixEnd_4664957 88717228650230002517917 := by
  unfold tailWord_4664957
  simp only [CollatzResearch.WordTrace]
  refine ⟨170144959760664975071289125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113429973173776650047526083 170144959760664975071289125)
  ·
    refine ⟨31902179955124682825866711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170144959760664975071289125 31902179955124682825866711)
    ·
      refine ⟨47853269932687024238800067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31902179955124682825866711 47853269932687024238800067)
      ·
        refine ⟨71779904899030536358200101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47853269932687024238800067 71779904899030536358200101)
        ·
          refine ⟨13458732168568225567162519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71779904899030536358200101 13458732168568225567162519)
          ·
            refine ⟨20188098252852338350743779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13458732168568225567162519 20188098252852338350743779)
            ·
              refine ⟨30282147379278507526115669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20188098252852338350743779 30282147379278507526115669)
              ·
                refine ⟨88717228650230002517917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30282147379278507526115669 88717228650230002517917)
                ·
                  rfl

theorem cell23_4664957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 10].length) (baseStart_4664957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664957 prefixEnd_4664957 := by exact prefixLift 4664957
  have htrace : WordTrace (prefixWord ++ tailWord_4664957) baseStart_4664957 baseEnd_4664957 := by
    simpa [prefixWord, tailWord_4664957, baseEnd_4664957] using wordTrace_append hprefix tailTrace_4664957
  have hstable : (prefixWord ++ tailWord_4664957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664957).length < 2 ^ (prefixWord ++ tailWord_4664957).sum := by decide
  have hdescent : baseEnd_4664957 < baseStart_4664957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664961 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 2, 4]
def baseStart_4664961 : Nat := 118140960795 + 4664961 * 2 ^ 59
def prefixEnd_4664961 : Nat := 4983230072969 + 3 ^ 40 * 4664961 * 2
def baseEnd_4664961 : Nat := 798455742492942684111247

theorem tailTrace_4664961 : CollatzResearch.WordTrace tailWord_4664961 prefixEnd_4664961 798455742492942684111247 := by
  unfold tailWord_4664961
  simp only [CollatzResearch.WordTrace]
  refine ⟨170145105652650483754434737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113430070435100322502956491 170145105652650483754434737)
  ·
    refine ⟨127608829239487862815826053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170145105652650483754434737 127608829239487862815826053)
    ·
      refine ⟨23926655482403974277967385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127608829239487862815826053 23926655482403974277967385)
      ·
        refine ⟨17944991611802980708475539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23926655482403974277967385 17944991611802980708475539)
        ·
          refine ⟨26917487417704471062713309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17944991611802980708475539 26917487417704471062713309)
          ·
            refine ⟨10094057781639176648517491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26917487417704471062713309 10094057781639176648517491)
            ·
              refine ⟨15141086672458764972776237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10094057781639176648517491 15141086672458764972776237)
              ·
                refine ⟨5677907502172036864791089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15141086672458764972776237 5677907502172036864791089)
                ·
                  refine ⟨4258430626629027648593317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5677907502172036864791089 4258430626629027648593317)
                  ·
                    refine ⟨798455742492942684111247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4258430626629027648593317 798455742492942684111247)
                    ·
                      rfl

theorem cell23_4664961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_4664961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664961 prefixEnd_4664961 := by exact prefixLift 4664961
  have htrace : WordTrace (prefixWord ++ tailWord_4664961) baseStart_4664961 baseEnd_4664961 := by
    simpa [prefixWord, tailWord_4664961, baseEnd_4664961] using wordTrace_append hprefix tailTrace_4664961
  have hstable : (prefixWord ++ tailWord_4664961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664961).length < 2 ^ (prefixWord ++ tailWord_4664961).sum := by decide
  have hdescent : baseEnd_4664961 < baseStart_4664961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664984 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 3, 3, 3]
def baseStart_4664984 : Nat := 118140960795 + 4664984 * 2 ^ 59
def prefixEnd_4664984 : Nat := 4983230072969 + 3 ^ 40 * 4664984 * 2
def baseEnd_4664984 : Nat := 2395379037533881462346135

theorem tailTrace_4664984 : CollatzResearch.WordTrace tailWord_4664984 prefixEnd_4664984 2395379037533881462346135 := by
  unfold tailWord_4664984
  simp only [CollatzResearch.WordTrace]
  refine ⟨85072972265783579341261003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113430629687711439121681337 85072972265783579341261003)
  ·
    refine ⟨127609458398675369011891505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85072972265783579341261003 127609458398675369011891505)
    ·
      refine ⟨95707093799006526758918629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127609458398675369011891505 95707093799006526758918629)
      ·
        refine ⟨17945080087313723767297243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95707093799006526758918629 17945080087313723767297243)
        ·
          refine ⟨26917620130970585650945865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17945080087313723767297243 26917620130970585650945865)
          ·
            refine ⟨20188215098227939238209399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26917620130970585650945865 20188215098227939238209399)
            ·
              refine ⟨30282322647341908857314099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20188215098227939238209399 30282322647341908857314099)
              ·
                refine ⟨45423483971012863285971149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30282322647341908857314099 45423483971012863285971149)
                ·
                  refine ⟨17033806489129823732239181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45423483971012863285971149 17033806489129823732239181)
                  ·
                    refine ⟨6387677433423683899589693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17033806489129823732239181 6387677433423683899589693)
                    ·
                      refine ⟨2395379037533881462346135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6387677433423683899589693 2395379037533881462346135)
                      ·
                        rfl

theorem cell23_4664984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_4664984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664984 prefixEnd_4664984 := by exact prefixLift 4664984
  have htrace : WordTrace (prefixWord ++ tailWord_4664984) baseStart_4664984 baseEnd_4664984 := by
    simpa [prefixWord, tailWord_4664984, baseEnd_4664984] using wordTrace_append hprefix tailTrace_4664984
  have hstable : (prefixWord ++ tailWord_4664984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664984).length < 2 ^ (prefixWord ++ tailWord_4664984).sum := by decide
  have hdescent : baseEnd_4664984 < baseStart_4664984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664988 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_4664988 : Nat := 118140960795 + 4664988 * 2 ^ 59
def prefixEnd_4664988 : Nat := 4983230072969 + 3 ^ 40 * 4664988 * 2
def baseEnd_4664988 : Nat := 2395381091456499446696117

theorem tailTrace_4664988 : CollatzResearch.WordTrace tailWord_4664988 prefixEnd_4664988 2395381091456499446696117 := by
  unfold tailWord_4664988
  simp only [CollatzResearch.WordTrace]
  refine ⟨85073045211776333682833809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113430726949035111577111745 85073045211776333682833809)
  ·
    refine ⟨63804783908832250262125357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85073045211776333682833809 63804783908832250262125357)
    ·
      refine ⟨23926793965812093848297009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63804783908832250262125357 23926793965812093848297009)
      ·
        refine ⟨17945095474359070386222757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23926793965812093848297009 17945095474359070386222757)
        ·
          refine ⟨3364705401442325697416767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17945095474359070386222757 3364705401442325697416767)
          ·
            refine ⟨5047058102163488546125151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3364705401442325697416767 5047058102163488546125151)
            ·
              refine ⟨7570587153245232819187727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5047058102163488546125151 7570587153245232819187727)
              ·
                refine ⟨11355880729867849228781591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7570587153245232819187727 11355880729867849228781591)
                ·
                  refine ⟨17033821094801773843172387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11355880729867849228781591 17033821094801773843172387)
                  ·
                    refine ⟨25550731642202660764758581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17033821094801773843172387 25550731642202660764758581)
                    ·
                      refine ⟨2395381091456499446696117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25550731642202660764758581 2395381091456499446696117)
                      ·
                        rfl

theorem cell23_4664988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_4664988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664988 prefixEnd_4664988 := by exact prefixLift 4664988
  have htrace : WordTrace (prefixWord ++ tailWord_4664988) baseStart_4664988 baseEnd_4664988 := by
    simpa [prefixWord, tailWord_4664988, baseEnd_4664988] using wordTrace_append hprefix tailTrace_4664988
  have hstable : (prefixWord ++ tailWord_4664988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664988).length < 2 ^ (prefixWord ++ tailWord_4664988).sum := by decide
  have hdescent : baseEnd_4664988 < baseStart_4664988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4664997 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_4664997 : Nat := 118140960795 + 4664997 * 2 ^ 59
def prefixEnd_4664997 : Nat := 4983230072969 + 3 ^ 40 * 4664997 * 2
def baseEnd_4664997 : Nat := 2395385712782389911483575

theorem tailTrace_4664997 : CollatzResearch.WordTrace tailWord_4664997 prefixEnd_4664997 2395385712782389911483575 := by
  unfold tailWord_4664997
  simp only [CollatzResearch.WordTrace]
  refine ⟨170146418680520061902745245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113430945787013374601830163 170146418680520061902745245)
  ·
    refine ⟨63804907005195023213529467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170146418680520061902745245 63804907005195023213529467)
    ·
      refine ⟨95707360507792534820294201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63804907005195023213529467 95707360507792534820294201)
      ·
        refine ⟨71780520380844401115220651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95707360507792534820294201 71780520380844401115220651)
        ·
          refine ⟨107670780571266601672830977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71780520380844401115220651 107670780571266601672830977)
          ·
            refine ⟨80753085428449951254623233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107670780571266601672830977 80753085428449951254623233)
            ·
              refine ⟨60564814071337463440967425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80753085428449951254623233 60564814071337463440967425)
              ·
                refine ⟨45423610553503097580725569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60564814071337463440967425 45423610553503097580725569)
                ·
                  refine ⟨34067707915127323185544177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45423610553503097580725569 34067707915127323185544177)
                  ·
                    refine ⟨25550780936345492389158133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34067707915127323185544177 25550780936345492389158133)
                    ·
                      refine ⟨2395385712782389911483575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25550780936345492389158133 2395385712782389911483575)
                      ·
                        rfl

theorem cell23_4664997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_4664997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4664997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4664997 prefixEnd_4664997 := by exact prefixLift 4664997
  have htrace : WordTrace (prefixWord ++ tailWord_4664997) baseStart_4664997 baseEnd_4664997 := by
    simpa [prefixWord, tailWord_4664997, baseEnd_4664997] using wordTrace_append hprefix tailTrace_4664997
  have hstable : (prefixWord ++ tailWord_4664997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4664997).length < 2 ^ (prefixWord ++ tailWord_4664997).sum := by decide
  have hdescent : baseEnd_4664997 < baseStart_4664997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4664997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665007 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 4]
def baseStart_4665007 : Nat := 118140960795 + 4665007 * 2 ^ 59
def prefixEnd_4665007 : Nat := 4983230072969 + 3 ^ 40 * 4665007 * 2
def baseEnd_4665007 : Nat := 2395390847588934872358529

theorem tailTrace_4665007 : CollatzResearch.WordTrace tailWord_4665007 prefixEnd_4665007 2395390847588934872358529 := by
  unfold tailWord_4665007
  simp only [CollatzResearch.WordTrace]
  refine ⟨170146783410483833610609275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113431188940322555740406183 170146783410483833610609275)
  ·
    refine ⟨255220175115725750415913913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170146783410483833610609275 255220175115725750415913913)
    ·
      refine ⟨191415131336794312811935435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255220175115725750415913913 191415131336794312811935435)
      ·
        refine ⟨287122697005191469217903153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191415131336794312811935435 287122697005191469217903153)
        ·
          refine ⟨215342022753893601913427365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287122697005191469217903153 215342022753893601913427365)
          ·
            refine ⟨40376629266355050358767631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215342022753893601913427365 40376629266355050358767631)
            ·
              refine ⟨60564943899532575538151447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40376629266355050358767631 60564943899532575538151447)
              ·
                refine ⟨90847415849298863307227171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60564943899532575538151447 90847415849298863307227171)
                ·
                  refine ⟨136271123773948294960840757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90847415849298863307227171 136271123773948294960840757)
                  ·
                    refine ⟨12775417853807652652578821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 136271123773948294960840757 12775417853807652652578821)
                    ·
                      refine ⟨2395390847588934872358529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12775417853807652652578821 2395390847588934872358529)
                      ·
                        rfl

theorem cell23_4665007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_4665007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665007 prefixEnd_4665007 := by exact prefixLift 4665007
  have htrace : WordTrace (prefixWord ++ tailWord_4665007) baseStart_4665007 baseEnd_4665007 := by
    simpa [prefixWord, tailWord_4665007, baseEnd_4665007] using wordTrace_append hprefix tailTrace_4665007
  have hstable : (prefixWord ++ tailWord_4665007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665007).length < 2 ^ (prefixWord ++ tailWord_4665007).sum := by decide
  have hdescent : baseEnd_4665007 < baseStart_4665007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665017 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 1, 8]
def baseStart_4665017 : Nat := 118140960795 + 4665017 * 2 ^ 59
def prefixEnd_4665017 : Nat := 4983230072969 + 3 ^ 40 * 4665017 * 2
def baseEnd_4665017 : Nat := 798465327465159944411161

theorem tailTrace_4665017 : CollatzResearch.WordTrace tailWord_4665017 prefixEnd_4665017 798465327465159944411161 := by
  unfold tailWord_4665017
  simp only [CollatzResearch.WordTrace]
  refine ⟨170147148140447605318473305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113431432093631736878982203 170147148140447605318473305)
  ·
    refine ⟨127610361105335703988854979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170147148140447605318473305 127610361105335703988854979)
    ·
      refine ⟨191415541658003555983282469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127610361105335703988854979 191415541658003555983282469)
      ·
        refine ⟨35890414060875666746865463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191415541658003555983282469 35890414060875666746865463)
        ·
          refine ⟨53835621091313500120298195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35890414060875666746865463 53835621091313500120298195)
          ·
            refine ⟨80753431636970250180447293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53835621091313500120298195 80753431636970250180447293)
            ·
              refine ⟨30282536863863843817667735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80753431636970250180447293 30282536863863843817667735)
              ·
                refine ⟨45423805295795765726501603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30282536863863843817667735 45423805295795765726501603)
                ·
                  refine ⟨68135707943693648589752405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45423805295795765726501603 68135707943693648589752405)
                  ·
                    refine ⟨798465327465159944411161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68135707943693648589752405 798465327465159944411161)
                    ·
                      rfl

theorem cell23_4665017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_4665017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665017 prefixEnd_4665017 := by exact prefixLift 4665017
  have htrace : WordTrace (prefixWord ++ tailWord_4665017) baseStart_4665017 baseEnd_4665017 := by
    simpa [prefixWord, tailWord_4665017, baseEnd_4665017] using wordTrace_append hprefix tailTrace_4665017
  have hstable : (prefixWord ++ tailWord_4665017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665017).length < 2 ^ (prefixWord ++ tailWord_4665017).sum := by decide
  have hdescent : baseEnd_4665017 < baseStart_4665017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665028 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_4665028 : Nat := 118140960795 + 4665028 * 2 ^ 59
def prefixEnd_4665028 : Nat := 4983230072969 + 3 ^ 40 * 4665028 * 2
def baseEnd_4665028 : Nat := 2395401630682679290195933

theorem tailTrace_4665028 : CollatzResearch.WordTrace tailWord_4665028 prefixEnd_4665028 2395401630682679290195933 := by
  unfold tailWord_4665028
  simp only [CollatzResearch.WordTrace]
  refine ⟨85073774671703877098561869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113431699562271836131415825 85073774671703877098561869)
  ·
    refine ⟨31902665501888953911960701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85073774671703877098561869 31902665501888953911960701)
    ·
      refine ⟨11963499563208357716985263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31902665501888953911960701 11963499563208357716985263)
      ·
        refine ⟨17945249344812536575477895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11963499563208357716985263 17945249344812536575477895)
        ·
          refine ⟨26917874017218804863216843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17945249344812536575477895 26917874017218804863216843)
          ·
            refine ⟨40376811025828207294825265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26917874017218804863216843 40376811025828207294825265)
            ·
              refine ⟨30282608269371155471118949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40376811025828207294825265 30282608269371155471118949)
              ·
                refine ⟨5677989050507091650834803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30282608269371155471118949 5677989050507091650834803)
                ·
                  refine ⟨8516983575760637476252205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5677989050507091650834803 8516983575760637476252205)
                  ·
                    refine ⟨3193868840910239053594577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8516983575760637476252205 3193868840910239053594577)
                    ·
                      refine ⟨2395401630682679290195933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193868840910239053594577 2395401630682679290195933)
                      ·
                        rfl

theorem cell23_4665028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_4665028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665028 prefixEnd_4665028 := by exact prefixLift 4665028
  have htrace : WordTrace (prefixWord ++ tailWord_4665028) baseStart_4665028 baseEnd_4665028 := by
    simpa [prefixWord, tailWord_4665028, baseEnd_4665028] using wordTrace_append hprefix tailTrace_4665028
  have hstable : (prefixWord ++ tailWord_4665028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665028).length < 2 ^ (prefixWord ++ tailWord_4665028).sum := by decide
  have hdescent : baseEnd_4665028 < baseStart_4665028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665041 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 1, 4, 2]
def baseStart_4665041 : Nat := 118140960795 + 4665041 * 2 ^ 59
def prefixEnd_4665041 : Nat := 4983230072969 + 3 ^ 40 * 4665041 * 2
def baseEnd_4665041 : Nat := 2395408305931187739333373

theorem tailTrace_4665041 : CollatzResearch.WordTrace tailWord_4665041 prefixEnd_4665041 2395408305931187739333373 := by
  unfold tailWord_4665041
  simp only [CollatzResearch.WordTrace]
  refine ⟨170148023492360657417346977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113432015661573771611564651 170148023492360657417346977)
  ·
    refine ⟨127611017619270493063010233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170148023492360657417346977 127611017619270493063010233)
    ·
      refine ⟨95708263214452869797257675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127611017619270493063010233 95708263214452869797257675)
      ·
        refine ⟨143562394821679304695886513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95708263214452869797257675 143562394821679304695886513)
        ·
          refine ⟨107671796116259478521914885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143562394821679304695886513 107671796116259478521914885)
          ·
            refine ⟨20188461771798652222859041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107671796116259478521914885 20188461771798652222859041)
            ·
              refine ⟨15141346328848989167144281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20188461771798652222859041 15141346328848989167144281)
              ·
                refine ⟨11356009746636741875358211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15141346328848989167144281 11356009746636741875358211)
                ·
                  refine ⟨17034014619955112813037317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11356009746636741875358211 17034014619955112813037317)
                  ·
                    refine ⟨3193877741241583652444497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17034014619955112813037317 3193877741241583652444497)
                    ·
                      refine ⟨2395408305931187739333373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3193877741241583652444497 2395408305931187739333373)
                      ·
                        rfl

theorem cell23_4665041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 4, 2].length) (baseStart_4665041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665041 prefixEnd_4665041 := by exact prefixLift 4665041
  have htrace : WordTrace (prefixWord ++ tailWord_4665041) baseStart_4665041 baseEnd_4665041 := by
    simpa [prefixWord, tailWord_4665041, baseEnd_4665041] using wordTrace_append hprefix tailTrace_4665041
  have hstable : (prefixWord ++ tailWord_4665041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665041).length < 2 ^ (prefixWord ++ tailWord_4665041).sum := by decide
  have hdescent : baseEnd_4665041 < baseStart_4665041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665047 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 9]
def baseStart_4665047 : Nat := 118140960795 + 4665047 * 2 ^ 59
def prefixEnd_4665047 : Nat := 4983230072969 + 3 ^ 40 * 4665047 * 2
def baseEnd_4665047 : Nat := 266156820757234968428705

theorem tailTrace_4665047 : CollatzResearch.WordTrace tailWord_4665047 prefixEnd_4665047 266156820757234968428705 := by
  unfold tailWord_4665047
  simp only [CollatzResearch.WordTrace]
  refine ⟨170148242330338920442065395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113432161553559280294710263 170148242330338920442065395)
  ·
    refine ⟨255222363495508380663098093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170148242330338920442065395 255222363495508380663098093)
    ·
      refine ⟨95708386310815642748661785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255222363495508380663098093 95708386310815642748661785)
      ·
        refine ⟨71781289733111732061496339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95708386310815642748661785 71781289733111732061496339)
        ·
          refine ⟨107671934599667598092244509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71781289733111732061496339 107671934599667598092244509)
          ·
            refine ⟨40376975474875349284591691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107671934599667598092244509 40376975474875349284591691)
            ·
              refine ⟨60565463212313023926887537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40376975474875349284591691 60565463212313023926887537)
              ·
                refine ⟨45424097409234767945165653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60565463212313023926887537 45424097409234767945165653)
                ·
                  refine ⟨266156820757234968428705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45424097409234767945165653 266156820757234968428705)
                  ·
                    rfl

theorem cell23_4665047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 9].length) (baseStart_4665047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665047 prefixEnd_4665047 := by exact prefixLift 4665047
  have htrace : WordTrace (prefixWord ++ tailWord_4665047) baseStart_4665047 baseEnd_4665047 := by
    simpa [prefixWord, tailWord_4665047, baseEnd_4665047] using wordTrace_append hprefix tailTrace_4665047
  have hstable : (prefixWord ++ tailWord_4665047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665047).length < 2 ^ (prefixWord ++ tailWord_4665047).sum := by decide
  have hdescent : baseEnd_4665047 < baseStart_4665047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665052 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_4665052 : Nat := 118140960795 + 4665052 * 2 ^ 59
def prefixEnd_4665052 : Nat := 4983230072969 + 3 ^ 40 * 4665052 * 2
def baseEnd_4665052 : Nat := 2395413954218387196295823

theorem tailTrace_4665052 : CollatzResearch.WordTrace tailWord_4665052 prefixEnd_4665052 2395413954218387196295823 := by
  unfold tailWord_4665052
  simp only [CollatzResearch.WordTrace]
  refine ⟨85074212347660403147998705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113432283130213870863998273 85074212347660403147998705)
  ·
    refine ⟨63805659260745302360999029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85074212347660403147998705 63805659260745302360999029)
    ·
      refine ⟨5981780555694872096343659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63805659260745302360999029 5981780555694872096343659)
      ·
        refine ⟨8972670833542308144515489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5981780555694872096343659 8972670833542308144515489)
        ·
          refine ⟨6729503125156731108386617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8972670833542308144515489 6729503125156731108386617)
          ·
            refine ⟨5047127343867548331289963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6729503125156731108386617 5047127343867548331289963)
            ·
              refine ⟨7570691015801322496934945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5047127343867548331289963 7570691015801322496934945)
              ·
                refine ⟨5678018261850991872701209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7570691015801322496934945 5678018261850991872701209)
                ·
                  refine ⟨4258513696388243904525907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5678018261850991872701209 4258513696388243904525907)
                  ·
                    refine ⟨6387770544582365856788861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4258513696388243904525907 6387770544582365856788861)
                    ·
                      refine ⟨2395413954218387196295823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6387770544582365856788861 2395413954218387196295823)
                      ·
                        rfl

theorem cell23_4665052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_4665052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665052 prefixEnd_4665052 := by exact prefixLift 4665052
  have htrace : WordTrace (prefixWord ++ tailWord_4665052) baseStart_4665052 baseEnd_4665052 := by
    simpa [prefixWord, tailWord_4665052, baseEnd_4665052] using wordTrace_append hprefix tailTrace_4665052
  have hstable : (prefixWord ++ tailWord_4665052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665052).length < 2 ^ (prefixWord ++ tailWord_4665052).sum := by decide
  have hdescent : baseEnd_4665052 < baseStart_4665052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665064 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 7]
def baseStart_4665064 : Nat := 118140960795 + 4665064 * 2 ^ 59
def prefixEnd_4665064 : Nat := 4983230072969 + 3 ^ 40 * 4665064 * 2
def baseEnd_4665064 : Nat := 266157790665137905482863

theorem tailTrace_4665064 : CollatzResearch.WordTrace tailWord_4665064 prefixEnd_4665064 266157790665137905482863 := by
  unfold tailWord_4665064
  simp only [CollatzResearch.WordTrace]
  refine ⟨85074431185638666172717123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113432574914184888230289497 85074431185638666172717123)
  ·
    refine ⟨127611646778457999259075685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85074431185638666172717123 127611646778457999259075685)
    ·
      refine ⟨23927183770960874861076691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127611646778457999259075685 23927183770960874861076691)
      ·
        refine ⟨35890775656441312291615037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23927183770960874861076691 35890775656441312291615037)
        ·
          refine ⟨13459040871165492109355639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35890775656441312291615037 13459040871165492109355639)
          ·
            refine ⟨20188561306748238164033459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13459040871165492109355639 20188561306748238164033459)
            ·
              refine ⟨30282841960122357246050189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20188561306748238164033459 30282841960122357246050189)
              ·
                refine ⟨11356065735045883967268821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30282841960122357246050189 11356065735045883967268821)
                ·
                  refine ⟨266157790665137905482863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11356065735045883967268821 266157790665137905482863)
                  ·
                    rfl

theorem cell23_4665064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 7].length) (baseStart_4665064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665064 prefixEnd_4665064 := by exact prefixLift 4665064
  have htrace : WordTrace (prefixWord ++ tailWord_4665064) baseStart_4665064 baseEnd_4665064 := by
    simpa [prefixWord, tailWord_4665064, baseEnd_4665064] using wordTrace_append hprefix tailTrace_4665064
  have hstable : (prefixWord ++ tailWord_4665064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665064).length < 2 ^ (prefixWord ++ tailWord_4665064).sum := by decide
  have hdescent : baseEnd_4665064 < baseStart_4665064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665098 : List Nat := [3, 1, 2, 2, 1, 5, 1, 3, 5]
def baseStart_4665098 : Nat := 118140960795 + 4665098 * 2 ^ 59
def prefixEnd_4665098 : Nat := 4983230072969 + 3 ^ 40 * 4665098 * 2
def baseEnd_4665098 : Nat := 266159730480943779591179

theorem tailTrace_4665098 : CollatzResearch.WordTrace tailWord_4665098 prefixEnd_4665098 266159730480943779591179 := by
  unfold tailWord_4665098
  simp only [CollatzResearch.WordTrace]
  refine ⟨42537525613288539038042987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113433401635436104101447965 42537525613288539038042987)
  ·
    refine ⟨63806288419932808557064481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42537525613288539038042987 63806288419932808557064481)
    ·
      refine ⟨47854716314949606417798361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63806288419932808557064481 47854716314949606417798361)
      ·
        refine ⟨35891037236212204813348771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47854716314949606417798361 35891037236212204813348771)
        ·
          refine ⟨53836555854318307220023157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35891037236212204813348771 53836555854318307220023157)
          ·
            refine ⟨5047177111342341301877171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53836555854318307220023157 5047177111342341301877171)
            ·
              refine ⟨7570765667013511952815757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5047177111342341301877171 7570765667013511952815757)
              ·
                refine ⟨2839037125130066982305909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7570765667013511952815757 2839037125130066982305909)
                ·
                  refine ⟨266159730480943779591179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2839037125130066982305909 266159730480943779591179)
                  ·
                    rfl

theorem cell23_4665098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_4665098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665098 prefixEnd_4665098 := by exact prefixLift 4665098
  have htrace : WordTrace (prefixWord ++ tailWord_4665098) baseStart_4665098 baseEnd_4665098 := by
    simpa [prefixWord, tailWord_4665098, baseEnd_4665098] using wordTrace_append hprefix tailTrace_4665098
  have hstable : (prefixWord ++ tailWord_4665098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665098).length < 2 ^ (prefixWord ++ tailWord_4665098).sum := by decide
  have hdescent : baseEnd_4665098 < baseStart_4665098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665111 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 2, 5]
def baseStart_4665111 : Nat := 118140960795 + 4665111 * 2 ^ 59
def prefixEnd_4665111 : Nat := 4983230072969 + 3 ^ 40 * 4665111 * 2
def baseEnd_4665111 : Nat := 798481416525667488486017

theorem tailTrace_4665111 : CollatzResearch.WordTrace tailWord_4665111 prefixEnd_4665111 798481416525667488486017 := by
  unfold tailWord_4665111
  simp only [CollatzResearch.WordTrace]
  refine ⟨170150576602107059372395187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113433717734738039581596791 170150576602107059372395187)
  ·
    refine ⟨255225864903160589058592781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170150576602107059372395187 255225864903160589058592781)
    ·
      refine ⟨95709699338685220896972293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255225864903160589058592781 95709699338685220896972293)
      ·
        refine ⟨17945568626003478918182305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95709699338685220896972293 17945568626003478918182305)
        ·
          refine ⟨13459176469502609188636729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17945568626003478918182305 13459176469502609188636729)
          ·
            refine ⟨10094382352126956891477547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13459176469502609188636729 10094382352126956891477547)
            ·
              refine ⟨15141573528190435337216321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10094382352126956891477547 15141573528190435337216321)
              ·
                refine ⟨11356180146142826502912241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15141573528190435337216321 11356180146142826502912241)
                ·
                  refine ⟨8517135109607119877184181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11356180146142826502912241 8517135109607119877184181)
                  ·
                    refine ⟨798481416525667488486017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8517135109607119877184181 798481416525667488486017)
                    ·
                      rfl

theorem cell23_4665111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_4665111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665111 prefixEnd_4665111 := by exact prefixLift 4665111
  have htrace : WordTrace (prefixWord ++ tailWord_4665111) baseStart_4665111 baseEnd_4665111 := by
    simpa [prefixWord, tailWord_4665111, baseEnd_4665111] using wordTrace_append hprefix tailTrace_4665111
  have hstable : (prefixWord ++ tailWord_4665111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665111).length < 2 ^ (prefixWord ++ tailWord_4665111).sum := by decide
  have hdescent : baseEnd_4665111 < baseStart_4665111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665175 : List Nat := [1, 1, 3, 2, 5, 1, 1, 4, 1, 4]
def baseStart_4665175 : Nat := 118140960795 + 4665175 * 2 ^ 59
def prefixEnd_4665175 : Nat := 4983230072969 + 3 ^ 40 * 4665175 * 2
def baseEnd_4665175 : Nat := 798492370779630071685919

theorem tailTrace_4665175 : CollatzResearch.WordTrace tailWord_4665175 prefixEnd_4665175 798492370779630071685919 := by
  unfold tailWord_4665175
  simp only [CollatzResearch.WordTrace]
  refine ⟨170152910873875198302724979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113435273915916798868483319 170152910873875198302724979)
  ·
    refine ⟨255229366310812797454087469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170152910873875198302724979 255229366310812797454087469)
    ·
      refine ⟨95711012366554799045282801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255229366310812797454087469 95711012366554799045282801)
      ·
        refine ⟨71783259274916099283962101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95711012366554799045282801 71783259274916099283962101)
        ·
          refine ⟨6729680557023384307871447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71783259274916099283962101 6729680557023384307871447)
          ·
            refine ⟨10094520835535076461807171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6729680557023384307871447 10094520835535076461807171)
            ·
              refine ⟨15141781253302614692710757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10094520835535076461807171 15141781253302614692710757)
              ·
                refine ⟨2839083984994240254883267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15141781253302614692710757 2839083984994240254883267)
                ·
                  refine ⟨4258625977491360382324901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2839083984994240254883267 4258625977491360382324901)
                  ·
                    refine ⟨798492370779630071685919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4258625977491360382324901 798492370779630071685919)
                    ·
                      rfl

theorem cell23_4665175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_4665175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665175 prefixEnd_4665175 := by exact prefixLift 4665175
  have htrace : WordTrace (prefixWord ++ tailWord_4665175) baseStart_4665175 baseEnd_4665175 := by
    simpa [prefixWord, tailWord_4665175, baseEnd_4665175] using wordTrace_append hprefix tailTrace_4665175
  have hstable : (prefixWord ++ tailWord_4665175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665175).length < 2 ^ (prefixWord ++ tailWord_4665175).sum := by decide
  have hdescent : baseEnd_4665175 < baseStart_4665175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665201 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 1, 5]
def baseStart_4665201 : Nat := 118140960795 + 4665201 * 2 ^ 59
def prefixEnd_4665201 : Nat := 4983230072969 + 3 ^ 40 * 4665201 * 2
def baseEnd_4665201 : Nat := 798496820945302371110879

theorem tailTrace_4665201 : CollatzResearch.WordTrace tailWord_4665201 prefixEnd_4665201 798496820945302371110879 := by
  unfold tailWord_4665201
  simp only [CollatzResearch.WordTrace]
  refine ⟨170153859171781004743171457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113435906114520669828780971 170153859171781004743171457)
  ·
    refine ⟨127615394378835753557378593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170153859171781004743171457 127615394378835753557378593)
    ·
      refine ⟨95711545784126815168033945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127615394378835753557378593 95711545784126815168033945)
      ·
        refine ⟨71783659338095111376025459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95711545784126815168033945 71783659338095111376025459)
        ·
          refine ⟨107675489007142667064038189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71783659338095111376025459 107675489007142667064038189)
          ·
            refine ⟨40378308377678500149014321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107675489007142667064038189 40378308377678500149014321)
            ·
              refine ⟨30283731283258875111760741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40378308377678500149014321 30283731283258875111760741)
              ·
                refine ⟨5678199615611039083455139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30283731283258875111760741 5678199615611039083455139)
                ·
                  refine ⟨8517299423416558625182709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5678199615611039083455139 8517299423416558625182709)
                  ·
                    refine ⟨798496820945302371110879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8517299423416558625182709 798496820945302371110879)
                    ·
                      rfl

theorem cell23_4665201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_4665201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665201 prefixEnd_4665201 := by exact prefixLift 4665201
  have htrace : WordTrace (prefixWord ++ tailWord_4665201) baseStart_4665201 baseEnd_4665201 := by
    simpa [prefixWord, tailWord_4665201, baseEnd_4665201] using wordTrace_append hprefix tailTrace_4665201
  have hstable : (prefixWord ++ tailWord_4665201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665201).length < 2 ^ (prefixWord ++ tailWord_4665201).sum := by decide
  have hdescent : baseEnd_4665201 < baseStart_4665201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665241 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 5, 2, 3]
def baseStart_4665241 : Nat := 118140960795 + 4665241 * 2 ^ 59
def prefixEnd_4665241 : Nat := 4983230072969 + 3 ^ 40 * 4665241 * 2
def baseEnd_4665241 : Nat := 2395511002062086956832453

theorem tailTrace_4665241 : CollatzResearch.WordTrace tailWord_4665241 prefixEnd_4665241 2395511002062086956832453 := by
  unfold tailWord_4665241
  simp only [CollatzResearch.WordTrace]
  refine ⟨170155318091636091574627577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113436878727757394383085051 170155318091636091574627577)
  ·
    refine ⟨127616488568727068680970683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170155318091636091574627577 127616488568727068680970683)
    ·
      refine ⟨191424732853090603021456025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127616488568727068680970683 191424732853090603021456025)
      ·
        refine ⟨143568549639817952266092019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191424732853090603021456025 143568549639817952266092019)
        ·
          refine ⟨215352824459726928399138029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143568549639817952266092019 215352824459726928399138029)
          ·
            refine ⟨80757309172397598149676761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215352824459726928399138029 80757309172397598149676761)
            ·
              refine ⟨60567981879298198612257571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80757309172397598149676761 60567981879298198612257571)
              ·
                refine ⟨90851972818947297918386357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60567981879298198612257571 90851972818947297918386357)
                ·
                  refine ⟨8517372451776309179848721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90851972818947297918386357 8517372451776309179848721)
                  ·
                    refine ⟨6388029338832231884886541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8517372451776309179848721 6388029338832231884886541)
                    ·
                      refine ⟨2395511002062086956832453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6388029338832231884886541 2395511002062086956832453)
                      ·
                        rfl

theorem cell23_4665241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_4665241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665241 prefixEnd_4665241 := by exact prefixLift 4665241
  have htrace : WordTrace (prefixWord ++ tailWord_4665241) baseStart_4665241 baseEnd_4665241 := by
    simpa [prefixWord, tailWord_4665241, baseEnd_4665241] using wordTrace_append hprefix tailTrace_4665241
  have hstable : (prefixWord ++ tailWord_4665241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665241).length < 2 ^ (prefixWord ++ tailWord_4665241).sum := by decide
  have hdescent : baseEnd_4665241 < baseStart_4665241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665255 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_4665255 : Nat := 118140960795 + 4665255 * 2 ^ 59
def prefixEnd_4665255 : Nat := 4983230072969 + 3 ^ 40 * 4665255 * 2
def baseEnd_4665255 : Nat := 2395518190791249902057389

theorem tailTrace_4665255 : CollatzResearch.WordTrace tailWord_4665255 prefixEnd_4665255 2395518190791249902057389 := by
  unfold tailWord_4665255
  simp only [CollatzResearch.WordTrace]
  refine ⟨170155828713585371965637219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113437219142390247977091479 170155828713585371965637219)
  ·
    refine ⟨255233743070378057948455829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170155828713585371965637219 255233743070378057948455829)
    ·
      refine ⟨11964081706423971466333867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 255233743070378057948455829 11964081706423971466333867)
      ·
        refine ⟨17946122559635957199500801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11964081706423971466333867 17946122559635957199500801)
        ·
          refine ⟨13459591919726967899625601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17946122559635957199500801 13459591919726967899625601)
          ·
            refine ⟨10094693939795225924719201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13459591919726967899625601 10094693939795225924719201)
            ·
              refine ⟨7571020454846419443539401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10094693939795225924719201 7571020454846419443539401)
              ·
                refine ⟨5678265341134814582654551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7571020454846419443539401 5678265341134814582654551)
                ·
                  refine ⟨8517398011702221873981827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5678265341134814582654551 8517398011702221873981827)
                  ·
                    refine ⟨12776097017553332810972741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8517398011702221873981827 12776097017553332810972741)
                    ·
                      refine ⟨2395518190791249902057389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12776097017553332810972741 2395518190791249902057389)
                      ·
                        rfl

theorem cell23_4665255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_4665255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665255 prefixEnd_4665255 := by exact prefixLift 4665255
  have htrace : WordTrace (prefixWord ++ tailWord_4665255) baseStart_4665255 baseEnd_4665255 := by
    simpa [prefixWord, tailWord_4665255, baseEnd_4665255] using wordTrace_append hprefix tailTrace_4665255
  have hstable : (prefixWord ++ tailWord_4665255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665255).length < 2 ^ (prefixWord ++ tailWord_4665255).sum := by decide
  have hdescent : baseEnd_4665255 < baseStart_4665255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665264 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_4665264 : Nat := 118140960795 + 4665264 * 2 ^ 59
def prefixEnd_4665264 : Nat := 4983230072969 + 3 ^ 40 * 4665264 * 2
def baseEnd_4665264 : Nat := 2395522812117140366844847

theorem tailTrace_4665264 : CollatzResearch.WordTrace tailWord_4665264 prefixEnd_4665264 2395522812117140366844847 := by
  unfold tailWord_4665264
  simp only [CollatzResearch.WordTrace]
  refine ⟨85078078485276383251357423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113437437980368511001809897 85078078485276383251357423)
  ·
    refine ⟨127617117727914574877036135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85078078485276383251357423 127617117727914574877036135)
    ·
      refine ⟨191425676591871862315554203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127617117727914574877036135 191425676591871862315554203)
      ·
        refine ⟨287138514887807793473331305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191425676591871862315554203 287138514887807793473331305)
        ·
          refine ⟨215353886165855845104998479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287138514887807793473331305 215353886165855845104998479)
          ·
            refine ⟨323030829248783767657497719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215353886165855845104998479 323030829248783767657497719)
            ·
              refine ⟨484546243873175651486246579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323030829248783767657497719 484546243873175651486246579)
              ·
                refine ⟨726819365809763477229369869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484546243873175651486246579 726819365809763477229369869)
                ·
                  refine ⟨272557262178661303961013701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726819365809763477229369869 272557262178661303961013701)
                  ·
                    refine ⟨51104486658498994492690069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 272557262178661303961013701 51104486658498994492690069)
                    ·
                      refine ⟨2395522812117140366844847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51104486658498994492690069 2395522812117140366844847)
                      ·
                        rfl

theorem cell23_4665264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_4665264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665264 prefixEnd_4665264 := by exact prefixLift 4665264
  have htrace : WordTrace (prefixWord ++ tailWord_4665264) baseStart_4665264 baseEnd_4665264 := by
    simpa [prefixWord, tailWord_4665264, baseEnd_4665264] using wordTrace_append hprefix tailTrace_4665264
  have hstable : (prefixWord ++ tailWord_4665264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665264).length < 2 ^ (prefixWord ++ tailWord_4665264).sum := by decide
  have hdescent : baseEnd_4665264 < baseStart_4665264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665271 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 3]
def baseStart_4665271 : Nat := 118140960795 + 4665271 * 2 ^ 59
def prefixEnd_4665271 : Nat := 4983230072969 + 3 ^ 40 * 4665271 * 2
def baseEnd_4665271 : Nat := 2395526406481721839457315

theorem tailTrace_4665271 : CollatzResearch.WordTrace tailWord_4665271 prefixEnd_4665271 2395526406481721839457315 := by
  unfold tailWord_4665271
  simp only [CollatzResearch.WordTrace]
  refine ⟨170156412281527406698219667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113437608187684937798813111 170156412281527406698219667)
  ·
    refine ⟨255234618422291110047329501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170156412281527406698219667 255234618422291110047329501)
    ·
      refine ⟨95712981908359166267748563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255234618422291110047329501 95712981908359166267748563)
      ·
        refine ⟨143569472862538749401622845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95712981908359166267748563 143569472862538749401622845)
        ·
          refine ⟨53838552323452031025608567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143569472862538749401622845 53838552323452031025608567)
          ·
            refine ⟨80757828485178046538412851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53838552323452031025608567 80757828485178046538412851)
            ·
              refine ⟨121136742727767069807619277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80757828485178046538412851 121136742727767069807619277)
              ·
                refine ⟨45426278522912651177857229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121136742727767069807619277 45426278522912651177857229)
                ·
                  refine ⟨17034854446092244191696461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45426278522912651177857229 17034854446092244191696461)
                  ·
                    refine ⟨6388070417284591571886173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17034854446092244191696461 6388070417284591571886173)
                    ·
                      refine ⟨2395526406481721839457315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6388070417284591571886173 2395526406481721839457315)
                      ·
                        rfl

theorem cell23_4665271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_4665271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665271 prefixEnd_4665271 := by exact prefixLift 4665271
  have htrace : WordTrace (prefixWord ++ tailWord_4665271) baseStart_4665271 baseEnd_4665271 := by
    simpa [prefixWord, tailWord_4665271, baseEnd_4665271] using wordTrace_append hprefix tailTrace_4665271
  have hstable : (prefixWord ++ tailWord_4665271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665271).length < 2 ^ (prefixWord ++ tailWord_4665271).sum := by decide
  have hdescent : baseEnd_4665271 < baseStart_4665271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665309 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_4665309 : Nat := 118140960795 + 4665309 * 2 ^ 59
def prefixEnd_4665309 : Nat := 4983230072969 + 3 ^ 40 * 4665309 * 2
def baseEnd_4665309 : Nat := 2395545918746592690782141

theorem tailTrace_4665309 : CollatzResearch.WordTrace tailWord_4665309 prefixEnd_4665309 2395545918746592690782141 := by
  unfold tailWord_4665309
  simp only [CollatzResearch.WordTrace]
  refine ⟨170157798255389739188102981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113438532170259826125401987 170157798255389739188102981)
  ·
    refine ⟨31904587172885576097769309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170157798255389739188102981 31904587172885576097769309)
    ·
      refine ⟨11964220189832091036663491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31904587172885576097769309 11964220189832091036663491)
      ·
        refine ⟨17946330284748136554995237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11964220189832091036663491 17946330284748136554995237)
        ·
          refine ⟨3364936928390275604061607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17946330284748136554995237 3364936928390275604061607)
          ·
            refine ⟨5047405392585413406092411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3364936928390275604061607 5047405392585413406092411)
            ·
              refine ⟨7571108088878120109138617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5047405392585413406092411 7571108088878120109138617)
              ·
                refine ⟨5678331066658590081853963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7571108088878120109138617 5678331066658590081853963)
                ·
                  refine ⟨8517496599987885122780945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5678331066658590081853963 8517496599987885122780945)
                  ·
                    refine ⟨6388122449990913842085709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8517496599987885122780945 6388122449990913842085709)
                    ·
                      refine ⟨2395545918746592690782141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6388122449990913842085709 2395545918746592690782141)
                      ·
                        rfl

theorem cell23_4665309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_4665309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665309 prefixEnd_4665309 := by exact prefixLift 4665309
  have htrace : WordTrace (prefixWord ++ tailWord_4665309) baseStart_4665309 baseEnd_4665309 := by
    simpa [prefixWord, tailWord_4665309, baseEnd_4665309] using wordTrace_append hprefix tailTrace_4665309
  have hstable : (prefixWord ++ tailWord_4665309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665309).length < 2 ^ (prefixWord ++ tailWord_4665309).sum := by decide
  have hdescent : baseEnd_4665309 < baseStart_4665309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665315 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 3, 3, 2]
def baseStart_4665315 : Nat := 118140960795 + 4665315 * 2 ^ 59
def prefixEnd_4665315 : Nat := 4983230072969 + 3 ^ 40 * 4665315 * 2
def baseEnd_4665315 : Nat := 2395548999630519667307113

theorem tailTrace_4665315 : CollatzResearch.WordTrace tailWord_4665315 prefixEnd_4665315 2395548999630519667307113 := by
  unfold tailWord_4665315
  simp only [CollatzResearch.WordTrace]
  refine ⟨170158017093368002212821399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113438678062245334808547599 170158017093368002212821399)
  ·
    refine ⟨255237025640052003319232099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170158017093368002212821399 255237025640052003319232099)
    ·
      refine ⟨382855538460078004978848149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255237025640052003319232099 382855538460078004978848149)
      ·
        refine ⟨17946353365316156483383507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 382855538460078004978848149 17946353365316156483383507)
        ·
          refine ⟨26919530047974234725075261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17946353365316156483383507 26919530047974234725075261)
          ·
            refine ⟨10094823767990338021903223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26919530047974234725075261 10094823767990338021903223)
            ·
              refine ⟨15142235651985507032854835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10094823767990338021903223 15142235651985507032854835)
              ·
                refine ⟨22713353477978260549282253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15142235651985507032854835 22713353477978260549282253)
                ·
                  refine ⟨8517507554241847705980845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22713353477978260549282253 8517507554241847705980845)
                  ·
                    refine ⟨3194065332840692889742817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8517507554241847705980845 3194065332840692889742817)
                    ·
                      refine ⟨2395548999630519667307113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194065332840692889742817 2395548999630519667307113)
                      ·
                        rfl

theorem cell23_4665315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_4665315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665315 prefixEnd_4665315 := by exact prefixLift 4665315
  have htrace : WordTrace (prefixWord ++ tailWord_4665315) baseStart_4665315 baseEnd_4665315 := by
    simpa [prefixWord, tailWord_4665315, baseEnd_4665315] using wordTrace_append hprefix tailTrace_4665315
  have hstable : (prefixWord ++ tailWord_4665315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665315).length < 2 ^ (prefixWord ++ tailWord_4665315).sum := by decide
  have hdescent : baseEnd_4665315 < baseStart_4665315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665328 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 3, 4, 2]
def baseStart_4665328 : Nat := 118140960795 + 4665328 * 2 ^ 59
def prefixEnd_4665328 : Nat := 4983230072969 + 3 ^ 40 * 4665328 * 2
def baseEnd_4665328 : Nat := 2395555674879028116444553

theorem tailTrace_4665328 : CollatzResearch.WordTrace tailWord_4665328 prefixEnd_4665328 2395555674879028116444553 := by
  unfold tailWord_4665328
  simp only [CollatzResearch.WordTrace]
  refine ⟨85079245621160452716522319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113438994161547270288696425 85079245621160452716522319)
  ·
    refine ⟨127618868431740679074783479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85079245621160452716522319 127618868431740679074783479)
    ·
      refine ⟨191428302647611018612175219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127618868431740679074783479 191428302647611018612175219)
      ·
        refine ⟨287142453971416527918262829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191428302647611018612175219 287142453971416527918262829)
        ·
          refine ⟨107678420239281197969348561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287142453971416527918262829 107678420239281197969348561)
          ·
            refine ⟨80758815179460898477011421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107678420239281197969348561 80758815179460898477011421)
            ·
              refine ⟨30284555692297836928879283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80758815179460898477011421 30284555692297836928879283)
              ·
                refine ⟨45426833538446755393318925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30284555692297836928879283 45426833538446755393318925)
                ·
                  refine ⟨17035062576917533272494597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45426833538446755393318925 17035062576917533272494597)
                  ·
                    refine ⟨3194074233172037488592737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17035062576917533272494597 3194074233172037488592737)
                    ·
                      refine ⟨2395555674879028116444553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194074233172037488592737 2395555674879028116444553)
                      ·
                        rfl

theorem cell23_4665328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 4, 2].length) (baseStart_4665328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665328 prefixEnd_4665328 := by exact prefixLift 4665328
  have htrace : WordTrace (prefixWord ++ tailWord_4665328) baseStart_4665328 baseEnd_4665328 := by
    simpa [prefixWord, tailWord_4665328, baseEnd_4665328] using wordTrace_append hprefix tailTrace_4665328
  have hstable : (prefixWord ++ tailWord_4665328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665328).length < 2 ^ (prefixWord ++ tailWord_4665328).sum := by decide
  have hdescent : baseEnd_4665328 < baseStart_4665328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665331 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 3]
def baseStart_4665331 : Nat := 118140960795 + 4665331 * 2 ^ 59
def prefixEnd_4665331 : Nat := 4983230072969 + 3 ^ 40 * 4665331 * 2
def baseEnd_4665331 : Nat := 2395557215320991604707039

theorem tailTrace_4665331 : CollatzResearch.WordTrace tailWord_4665331 prefixEnd_4665331 2395557215320991604707039 := by
  unfold tailWord_4665331
  simp only [CollatzResearch.WordTrace]
  refine ⟨170158600661310036945403847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113439067107540024630269231 170158600661310036945403847)
  ·
    refine ⟨255237900991965055418105771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170158600661310036945403847 255237900991965055418105771)
    ·
      refine ⟨382856851487947583127158657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255237900991965055418105771 382856851487947583127158657)
      ·
        refine ⟨287142638615960687345368993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382856851487947583127158657 287142638615960687345368993)
        ·
          refine ⟨215356978961970515509026745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287142638615960687345368993 215356978961970515509026745)
          ·
            refine ⟨161517734221477886631770059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215356978961970515509026745 161517734221477886631770059)
            ·
              refine ⟨242276601332216829947655089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161517734221477886631770059 242276601332216829947655089)
              ·
                refine ⟨181707450999162622460741317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242276601332216829947655089 181707450999162622460741317)
                ·
                  refine ⟨34070147062342991711388997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181707450999162622460741317 34070147062342991711388997)
                  ·
                    refine ⟨6388152574189310945885437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34070147062342991711388997 6388152574189310945885437)
                    ·
                      refine ⟨2395557215320991604707039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6388152574189310945885437 2395557215320991604707039)
                      ·
                        rfl

theorem cell23_4665331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 3].length) (baseStart_4665331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665331 prefixEnd_4665331 := by exact prefixLift 4665331
  have htrace : WordTrace (prefixWord ++ tailWord_4665331) baseStart_4665331 baseEnd_4665331 := by
    simpa [prefixWord, tailWord_4665331, baseEnd_4665331] using wordTrace_append hprefix tailTrace_4665331
  have hstable : (prefixWord ++ tailWord_4665331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665331).length < 2 ^ (prefixWord ++ tailWord_4665331).sum := by decide
  have hdescent : baseEnd_4665331 < baseStart_4665331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665358 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_4665358 : Nat := 118140960795 + 4665358 * 2 ^ 59
def prefixEnd_4665358 : Nat := 4983230072969 + 3 ^ 40 * 4665358 * 2
def baseEnd_4665358 : Nat := 2395571079298662999069415

theorem tailTrace_4665358 : CollatzResearch.WordTrace tailWord_4665358 prefixEnd_4665358 2395571079298662999069415 := by
  unfold tailWord_4665358
  simp only [CollatzResearch.WordTrace]
  refine ⟨21269948179026527569579591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113439723621474813704424485 21269948179026527569579591)
  ·
    refine ⟨31904922268539791354369387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21269948179026527569579591 31904922268539791354369387)
    ·
      refine ⟨47857383402809687031554081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31904922268539791354369387 47857383402809687031554081)
      ·
        refine ⟨35893037552107265273665561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47857383402809687031554081 35893037552107265273665561)
        ·
          refine ⟨26919778164080448955249171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35893037552107265273665561 26919778164080448955249171)
          ·
            refine ⟨40379667246120673432873757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26919778164080448955249171 40379667246120673432873757)
            ·
              refine ⟨15142375217295252537327659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40379667246120673432873757 15142375217295252537327659)
              ·
                refine ⟨22713562825942878805991489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15142375217295252537327659 22713562825942878805991489)
                ·
                  refine ⟨17035172119457159104493617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22713562825942878805991489 17035172119457159104493617)
                  ·
                    refine ⟨12776379089592869328370213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17035172119457159104493617 12776379089592869328370213)
                    ·
                      refine ⟨2395571079298662999069415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12776379089592869328370213 2395571079298662999069415)
                      ·
                        rfl

theorem cell23_4665358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_4665358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665358 prefixEnd_4665358 := by exact prefixLift 4665358
  have htrace : WordTrace (prefixWord ++ tailWord_4665358) baseStart_4665358 baseEnd_4665358 := by
    simpa [prefixWord, tailWord_4665358, baseEnd_4665358] using wordTrace_append hprefix tailTrace_4665358
  have hstable : (prefixWord ++ tailWord_4665358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665358).length < 2 ^ (prefixWord ++ tailWord_4665358).sum := by decide
  have hdescent : baseEnd_4665358 < baseStart_4665358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665378 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_4665378 : Nat := 118140960795 + 4665378 * 2 ^ 59
def prefixEnd_4665378 : Nat := 4983230072969 + 3 ^ 40 * 4665378 * 2
def baseEnd_4665378 : Nat := 2395581348911752920819323

theorem tailTrace_4665378 : CollatzResearch.WordTrace tailWord_4665378 prefixEnd_4665378 2395581348911752920819323 := by
  unfold tailWord_4665378
  simp only [CollatzResearch.WordTrace]
  refine ⟨42540078723034940993091197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113440209928093175981576525 42540078723034940993091197)
  ·
    refine ⟨15952529521138102872409199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42540078723034940993091197 15952529521138102872409199)
    ·
      refine ⟨23928794281707154308613799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15952529521138102872409199 23928794281707154308613799)
      ·
        refine ⟨35893191422560731462920699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23928794281707154308613799 35893191422560731462920699)
        ·
          refine ⟨53839787133841097194381049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35893191422560731462920699 53839787133841097194381049)
          ·
            refine ⟨40379840350380822895785787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53839787133841097194381049 40379840350380822895785787)
            ·
              refine ⟨60569760525571234343678681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40379840350380822895785787 60569760525571234343678681)
              ·
                refine ⟨45427320394178425757759011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60569760525571234343678681 45427320394178425757759011)
                ·
                  refine ⟨68140980591267638636638517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45427320394178425757759011 68140980591267638636638517)
                  ·
                    refine ⟨6388216930431341122184861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68140980591267638636638517 6388216930431341122184861)
                    ·
                      refine ⟨2395581348911752920819323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6388216930431341122184861 2395581348911752920819323)
                      ·
                        rfl

theorem cell23_4665378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_4665378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665378 prefixEnd_4665378 := by exact prefixLift 4665378
  have htrace : WordTrace (prefixWord ++ tailWord_4665378) baseStart_4665378 baseEnd_4665378 := by
    simpa [prefixWord, tailWord_4665378, baseEnd_4665378] using wordTrace_append hprefix tailTrace_4665378
  have hstable : (prefixWord ++ tailWord_4665378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665378).length < 2 ^ (prefixWord ++ tailWord_4665378).sum := by decide
  have hdescent : baseEnd_4665378 < baseStart_4665378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665383 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_4665383 : Nat := 118140960795 + 4665383 * 2 ^ 59
def prefixEnd_4665383 : Nat := 4983230072969 + 3 ^ 40 * 4665383 * 2
def baseEnd_4665383 : Nat := 2395583916315025401256801

theorem tailTrace_4665383 : CollatzResearch.WordTrace tailWord_4665383 prefixEnd_4665383 2395583916315025401256801 := by
  unfold tailWord_4665383
  simp only [CollatzResearch.WordTrace]
  refine ⟨170160497257121649826296803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113440331504747766550864535 170160497257121649826296803)
  ·
    refine ⟨255240745885682474739445205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170160497257121649826296803 255240745885682474739445205)
    ·
      refine ⟨5982204981695683001705747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 255240745885682474739445205 5982204981695683001705747)
      ·
        refine ⟨8973307472543524502558621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5982204981695683001705747 8973307472543524502558621)
        ·
          refine ⟨3364990302203821688459483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8973307472543524502558621 3364990302203821688459483)
          ·
            refine ⟨5047485453305732532689225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3364990302203821688459483 5047485453305732532689225)
            ·
              refine ⟨3785614089979299399516919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5047485453305732532689225 3785614089979299399516919)
              ·
                refine ⟨5678421134968949099275379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3785614089979299399516919 5678421134968949099275379)
                ·
                  refine ⟨8517631702453423648913069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5678421134968949099275379 8517631702453423648913069)
                  ·
                    refine ⟨3194111888420033868342401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8517631702453423648913069 3194111888420033868342401)
                    ·
                      refine ⟨2395583916315025401256801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194111888420033868342401 2395583916315025401256801)
                      ·
                        rfl

theorem cell23_4665383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_4665383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665383 prefixEnd_4665383 := by exact prefixLift 4665383
  have htrace : WordTrace (prefixWord ++ tailWord_4665383) baseStart_4665383 baseEnd_4665383 := by
    simpa [prefixWord, tailWord_4665383, baseEnd_4665383] using wordTrace_append hprefix tailTrace_4665383
  have hstable : (prefixWord ++ tailWord_4665383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665383).length < 2 ^ (prefixWord ++ tailWord_4665383).sum := by decide
  have hdescent : baseEnd_4665383 < baseStart_4665383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665388 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 1, 7, 2]
def baseStart_4665388 : Nat := 118140960795 + 4665388 * 2 ^ 59
def prefixEnd_4665388 : Nat := 4983230072969 + 3 ^ 40 * 4665388 * 2
def baseEnd_4665388 : Nat := 2395586483718297881694277

theorem tailTrace_4665388 : CollatzResearch.WordTrace tailWord_4665388 prefixEnd_4665388 2395586483718297881694277 := by
  unfold tailWord_4665388
  simp only [CollatzResearch.WordTrace]
  refine ⟨85080339811051767840114409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113440453081402357120152545 85080339811051767840114409)
  ·
    refine ⟨63810254858288825880085807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85080339811051767840114409 63810254858288825880085807)
    ·
      refine ⟨95715382287433238820128711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63810254858288825880085807 95715382287433238820128711)
      ·
        refine ⟨143573073431149858230193067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95715382287433238820128711 143573073431149858230193067)
        ·
          refine ⟨215359610146724787345289601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143573073431149858230193067 215359610146724787345289601)
          ·
            refine ⟨161519707610043590508967201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215359610146724787345289601 161519707610043590508967201)
            ·
              refine ⟨121139780707532692881725401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161519707610043590508967201 121139780707532692881725401)
              ·
                refine ⟨90854835530649519661294051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121139780707532692881725401 90854835530649519661294051)
                ·
                  refine ⟨136282253295974279491941077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90854835530649519661294051 136282253295974279491941077)
                  ·
                    refine ⟨3194115311624397175592369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 136282253295974279491941077 3194115311624397175592369)
                    ·
                      refine ⟨2395586483718297881694277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194115311624397175592369 2395586483718297881694277)
                      ·
                        rfl

theorem cell23_4665388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 7, 2].length) (baseStart_4665388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665388 prefixEnd_4665388 := by exact prefixLift 4665388
  have htrace : WordTrace (prefixWord ++ tailWord_4665388) baseStart_4665388 baseEnd_4665388 := by
    simpa [prefixWord, tailWord_4665388, baseEnd_4665388] using wordTrace_append hprefix tailTrace_4665388
  have hstable : (prefixWord ++ tailWord_4665388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665388).length < 2 ^ (prefixWord ++ tailWord_4665388).sum := by decide
  have hdescent : baseEnd_4665388 < baseStart_4665388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665391 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 5]
def baseStart_4665391 : Nat := 118140960795 + 4665391 * 2 ^ 59
def prefixEnd_4665391 : Nat := 4983230072969 + 3 ^ 40 * 4665391 * 2
def baseEnd_4665391 : Nat := 2395588024160261369956763

theorem tailTrace_4665391 : CollatzResearch.WordTrace tailWord_4665391 prefixEnd_4665391 2395588024160261369956763 := by
  unfold tailWord_4665391
  simp only [CollatzResearch.WordTrace]
  refine ⟨170160789041092667192588027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113440526027395111461725351 170160789041092667192588027)
  ·
    refine ⟨255241183561639000788882041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170160789041092667192588027 255241183561639000788882041)
    ·
      refine ⟨191430887671229250591661531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255241183561639000788882041 191430887671229250591661531)
      ·
        refine ⟨287146331506843875887492297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191430887671229250591661531 287146331506843875887492297)
        ·
          refine ⟨215359748630132906915619223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287146331506843875887492297 215359748630132906915619223)
          ·
            refine ⟨323039622945199360373428835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215359748630132906915619223 323039622945199360373428835)
            ·
              refine ⟨484559434417799040560143253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323039622945199360373428835 484559434417799040560143253)
              ·
                refine ⟨22713723488334330026256715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 484559434417799040560143253 22713723488334330026256715)
                ·
                  refine ⟨34070585232501495039385073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22713723488334330026256715 34070585232501495039385073)
                  ·
                    refine ⟨25552938924376121279538805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34070585232501495039385073 25552938924376121279538805)
                    ·
                      refine ⟨2395588024160261369956763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25552938924376121279538805 2395588024160261369956763)
                      ·
                        rfl

theorem cell23_4665391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_4665391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665391 prefixEnd_4665391 := by exact prefixLift 4665391
  have htrace : WordTrace (prefixWord ++ tailWord_4665391) baseStart_4665391 baseEnd_4665391 := by
    simpa [prefixWord, tailWord_4665391, baseEnd_4665391] using wordTrace_append hprefix tailTrace_4665391
  have hstable : (prefixWord ++ tailWord_4665391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665391).length < 2 ^ (prefixWord ++ tailWord_4665391).sum := by decide
  have hdescent : baseEnd_4665391 < baseStart_4665391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665455 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 3]
def baseStart_4665455 : Nat := 118140960795 + 4665455 * 2 ^ 59
def prefixEnd_4665455 : Nat := 4983230072969 + 3 ^ 40 * 4665455 * 2
def baseEnd_4665455 : Nat := 2395620886922149119556469

theorem tailTrace_4665455 : CollatzResearch.WordTrace tailWord_4665455 prefixEnd_4665455 2395620886922149119556469 := by
  unfold tailWord_4665455
  simp only [CollatzResearch.WordTrace]
  refine ⟨170163123312860806122917819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113442082208573870748611879 170163123312860806122917819)
  ·
    refine ⟨255244684969291209184376729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170163123312860806122917819 255244684969291209184376729)
    ·
      refine ⟨191433513726968406888282547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255244684969291209184376729 191433513726968406888282547)
      ·
        refine ⟨287150270590452610332423821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191433513726968406888282547 287150270590452610332423821)
        ·
          refine ⟨107681351471419728874658933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287150270590452610332423821 107681351471419728874658933)
          ·
            refine ⟨10095126700445599581999275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107681351471419728874658933 10095126700445599581999275)
            ·
              refine ⟨15142690050668399372998913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10095126700445599581999275 15142690050668399372998913)
              ·
                refine ⟨11357017538001299529749185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15142690050668399372998913 11357017538001299529749185)
                ·
                  refine ⟨8517763153500974647311889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11357017538001299529749185 8517763153500974647311889)
                  ·
                    refine ⟨6388322365125730985483917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8517763153500974647311889 6388322365125730985483917)
                    ·
                      refine ⟨2395620886922149119556469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6388322365125730985483917 2395620886922149119556469)
                      ·
                        rfl

theorem cell23_4665455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 3].length) (baseStart_4665455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665455 prefixEnd_4665455 := by exact prefixLift 4665455
  have htrace : WordTrace (prefixWord ++ tailWord_4665455) baseStart_4665455 baseEnd_4665455 := by
    simpa [prefixWord, tailWord_4665455, baseEnd_4665455] using wordTrace_append hprefix tailTrace_4665455
  have hstable : (prefixWord ++ tailWord_4665455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665455).length < 2 ^ (prefixWord ++ tailWord_4665455).sum := by decide
  have hdescent : baseEnd_4665455 < baseStart_4665455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665458 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 8]
def baseStart_4665458 : Nat := 118140960795 + 4665458 * 2 ^ 59
def prefixEnd_4665458 : Nat := 4983230072969 + 3 ^ 40 * 4665458 * 2
def baseEnd_4665458 : Nat := 266180269707123623090995

theorem tailTrace_4665458 : CollatzResearch.WordTrace tailWord_4665458 prefixEnd_4665458 266180269707123623090995 := by
  unfold tailWord_4665458
  simp only [CollatzResearch.WordTrace]
  refine ⟨42540808182962484408819257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113442155154566625090184685 42540808182962484408819257)
  ·
    refine ⟨31905606137221863306614443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42540808182962484408819257 31905606137221863306614443)
    ·
      refine ⟨47858409205832794959921665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31905606137221863306614443 47858409205832794959921665)
      ·
        refine ⟨35893806904374596219941249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47858409205832794959921665 35893806904374596219941249)
        ·
          refine ⟨26920355178280947164955937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35893806904374596219941249 26920355178280947164955937)
          ·
            refine ⟨20190266383710710373716953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26920355178280947164955937 20190266383710710373716953)
            ·
              refine ⟨15142699787783032780287715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20190266383710710373716953 15142699787783032780287715)
              ·
                refine ⟨22714049681674549170431573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15142699787783032780287715 22714049681674549170431573)
                ·
                  refine ⟨266180269707123623090995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22714049681674549170431573 266180269707123623090995)
                  ·
                    rfl

theorem cell23_4665458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_4665458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665458 prefixEnd_4665458 := by exact prefixLift 4665458
  have htrace : WordTrace (prefixWord ++ tailWord_4665458) baseStart_4665458 baseEnd_4665458 := by
    simpa [prefixWord, tailWord_4665458, baseEnd_4665458] using wordTrace_append hprefix tailTrace_4665458
  have hstable : (prefixWord ++ tailWord_4665458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665458).length < 2 ^ (prefixWord ++ tailWord_4665458).sum := by decide
  have hdescent : baseEnd_4665458 < baseStart_4665458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665462 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_4665462 : Nat := 118140960795 + 4665462 * 2 ^ 59
def prefixEnd_4665462 : Nat := 4983230072969 + 3 ^ 40 * 4665462 * 2
def baseEnd_4665462 : Nat := 798541493762243530722979

theorem tailTrace_4665462 : CollatzResearch.WordTrace tailWord_4665462 prefixEnd_4665462 798541493762243530722979 := by
  unfold tailWord_4665462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10635211163989715394901415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113442252415890297545615093 10635211163989715394901415)
  ·
    refine ⟨15952816745984573092352123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10635211163989715394901415 15952816745984573092352123)
    ·
      refine ⟨23929225118976859638528185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15952816745984573092352123 23929225118976859638528185)
      ·
        refine ⟨17946918839232644728896139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23929225118976859638528185 17946918839232644728896139)
        ·
          refine ⟨26920378258848967093344209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17946918839232644728896139 26920378258848967093344209)
          ·
            refine ⟨20190283694136725320008157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26920378258848967093344209 20190283694136725320008157)
            ·
              refine ⟨7571356385301271995003059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20190283694136725320008157 7571356385301271995003059)
              ·
                refine ⟨11357034577951907992504589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7571356385301271995003059 11357034577951907992504589)
                ·
                  refine ⟨4258887966731965497189221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11357034577951907992504589 4258887966731965497189221)
                  ·
                    refine ⟨798541493762243530722979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4258887966731965497189221 798541493762243530722979)
                    ·
                      rfl

theorem cell23_4665462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_4665462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665462 prefixEnd_4665462 := by exact prefixLift 4665462
  have htrace : WordTrace (prefixWord ++ tailWord_4665462) baseStart_4665462 baseEnd_4665462 := by
    simpa [prefixWord, tailWord_4665462, baseEnd_4665462] using wordTrace_append hprefix tailTrace_4665462
  have hstable : (prefixWord ++ tailWord_4665462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665462).length < 2 ^ (prefixWord ++ tailWord_4665462).sum := by decide
  have hdescent : baseEnd_4665462 < baseStart_4665462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665475 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 6]
def baseStart_4665475 : Nat := 118140960795 + 4665475 * 2 ^ 59
def prefixEnd_4665475 : Nat := 4983230072969 + 3 ^ 40 * 4665475 * 2
def baseEnd_4665475 : Nat := 266181239615026560145153

theorem tailTrace_4665475 : CollatzResearch.WordTrace tailWord_4665475 prefixEnd_4665475 266181239615026560145153 := by
  unfold tailWord_4665475
  simp only [CollatzResearch.WordTrace]
  refine ⟨170163852772788349538645879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113442568515192233025763919 170163852772788349538645879)
  ·
    refine ⟨255245779159182524307968819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170163852772788349538645879 255245779159182524307968819)
    ·
      refine ⟨382868668738773786461953229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255245779159182524307968819 382868668738773786461953229)
      ·
        refine ⟨143575750777040169923232461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 382868668738773786461953229 143575750777040169923232461)
        ·
          refine ⟨53840906541390063721212173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143575750777040169923232461 53840906541390063721212173)
          ·
            refine ⟨20190339953021273895454565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53840906541390063721212173 20190339953021273895454565)
            ·
              refine ⟨3785688741191488855397731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20190339953021273895454565 3785688741191488855397731)
              ·
                refine ⟨5678533111787233283096597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3785688741191488855397731 5678533111787233283096597)
                ·
                  refine ⟨266181239615026560145153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5678533111787233283096597 266181239615026560145153)
                  ·
                    rfl

theorem cell23_4665475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 6].length) (baseStart_4665475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665475 prefixEnd_4665475 := by exact prefixLift 4665475
  have htrace : WordTrace (prefixWord ++ tailWord_4665475) baseStart_4665475 baseEnd_4665475 := by
    simpa [prefixWord, tailWord_4665475, baseEnd_4665475] using wordTrace_append hprefix tailTrace_4665475
  have hstable : (prefixWord ++ tailWord_4665475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665475).length < 2 ^ (prefixWord ++ tailWord_4665475).sum := by decide
  have hdescent : baseEnd_4665475 < baseStart_4665475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665488 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 3, 5]
def baseStart_4665488 : Nat := 118140960795 + 4665488 * 2 ^ 59
def prefixEnd_4665488 : Nat := 4983230072969 + 3 ^ 40 * 4665488 * 2
def baseEnd_4665488 : Nat := 798545943927915830147939

theorem tailTrace_4665488 : CollatzResearch.WordTrace tailWord_4665488 prefixEnd_4665488 798545943927915830147939 := by
  unfold tailWord_4665488
  simp only [CollatzResearch.WordTrace]
  refine ⟨85082163460870626379434559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113442884614494168505912745 85082163460870626379434559)
  ·
    refine ⟨127623245191305939569151839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85082163460870626379434559 127623245191305939569151839)
    ·
      refine ⟨191434867786958909353727759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127623245191305939569151839 191434867786958909353727759)
      ·
        refine ⟨287152301680438364030591639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191434867786958909353727759 287152301680438364030591639)
        ·
          refine ⟨430728452520657546045887459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287152301680438364030591639 430728452520657546045887459)
          ·
            refine ⟨646092678780986319068831189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430728452520657546045887459 646092678780986319068831189)
            ·
              refine ⟨15142797158929366853175731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 646092678780986319068831189 15142797158929366853175731)
              ·
                refine ⟨22714195738394050279763597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15142797158929366853175731 22714195738394050279763597)
                ·
                  refine ⟨8517823401897768854911349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22714195738394050279763597 8517823401897768854911349)
                  ·
                    refine ⟨798545943927915830147939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8517823401897768854911349 798545943927915830147939)
                    ·
                      rfl

theorem cell23_4665488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_4665488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665488 prefixEnd_4665488 := by exact prefixLift 4665488
  have htrace : WordTrace (prefixWord ++ tailWord_4665488) baseStart_4665488 baseEnd_4665488 := by
    simpa [prefixWord, tailWord_4665488, baseEnd_4665488] using wordTrace_append hprefix tailTrace_4665488
  have hstable : (prefixWord ++ tailWord_4665488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665488).length < 2 ^ (prefixWord ++ tailWord_4665488).sum := by decide
  have hdescent : baseEnd_4665488 < baseStart_4665488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665528 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_4665528 : Nat := 118140960795 + 4665528 * 2 ^ 59
def prefixEnd_4665528 : Nat := 4983230072969 + 3 ^ 40 * 4665528 * 2
def baseEnd_4665528 : Nat := 2395658371009927333943633

theorem tailTrace_4665528 : CollatzResearch.WordTrace tailWord_4665528 prefixEnd_4665528 2395658371009927333943633 := by
  unfold tailWord_4665528
  simp only [CollatzResearch.WordTrace]
  refine ⟨85082892920798169795162619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113443857227730893060216825 85082892920798169795162619)
  ·
    refine ⟨127624339381197254692743929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85082892920798169795162619 127624339381197254692743929)
    ·
      refine ⟨95718254535897941019557947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127624339381197254692743929 95718254535897941019557947)
      ·
        refine ⟨143577381803846911529336921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95718254535897941019557947 143577381803846911529336921)
        ·
          refine ⟨107683036352885183647002691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143577381803846911529336921 107683036352885183647002691)
          ·
            refine ⟨161524554529327775470504037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107683036352885183647002691 161524554529327775470504037)
            ·
              refine ⟨30285853974248957900719507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161524554529327775470504037 30285853974248957900719507)
              ·
                refine ⟨45428780961373436851079261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30285853974248957900719507 45428780961373436851079261)
                ·
                  refine ⟨17035792860515038819154723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45428780961373436851079261 17035792860515038819154723)
                  ·
                    refine ⟨25553689290772558228732085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17035792860515038819154723 25553689290772558228732085)
                    ·
                      refine ⟨2395658371009927333943633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25553689290772558228732085 2395658371009927333943633)
                      ·
                        rfl

theorem cell23_4665528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_4665528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665528 prefixEnd_4665528 := by exact prefixLift 4665528
  have htrace : WordTrace (prefixWord ++ tailWord_4665528) baseStart_4665528 baseEnd_4665528 := by
    simpa [prefixWord, tailWord_4665528, baseEnd_4665528] using wordTrace_append hprefix tailTrace_4665528
  have hstable : (prefixWord ++ tailWord_4665528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665528).length < 2 ^ (prefixWord ++ tailWord_4665528).sum := by decide
  have hdescent : baseEnd_4665528 < baseStart_4665528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665565 : List Nat := [1, 4, 3, 2, 1, 2, 10]
def baseStart_4665565 : Nat := 118140960795 + 4665565 * 2 ^ 59
def prefixEnd_4665565 : Nat := 4983230072969 + 3 ^ 40 * 4665565 * 2
def baseEnd_4665565 : Nat := 29576263824619057891123

theorem tailTrace_4665565 : CollatzResearch.WordTrace tailWord_4665565 prefixEnd_4665565 29576263824619057891123 := by
  unfold tailWord_4665565
  simp only [CollatzResearch.WordTrace]
  refine ⟨170167135342462294909422149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113444756894974863272948099 170167135342462294909422149)
  ·
    refine ⟨31906337876711680295516653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170167135342462294909422149 31906337876711680295516653)
    ·
      refine ⟨11964876703766880110818745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31906337876711680295516653 11964876703766880110818745)
      ·
        refine ⟨8973657527825160083114059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11964876703766880110818745 8973657527825160083114059)
        ·
          refine ⟨13460486291737740124671089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8973657527825160083114059 13460486291737740124671089)
          ·
            refine ⟨10095364718803305093503317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13460486291737740124671089 10095364718803305093503317)
            ·
              refine ⟨29576263824619057891123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10095364718803305093503317 29576263824619057891123)
              ·
                rfl

theorem cell23_4665565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 10].length) (baseStart_4665565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665565 prefixEnd_4665565 := by exact prefixLift 4665565
  have htrace : WordTrace (prefixWord ++ tailWord_4665565) baseStart_4665565 baseEnd_4665565 := by
    simpa [prefixWord, tailWord_4665565, baseEnd_4665565] using wordTrace_append hprefix tailTrace_4665565
  have hstable : (prefixWord ++ tailWord_4665565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665565).length < 2 ^ (prefixWord ++ tailWord_4665565).sum := by decide
  have hdescent : baseEnd_4665565 < baseStart_4665565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665576 : List Nat := [2, 1, 4, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_4665576 : Nat := 118140960795 + 4665576 * 2 ^ 59
def prefixEnd_4665576 : Nat := 4983230072969 + 3 ^ 40 * 4665576 * 2
def baseEnd_4665576 : Nat := 2395683018081343146143413

theorem tailTrace_4665576 : CollatzResearch.WordTrace tailWord_4665576 prefixEnd_4665576 2395683018081343146143413 := by
  unfold tailWord_4665576
  simp only [CollatzResearch.WordTrace]
  refine ⟨85083768272711221894036291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113445024363614962525381721 85083768272711221894036291)
  ·
    refine ⟨127625652409066832841054437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85083768272711221894036291 127625652409066832841054437)
    ·
      refine ⟨23929809826700031157697707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127625652409066832841054437 23929809826700031157697707)
      ·
        refine ⟨35894714740050046736546561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23929809826700031157697707 35894714740050046736546561)
        ·
          refine ⟨26921036055037535052409921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35894714740050046736546561 26921036055037535052409921)
          ·
            refine ⟨20190777041278151289307441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26921036055037535052409921 20190777041278151289307441)
            ·
              refine ⟨15143082780958613466980581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20190777041278151289307441 15143082780958613466980581)
              ·
                refine ⟨2839328021429740025058859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15143082780958613466980581 2839328021429740025058859)
                ·
                  refine ⟨4258992032144610037588289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2839328021429740025058859 4258992032144610037588289)
                  ·
                    refine ⟨3194244024108457528191217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4258992032144610037588289 3194244024108457528191217)
                    ·
                      refine ⟨2395683018081343146143413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194244024108457528191217 2395683018081343146143413)
                      ·
                        rfl

theorem cell23_4665576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_4665576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665576 prefixEnd_4665576 := by exact prefixLift 4665576
  have htrace : WordTrace (prefixWord ++ tailWord_4665576) baseStart_4665576 baseEnd_4665576 := by
    simpa [prefixWord, tailWord_4665576, baseEnd_4665576] using wordTrace_append hprefix tailTrace_4665576
  have hstable : (prefixWord ++ tailWord_4665576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665576).length < 2 ^ (prefixWord ++ tailWord_4665576).sum := by decide
  have hdescent : baseEnd_4665576 < baseStart_4665576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665592 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 2, 1, 3]
def baseStart_4665592 : Nat := 118140960795 + 4665592 * 2 ^ 59
def prefixEnd_4665592 : Nat := 4983230072969 + 3 ^ 40 * 4665592 * 2
def baseEnd_4665592 : Nat := 2395691233771815083543339

theorem tailTrace_4665592 : CollatzResearch.WordTrace tailWord_4665592 prefixEnd_4665592 2395691233771815083543339 := by
  unfold tailWord_4665592
  simp only [CollatzResearch.WordTrace]
  refine ⟨85084060056682239260327515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113445413408909652347103353 85084060056682239260327515)
  ·
    refine ⟨127626090085023358890491273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85084060056682239260327515 127626090085023358890491273)
    ·
      refine ⟨95719567563767519167868455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127626090085023358890491273 95719567563767519167868455)
      ·
        refine ⟨143579351345651278751802683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95719567563767519167868455 143579351345651278751802683)
        ·
          refine ⟨215369027018476918127704025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143579351345651278751802683 215369027018476918127704025)
          ·
            refine ⟨161526770263857688595778019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215369027018476918127704025 161526770263857688595778019)
            ·
              refine ⟨242290155395786532893667029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161526770263857688595778019 242290155395786532893667029)
              ·
                refine ⟨5678675517088746864695321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 242290155395786532893667029 5678675517088746864695321)
                ·
                  refine ⟨4259006637816560148521491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5678675517088746864695321 4259006637816560148521491)
                  ·
                    refine ⟨6388509956724840222782237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4259006637816560148521491 6388509956724840222782237)
                    ·
                      refine ⟨2395691233771815083543339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6388509956724840222782237 2395691233771815083543339)
                      ·
                        rfl

theorem cell23_4665592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_4665592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665592 prefixEnd_4665592 := by exact prefixLift 4665592
  have htrace : WordTrace (prefixWord ++ tailWord_4665592) baseStart_4665592 baseEnd_4665592 := by
    simpa [prefixWord, tailWord_4665592, baseEnd_4665592] using wordTrace_append hprefix tailTrace_4665592
  have hstable : (prefixWord ++ tailWord_4665592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665592).length < 2 ^ (prefixWord ++ tailWord_4665592).sum := by decide
  have hdescent : baseEnd_4665592 < baseStart_4665592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665635 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 3]
def baseStart_4665635 : Nat := 118140960795 + 4665635 * 2 ^ 59
def prefixEnd_4665635 : Nat := 4983230072969 + 3 ^ 40 * 4665635 * 2
def baseEnd_4665635 : Nat := 2395713313439958415305641

theorem tailTrace_4665635 : CollatzResearch.WordTrace tailWord_4665635 prefixEnd_4665635 2395713313439958415305641 := by
  unfold tailWord_4665635
  simp only [CollatzResearch.WordTrace]
  refine ⟨170169688452208696864470359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113446458968139131242980239 170169688452208696864470359)
  ·
    refine ⟨255254532678313045296705539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170169688452208696864470359 255254532678313045296705539)
    ·
      refine ⟨382881799017469567945058309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255254532678313045296705539 382881799017469567945058309)
      ·
        refine ⟨71790337315775543989698433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 382881799017469567945058309 71790337315775543989698433)
        ·
          refine ⟨53842752986831657992273825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71790337315775543989698433 53842752986831657992273825)
          ·
            refine ⟨40382064740123743494205369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53842752986831657992273825 40382064740123743494205369)
            ·
              refine ⟨30286548555092807620654027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40382064740123743494205369 30286548555092807620654027)
              ·
                refine ⟨45429822832639211430981041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30286548555092807620654027 45429822832639211430981041)
                ·
                  refine ⟨34072367124479408573235781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45429822832639211430981041 34072367124479408573235781)
                  ·
                    refine ⟨6388568835839889107481709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34072367124479408573235781 6388568835839889107481709)
                    ·
                      refine ⟨2395713313439958415305641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6388568835839889107481709 2395713313439958415305641)
                      ·
                        rfl

theorem cell23_4665635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_4665635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665635 prefixEnd_4665635 := by exact prefixLift 4665635
  have htrace : WordTrace (prefixWord ++ tailWord_4665635) baseStart_4665635 baseEnd_4665635 := by
    simpa [prefixWord, tailWord_4665635, baseEnd_4665635] using wordTrace_append hprefix tailTrace_4665635
  have hstable : (prefixWord ++ tailWord_4665635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665635).length < 2 ^ (prefixWord ++ tailWord_4665635).sum := by decide
  have hdescent : baseEnd_4665635 < baseStart_4665635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665652 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_4665652 : Nat := 118140960795 + 4665652 * 2 ^ 59
def prefixEnd_4665652 : Nat := 4983230072969 + 3 ^ 40 * 4665652 * 2
def baseEnd_4665652 : Nat := 2395722042611084848793063

theorem tailTrace_4665652 : CollatzResearch.WordTrace tailWord_4665652 prefixEnd_4665652 2395722042611084848793063 := by
  unfold tailWord_4665652
  simp only [CollatzResearch.WordTrace]
  refine ⟨85085154246573554383919605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113446872328764739178559473 85085154246573554383919605)
  ·
    refine ⟨7976733210616270723492463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85085154246573554383919605 7976733210616270723492463)
    ·
      refine ⟨11965099815924406085238695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7976733210616270723492463 11965099815924406085238695)
      ·
        refine ⟨17947649723886609127858043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11965099815924406085238695 17947649723886609127858043)
        ·
          refine ⟨26921474585829913691787065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17947649723886609127858043 26921474585829913691787065)
          ·
            refine ⟨20191105939372435268840299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26921474585829913691787065 20191105939372435268840299)
            ·
              refine ⟨30286658909058652903260449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20191105939372435268840299 30286658909058652903260449)
              ·
                refine ⟨22714994181793989677445337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30286658909058652903260449 22714994181793989677445337)
                ·
                  refine ⟨17036245636345492258084003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22714994181793989677445337 17036245636345492258084003)
                  ·
                    refine ⟨25554368454518238387126005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17036245636345492258084003 25554368454518238387126005)
                    ·
                      refine ⟨2395722042611084848793063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25554368454518238387126005 2395722042611084848793063)
                      ·
                        rfl

theorem cell23_4665652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_4665652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665652 prefixEnd_4665652 := by exact prefixLift 4665652
  have htrace : WordTrace (prefixWord ++ tailWord_4665652) baseStart_4665652 baseEnd_4665652 := by
    simpa [prefixWord, tailWord_4665652, baseEnd_4665652] using wordTrace_append hprefix tailTrace_4665652
  have hstable : (prefixWord ++ tailWord_4665652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665652).length < 2 ^ (prefixWord ++ tailWord_4665652).sum := by decide
  have hdescent : baseEnd_4665652 < baseStart_4665652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665695 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 5]
def baseStart_4665695 : Nat := 118140960795 + 4665695 * 2 ^ 59
def prefixEnd_4665695 : Nat := 4983230072969 + 3 ^ 40 * 4665695 * 2
def baseEnd_4665695 : Nat := 2395744122279228180555365

theorem tailTrace_4665695 : CollatzResearch.WordTrace tailWord_4665695 prefixEnd_4665695 2395744122279228180555365 := by
  unfold tailWord_4665695
  simp only [CollatzResearch.WordTrace]
  refine ⟨170171876831991327111654539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113447917887994218074436359 170171876831991327111654539)
  ·
    refine ⟨255257815247986990667481809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170171876831991327111654539 255257815247986990667481809)
    ·
      refine ⟨191443361435990243000611357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255257815247986990667481809 191443361435990243000611357)
      ·
        refine ⟨71791260538496341125229259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191443361435990243000611357 71791260538496341125229259)
        ·
          refine ⟨107686890807744511687843889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71791260538496341125229259 107686890807744511687843889)
          ·
            refine ⟨80765168105808383765882917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107686890807744511687843889 80765168105808383765882917)
            ·
              refine ⟨15143469019839071956103047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80765168105808383765882917 15143469019839071956103047)
              ·
                refine ⟨22715203529758607934154571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15143469019839071956103047 22715203529758607934154571)
                ·
                  refine ⟨34072805294637911901231857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22715203529758607934154571 34072805294637911901231857)
                  ·
                    refine ⟨25554603970978433925923893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34072805294637911901231857 25554603970978433925923893)
                    ·
                      refine ⟨2395744122279228180555365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25554603970978433925923893 2395744122279228180555365)
                      ·
                        rfl

theorem cell23_4665695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_4665695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665695 prefixEnd_4665695 := by exact prefixLift 4665695
  have htrace : WordTrace (prefixWord ++ tailWord_4665695) baseStart_4665695 baseEnd_4665695 := by
    simpa [prefixWord, tailWord_4665695, baseEnd_4665695] using wordTrace_append hprefix tailTrace_4665695
  have hstable : (prefixWord ++ tailWord_4665695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665695).length < 2 ^ (prefixWord ++ tailWord_4665695).sum := by decide
  have hdescent : baseEnd_4665695 < baseStart_4665695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665705 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 4]
def baseStart_4665705 : Nat := 118140960795 + 4665705 * 2 ^ 59
def prefixEnd_4665705 : Nat := 4983230072969 + 3 ^ 40 * 4665705 * 2
def baseEnd_4665705 : Nat := 2395749257085773141430319

theorem tailTrace_4665705 : CollatzResearch.WordTrace tailWord_4665705 prefixEnd_4665705 2395749257085773141430319 := by
  unfold tailWord_4665705
  simp only [CollatzResearch.WordTrace]
  refine ⟨170172241561955098819518569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113448161041303399213012379 170172241561955098819518569)
  ·
    refine ⟨127629181171466324114638927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170172241561955098819518569 127629181171466324114638927)
    ·
      refine ⟨191443771757199486171958391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127629181171466324114638927 191443771757199486171958391)
      ·
        refine ⟨287165657635799229257937587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191443771757199486171958391 287165657635799229257937587)
        ·
          refine ⟨430748486453698843886906381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287165657635799229257937587 430748486453698843886906381)
          ·
            refine ⟨161530682420137066457589893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 430748486453698843886906381 161530682420137066457589893)
            ·
              refine ⟨30287002953775699960798105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161530682420137066457589893 30287002953775699960798105)
              ·
                refine ⟨22715252215331774970598579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30287002953775699960798105 22715252215331774970598579)
                ·
                  refine ⟨34072878322997662455897869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22715252215331774970598579 34072878322997662455897869)
                  ·
                    refine ⟨12777329371124123420961701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34072878322997662455897869 12777329371124123420961701)
                    ·
                      refine ⟨2395749257085773141430319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12777329371124123420961701 2395749257085773141430319)
                      ·
                        rfl

theorem cell23_4665705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_4665705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665705 prefixEnd_4665705 := by exact prefixLift 4665705
  have htrace : WordTrace (prefixWord ++ tailWord_4665705) baseStart_4665705 baseEnd_4665705 := by
    simpa [prefixWord, tailWord_4665705, baseEnd_4665705] using wordTrace_append hprefix tailTrace_4665705
  have hstable : (prefixWord ++ tailWord_4665705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665705).length < 2 ^ (prefixWord ++ tailWord_4665705).sum := by decide
  have hdescent : baseEnd_4665705 < baseStart_4665705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665722 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2]
def baseStart_4665722 : Nat := 118140960795 + 4665722 * 2 ^ 59
def prefixEnd_4665722 : Nat := 4983230072969 + 3 ^ 40 * 4665722 * 2
def baseEnd_4665722 : Nat := 2395757986256899574917741

theorem tailTrace_4665722 : CollatzResearch.WordTrace tailWord_4665722 prefixEnd_4665722 2395757986256899574917741 := by
  unfold tailWord_4665722
  simp only [CollatzResearch.WordTrace]
  refine ⟨42543215400723377680721855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113448574401929007148591613 42543215400723377680721855)
  ·
    refine ⟨63814823101085066521082783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42543215400723377680721855 63814823101085066521082783)
    ·
      refine ⟨95722234651627599781624175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63814823101085066521082783 95722234651627599781624175)
      ·
        refine ⟨143583351977441399672436263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95722234651627599781624175 143583351977441399672436263)
        ·
          refine ⟨215375027966162099508654395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143583351977441399672436263 215375027966162099508654395)
          ·
            refine ⟨323062541949243149262981593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215375027966162099508654395 323062541949243149262981593)
            ·
              refine ⟨242296906461932361947236195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323062541949243149262981593 242296906461932361947236195)
              ·
                refine ⟨363445359692898542920854293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242296906461932361947236195 363445359692898542920854293)
                ·
                  refine ⟨17036501235604619199415045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 363445359692898542920854293 17036501235604619199415045)
                  ·
                    refine ⟨3194343981675866099890321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17036501235604619199415045 3194343981675866099890321)
                    ·
                      refine ⟨2395757986256899574917741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194343981675866099890321 2395757986256899574917741)
                      ·
                        rfl

theorem cell23_4665722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2].length) (baseStart_4665722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665722 prefixEnd_4665722 := by exact prefixLift 4665722
  have htrace : WordTrace (prefixWord ++ tailWord_4665722) baseStart_4665722 baseEnd_4665722 := by
    simpa [prefixWord, tailWord_4665722, baseEnd_4665722] using wordTrace_append hprefix tailTrace_4665722
  have hstable : (prefixWord ++ tailWord_4665722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665722).length < 2 ^ (prefixWord ++ tailWord_4665722).sum := by decide
  have hdescent : baseEnd_4665722 < baseStart_4665722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665732 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_4665732 : Nat := 118140960795 + 4665732 * 2 ^ 59
def prefixEnd_4665732 : Nat := 4983230072969 + 3 ^ 40 * 4665732 * 2
def baseEnd_4665732 : Nat := 798587707021148178597565

theorem tailTrace_4665732 : CollatzResearch.WordTrace tailWord_4665732 prefixEnd_4665732 798587707021148178597565 := by
  unfold tailWord_4665732
  simp only [CollatzResearch.WordTrace]
  refine ⟨85086613166428641215375725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113448817555238188287167633 85086613166428641215375725)
  ·
    refine ⟨31907479937410740455765897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85086613166428641215375725 31907479937410740455765897)
    ·
      refine ⟨23930609953058055341824423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31907479937410740455765897 23930609953058055341824423)
      ·
        refine ⟨35895914929587083012736635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23930609953058055341824423 35895914929587083012736635)
        ·
          refine ⟨53843872394380624519104953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35895914929587083012736635 53843872394380624519104953)
          ·
            refine ⟨40382904295785468389328715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53843872394380624519104953 40382904295785468389328715)
            ·
              refine ⟨60574356443678202583993073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40382904295785468389328715 60574356443678202583993073)
              ·
                refine ⟨45430767332758651937994805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60574356443678202583993073 45430767332758651937994805)
                ·
                  refine ⟨4259134437446123619187013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45430767332758651937994805 4259134437446123619187013)
                  ·
                    refine ⟨798587707021148178597565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4259134437446123619187013 798587707021148178597565)
                    ·
                      rfl

theorem cell23_4665732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_4665732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665732 prefixEnd_4665732 := by exact prefixLift 4665732
  have htrace : WordTrace (prefixWord ++ tailWord_4665732) baseStart_4665732 baseEnd_4665732 := by
    simpa [prefixWord, tailWord_4665732, baseEnd_4665732] using wordTrace_append hprefix tailTrace_4665732
  have hstable : (prefixWord ++ tailWord_4665732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665732).length < 2 ^ (prefixWord ++ tailWord_4665732).sum := by decide
  have hdescent : baseEnd_4665732 < baseStart_4665732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665735 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_4665735 : Nat := 118140960795 + 4665735 * 2 ^ 59
def prefixEnd_4665735 : Nat := 4983230072969 + 3 ^ 40 * 4665735 * 2
def baseEnd_4665735 : Nat := 2395764661505408024055181

theorem tailTrace_4665735 : CollatzResearch.WordTrace tailWord_4665735 prefixEnd_4665735 2395764661505408024055181 := by
  unfold tailWord_4665735
  simp only [CollatzResearch.WordTrace]
  refine ⟨170173335751846413943110659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113448890501230942628740439 170173335751846413943110659)
  ·
    refine ⟨255260003627769620914665989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170173335751846413943110659 255260003627769620914665989)
    ·
      refine ⟨47861250680206803921499873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255260003627769620914665989 47861250680206803921499873)
      ·
        refine ⟨35895938010155102941124905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47861250680206803921499873 35895938010155102941124905)
        ·
          refine ⟨26921953507616327205843679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35895938010155102941124905 26921953507616327205843679)
          ·
            refine ⟨40382930261424490808765519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26921953507616327205843679 40382930261424490808765519)
            ·
              refine ⟨60574395392136736213148279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40382930261424490808765519 60574395392136736213148279)
              ·
                refine ⟨90861593088205104319722419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60574395392136736213148279 90861593088205104319722419)
                ·
                  refine ⟨136292389632307656479583629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90861593088205104319722419 136292389632307656479583629)
                  ·
                    refine ⟨51109646112115371179843861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 136292389632307656479583629 51109646112115371179843861)
                    ·
                      refine ⟨2395764661505408024055181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51109646112115371179843861 2395764661505408024055181)
                      ·
                        rfl

theorem cell23_4665735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_4665735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665735 prefixEnd_4665735 := by exact prefixLift 4665735
  have htrace : WordTrace (prefixWord ++ tailWord_4665735) baseStart_4665735 baseEnd_4665735 := by
    simpa [prefixWord, tailWord_4665735, baseEnd_4665735] using wordTrace_append hprefix tailTrace_4665735
  have hstable : (prefixWord ++ tailWord_4665735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665735).length < 2 ^ (prefixWord ++ tailWord_4665735).sum := by decide
  have hdescent : baseEnd_4665735 < baseStart_4665735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665765 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_4665765 : Nat := 118140960795 + 4665765 * 2 ^ 59
def prefixEnd_4665765 : Nat := 4983230072969 + 3 ^ 40 * 4665765 * 2
def baseEnd_4665765 : Nat := 2395780065925042906680043

theorem tailTrace_4665765 : CollatzResearch.WordTrace tailWord_4665765 prefixEnd_4665765 2395780065925042906680043 := by
  unfold tailWord_4665765
  simp only [CollatzResearch.WordTrace]
  refine ⟨170174429941737729066702749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113449619961158486044468499 170174429941737729066702749)
  ·
    refine ⟨63815411228151648400013531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170174429941737729066702749 63815411228151648400013531)
    ·
      refine ⟨95723116842227472600020297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63815411228151648400013531 95723116842227472600020297)
      ·
        refine ⟨71792337631670604450015223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95723116842227472600020297 71792337631670604450015223)
        ·
          refine ⟨107688506447505906675022835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71792337631670604450015223 107688506447505906675022835)
          ·
            refine ⟨161532759671258860012534253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107688506447505906675022835 161532759671258860012534253)
            ·
              refine ⟨60574784876722072504700345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161532759671258860012534253 60574784876722072504700345)
              ·
                refine ⟨45431088657541554378525259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60574784876722072504700345 45431088657541554378525259)
                ·
                  refine ⟨68146632986312331567787889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45431088657541554378525259 68146632986312331567787889)
                  ·
                    refine ⟨51109974739734248675840917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68146632986312331567787889 51109974739734248675840917)
                    ·
                      refine ⟨2395780065925042906680043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51109974739734248675840917 2395780065925042906680043)
                      ·
                        rfl

theorem cell23_4665765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_4665765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665765 prefixEnd_4665765 := by exact prefixLift 4665765
  have htrace : WordTrace (prefixWord ++ tailWord_4665765) baseStart_4665765 baseEnd_4665765 := by
    simpa [prefixWord, tailWord_4665765, baseEnd_4665765] using wordTrace_append hprefix tailTrace_4665765
  have hstable : (prefixWord ++ tailWord_4665765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665765).length < 2 ^ (prefixWord ++ tailWord_4665765).sum := by decide
  have hdescent : baseEnd_4665765 < baseStart_4665765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665799 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 4, 3, 2]
def baseStart_4665799 : Nat := 118140960795 + 4665799 * 2 ^ 59
def prefixEnd_4665799 : Nat := 4983230072969 + 3 ^ 40 * 4665799 * 2
def baseEnd_4665799 : Nat := 2395797524267295773654887

theorem tailTrace_4665799 : CollatzResearch.WordTrace tailWord_4665799 prefixEnd_4665799 2395797524267295773654887 := by
  unfold tailWord_4665799
  simp only [CollatzResearch.WordTrace]
  refine ⟨170175670023614552873440451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113450446682409701915626967 170175670023614552873440451)
  ·
    refine ⟨255263505035421829310160677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170175670023614552873440451 255263505035421829310160677)
    ·
      refine ⟨47861907194141592995655127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255263505035421829310160677 47861907194141592995655127)
      ·
        refine ⟨71792860791212389493482691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47861907194141592995655127 71792860791212389493482691)
        ·
          refine ⟨107689291186818584240224037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71792860791212389493482691 107689291186818584240224037)
          ·
            refine ⟨20191742097528484545042007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107689291186818584240224037 20191742097528484545042007)
            ·
              refine ⟨30287613146292726817563011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20191742097528484545042007 30287613146292726817563011)
              ·
                refine ⟨45431419719439090226344517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30287613146292726817563011 45431419719439090226344517)
                ·
                  refine ⟨8518391197394829417439597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45431419719439090226344517 8518391197394829417439597)
                  ·
                    refine ⟨3194396699023061031539849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8518391197394829417439597 3194396699023061031539849)
                    ·
                      refine ⟨2395797524267295773654887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194396699023061031539849 2395797524267295773654887)
                      ·
                        rfl

theorem cell23_4665799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_4665799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665799 prefixEnd_4665799 := by exact prefixLift 4665799
  have htrace : WordTrace (prefixWord ++ tailWord_4665799) baseStart_4665799 baseEnd_4665799 := by
    simpa [prefixWord, tailWord_4665799, baseEnd_4665799] using wordTrace_append hprefix tailTrace_4665799
  have hstable : (prefixWord ++ tailWord_4665799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665799).length < 2 ^ (prefixWord ++ tailWord_4665799).sum := by decide
  have hdescent : baseEnd_4665799 < baseStart_4665799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665835 : List Nat := [1, 1, 1, 1, 2, 3, 3, 11]
def baseStart_4665835 : Nat := 118140960795 + 4665835 * 2 ^ 59
def prefixEnd_4665835 : Nat := 4983230072969 + 3 ^ 40 * 4665835 * 2
def baseEnd_4665835 : Nat := 88733926280402134548323

theorem tailTrace_4665835 : CollatzResearch.WordTrace tailWord_4665835 prefixEnd_4665835 88733926280402134548323 := by
  unfold tailWord_4665835
  simp only [CollatzResearch.WordTrace]
  refine ⟨170176983051484131021750959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113451322034322754014500639 170176983051484131021750959)
  ·
    refine ⟨255265474577226196532626439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170176983051484131021750959 255265474577226196532626439)
    ·
      refine ⟨382898211865839294798939659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255265474577226196532626439 382898211865839294798939659)
      ·
        refine ⟨574347317798758942198409489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382898211865839294798939659 574347317798758942198409489)
        ·
          refine ⟨430760488349069206648807117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 574347317798758942198409489 430760488349069206648807117)
          ·
            refine ⟨161535183130900952493302669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 430760488349069206648807117 161535183130900952493302669)
            ·
              refine ⟨60575693674087857184988501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161535183130900952493302669 60575693674087857184988501)
              ·
                refine ⟨88733926280402134548323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 60575693674087857184988501 88733926280402134548323)
                ·
                  rfl

theorem cell23_4665835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 11].length) (baseStart_4665835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665835 prefixEnd_4665835 := by exact prefixLift 4665835
  have htrace : WordTrace (prefixWord ++ tailWord_4665835) baseStart_4665835 baseEnd_4665835 := by
    simpa [prefixWord, tailWord_4665835, baseEnd_4665835] using wordTrace_append hprefix tailTrace_4665835
  have hstable : (prefixWord ++ tailWord_4665835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665835).length < 2 ^ (prefixWord ++ tailWord_4665835).sum := by decide
  have hdescent : baseEnd_4665835 < baseStart_4665835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665849 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 1, 2, 3]
def baseStart_4665849 : Nat := 118140960795 + 4665849 * 2 ^ 59
def prefixEnd_4665849 : Nat := 4983230072969 + 3 ^ 40 * 4665849 * 2
def baseEnd_4665849 : Nat := 2395823198300020578029657

theorem tailTrace_4665849 : CollatzResearch.WordTrace tailWord_4665849 prefixEnd_4665849 2395823198300020578029657 := by
  unfold tailWord_4665849
  simp only [CollatzResearch.WordTrace]
  refine ⟨170177493673433411412760601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113451662448955607608507067 170177493673433411412760601)
  ·
    refine ⟨127633120255075058559570451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170177493673433411412760601 127633120255075058559570451)
    ·
      refine ⟨191449680382612587839355677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127633120255075058559570451 191449680382612587839355677)
      ·
        refine ⟨71793630143479720439758379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191449680382612587839355677 71793630143479720439758379)
        ·
          refine ⟨107690445215219580659637569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71793630143479720439758379 107690445215219580659637569)
          ·
            refine ⟨80767833911414685494728177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107690445215219580659637569 80767833911414685494728177)
            ·
              refine ⟨60575875433561014121046133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80767833911414685494728177 60575875433561014121046133)
              ·
                refine ⟨5678988321896345073848075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60575875433561014121046133 5678988321896345073848075)
                ·
                  refine ⟨8518482482844517610772113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5678988321896345073848075 8518482482844517610772113)
                  ·
                    refine ⟨6388861862133388208079085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8518482482844517610772113 6388861862133388208079085)
                    ·
                      refine ⟨2395823198300020578029657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6388861862133388208079085 2395823198300020578029657)
                      ·
                        rfl

theorem cell23_4665849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_4665849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665849 prefixEnd_4665849 := by exact prefixLift 4665849
  have htrace : WordTrace (prefixWord ++ tailWord_4665849) baseStart_4665849 baseEnd_4665849 := by
    simpa [prefixWord, tailWord_4665849, baseEnd_4665849] using wordTrace_append hprefix tailTrace_4665849
  have hstable : (prefixWord ++ tailWord_4665849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665849).length < 2 ^ (prefixWord ++ tailWord_4665849).sum := by decide
  have hdescent : baseEnd_4665849 < baseStart_4665849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665876 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_4665876 : Nat := 118140960795 + 4665876 * 2 ^ 59
def prefixEnd_4665876 : Nat := 4983230072969 + 3 ^ 40 * 4665876 * 2
def baseEnd_4665876 : Nat := 2395837062277691972392033

theorem tailTrace_4665876 : CollatzResearch.WordTrace tailWord_4665876 prefixEnd_4665876 2395837062277691972392033 := by
  unfold tailWord_4665876
  simp only [CollatzResearch.WordTrace]
  refine ⟨85089239222167797511996741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113452318962890396682662321 85089239222167797511996741)
  ·
    refine ⟨15954232354156462033499389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85089239222167797511996741 15954232354156462033499389)
    ·
      refine ⟨5982837132808673262562271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15954232354156462033499389 5982837132808673262562271)
      ·
        refine ⟨8974255699213009893843407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5982837132808673262562271 8974255699213009893843407)
        ·
          refine ⟨13461383548819514840765111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8974255699213009893843407 13461383548819514840765111)
          ·
            refine ⟨20192075323229272261147667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13461383548819514840765111 20192075323229272261147667)
            ·
              refine ⟨30288112984843908391721501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20192075323229272261147667 30288112984843908391721501)
              ·
                refine ⟨11358042369316465646895563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30288112984843908391721501 11358042369316465646895563)
                ·
                  refine ⟨17037063553974698470343345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11358042369316465646895563 17037063553974698470343345)
                  ·
                    refine ⟨12777797665481023852757509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17037063553974698470343345 12777797665481023852757509)
                    ·
                      refine ⟨2395837062277691972392033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12777797665481023852757509 2395837062277691972392033)
                      ·
                        rfl

theorem cell23_4665876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_4665876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665876 prefixEnd_4665876 := by exact prefixLift 4665876
  have htrace : WordTrace (prefixWord ++ tailWord_4665876) baseStart_4665876 baseEnd_4665876 := by
    simpa [prefixWord, tailWord_4665876, baseEnd_4665876] using wordTrace_append hprefix tailTrace_4665876
  have hstable : (prefixWord ++ tailWord_4665876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665876).length < 2 ^ (prefixWord ++ tailWord_4665876).sum := by decide
  have hdescent : baseEnd_4665876 < baseStart_4665876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665896 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_4665896 : Nat := 118140960795 + 4665896 * 2 ^ 59
def prefixEnd_4665896 : Nat := 4983230072969 + 3 ^ 40 * 4665896 * 2
def baseEnd_4665896 : Nat := 2395847331890781894141941

theorem tailTrace_4665896 : CollatzResearch.WordTrace tailWord_4665896 prefixEnd_4665896 2395847331890781894141941 := by
  unfold tailWord_4665896
  simp only [CollatzResearch.WordTrace]
  refine ⟨85089603952131569219860771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113452805269508758959814361 85089603952131569219860771)
  ·
    refine ⟨127634405928197353829791157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85089603952131569219860771 127634405928197353829791157)
    ·
      refine ⟨11965725555768501921542921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127634405928197353829791157 11965725555768501921542921)
      ·
        refine ⟨8974294166826376441157191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11965725555768501921542921 8974294166826376441157191)
        ·
          refine ⟨13461441250239564661735787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8974294166826376441157191 13461441250239564661735787)
          ·
            refine ⟨20192161875359346992603681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13461441250239564661735787 20192161875359346992603681)
            ·
              refine ⟨15144121406519510244452761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20192161875359346992603681 15144121406519510244452761)
              ·
                refine ⟨11358091054889632683339571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15144121406519510244452761 11358091054889632683339571)
                ·
                  refine ⟨17037136582334449025009357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11358091054889632683339571 17037136582334449025009357)
                  ·
                    refine ⟨6388926218375418384378509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17037136582334449025009357 6388926218375418384378509)
                    ·
                      refine ⟨2395847331890781894141941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6388926218375418384378509 2395847331890781894141941)
                      ·
                        rfl

theorem cell23_4665896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_4665896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665896 prefixEnd_4665896 := by exact prefixLift 4665896
  have htrace : WordTrace (prefixWord ++ tailWord_4665896) baseStart_4665896 baseEnd_4665896 := by
    simpa [prefixWord, tailWord_4665896, baseEnd_4665896] using wordTrace_append hprefix tailTrace_4665896
  have hstable : (prefixWord ++ tailWord_4665896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665896).length < 2 ^ (prefixWord ++ tailWord_4665896).sum := by decide
  have hdescent : baseEnd_4665896 < baseStart_4665896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4665912 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 4, 6]
def baseStart_4665912 : Nat := 118140960795 + 4665912 * 2 ^ 59
def prefixEnd_4665912 : Nat := 4983230072969 + 3 ^ 40 * 4665912 * 2
def baseEnd_4665912 : Nat := 798618515860417943847289

theorem tailTrace_4665912 : CollatzResearch.WordTrace tailWord_4665912 prefixEnd_4665912 798618515860417943847289 := by
  unfold tailWord_4665912
  simp only [CollatzResearch.WordTrace]
  refine ⟨85089895736102586586151995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113453194314803448781535993 85089895736102586586151995)
  ·
    refine ⟨127634843604153879879227993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85089895736102586586151995 127634843604153879879227993)
    ·
      refine ⟨95726132703115409909420995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127634843604153879879227993 95726132703115409909420995)
      ·
        refine ⟨143589199054673114864131493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95726132703115409909420995 143589199054673114864131493)
        ·
          refine ⟨26922974822751209037024655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143589199054673114864131493 26922974822751209037024655)
          ·
            refine ⟨40384462234126813555536983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26922974822751209037024655 40384462234126813555536983)
            ·
              refine ⟨60576693351190220333305475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40384462234126813555536983 60576693351190220333305475)
              ·
                refine ⟨90865040026785330499958213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60576693351190220333305475 90865040026785330499958213)
                ·
                  refine ⟨17037195005022249468742165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90865040026785330499958213 17037195005022249468742165)
                  ·
                    refine ⟨798618515860417943847289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17037195005022249468742165 798618515860417943847289)
                    ·
                      rfl

theorem cell23_4665912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_4665912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4665912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4665912 prefixEnd_4665912 := by exact prefixLift 4665912
  have htrace : WordTrace (prefixWord ++ tailWord_4665912) baseStart_4665912 baseEnd_4665912 := by
    simpa [prefixWord, tailWord_4665912, baseEnd_4665912] using wordTrace_append hprefix tailTrace_4665912
  have hstable : (prefixWord ++ tailWord_4665912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4665912).length < 2 ^ (prefixWord ++ tailWord_4665912).sum := by decide
  have hdescent : baseEnd_4665912 < baseStart_4665912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4665912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666019 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 7, 4]
def baseStart_4666019 : Nat := 118140960795 + 4666019 * 2 ^ 59
def prefixEnd_4666019 : Nat := 4983230072969 + 3 ^ 40 * 4666019 * 2
def baseEnd_4666019 : Nat := 798636830003761637634625

theorem tailTrace_4666019 : CollatzResearch.WordTrace tailWord_4666019 prefixEnd_4666019 798636830003761637634625 := by
  unfold tailWord_4666019
  simp only [CollatzResearch.WordTrace]
  refine ⟨170183694082817530446449111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113455796055211686964299407 170183694082817530446449111)
  ·
    refine ⟨255275541124226295669673667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170183694082817530446449111 255275541124226295669673667)
    ·
      refine ⟨382913311686339443504510501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255275541124226295669673667 382913311686339443504510501)
      ·
        refine ⟨71796245941188645657095719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 382913311686339443504510501 71796245941188645657095719)
        ·
          refine ⟨107694368911782968485643579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71796245941188645657095719 107694368911782968485643579)
          ·
            refine ⟨161541553367674452728465369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107694368911782968485643579 161541553367674452728465369)
            ·
              refine ⟨121156165025755839546349027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161541553367674452728465369 121156165025755839546349027)
              ·
                refine ⟨181734247538633759319523541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121156165025755839546349027 181734247538633759319523541)
                ·
                  refine ⟨4259396426686728734051333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 181734247538633759319523541 4259396426686728734051333)
                  ·
                    refine ⟨798636830003761637634625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4259396426686728734051333 798636830003761637634625)
                    ·
                      rfl

theorem cell23_4666019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 4].length) (baseStart_4666019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666019 prefixEnd_4666019 := by exact prefixLift 4666019
  have htrace : WordTrace (prefixWord ++ tailWord_4666019) baseStart_4666019 baseEnd_4666019 := by
    simpa [prefixWord, tailWord_4666019, baseEnd_4666019] using wordTrace_append hprefix tailTrace_4666019
  have hstable : (prefixWord ++ tailWord_4666019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666019).length < 2 ^ (prefixWord ++ tailWord_4666019).sum := by decide
  have hdescent : baseEnd_4666019 < baseStart_4666019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666046 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_4666046 : Nat := 118140960795 + 4666046 * 2 ^ 59
def prefixEnd_4666046 : Nat := 4983230072969 + 3 ^ 40 * 4666046 * 2
def baseEnd_4666046 : Nat := 2395924353988956307266251

theorem tailTrace_4666046 : CollatzResearch.WordTrace tailWord_4666046 prefixEnd_4666046 2395924353988956307266251 := by
  unfold tailWord_4666046
  simp only [CollatzResearch.WordTrace]
  refine ⟨21273084856714964257210249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113456452569146476038454661 21273084856714964257210249)
  ·
    refine ⟨15954813642536223192907687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21273084856714964257210249 15954813642536223192907687)
    ·
      refine ⟨23932220463804334789361531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15954813642536223192907687 23932220463804334789361531)
      ·
        refine ⟨35898330695706502184042297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23932220463804334789361531 35898330695706502184042297)
        ·
          refine ⟨26923748021779876638031723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35898330695706502184042297 26923748021779876638031723)
          ·
            refine ⟨40385622032669814957047585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26923748021779876638031723 40385622032669814957047585)
            ·
              refine ⟨30289216524502361217785689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40385622032669814957047585 30289216524502361217785689)
              ·
                refine ⟨22716912393376770913339267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30289216524502361217785689 22716912393376770913339267)
                ·
                  refine ⟨34075368590065156370008901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22716912393376770913339267 34075368590065156370008901)
                  ·
                    refine ⟨6389131610637216819376669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34075368590065156370008901 6389131610637216819376669)
                    ·
                      refine ⟨2395924353988956307266251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6389131610637216819376669 2395924353988956307266251)
                      ·
                        rfl

theorem cell23_4666046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_4666046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666046 prefixEnd_4666046 := by exact prefixLift 4666046
  have htrace : WordTrace (prefixWord ++ tailWord_4666046) baseStart_4666046 baseEnd_4666046 := by
    simpa [prefixWord, tailWord_4666046, baseEnd_4666046] using wordTrace_append hprefix tailTrace_4666046
  have hstable : (prefixWord ++ tailWord_4666046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666046).length < 2 ^ (prefixWord ++ tailWord_4666046).sum := by decide
  have hdescent : baseEnd_4666046 < baseStart_4666046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666083 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 6]
def baseStart_4666083 : Nat := 118140960795 + 4666083 * 2 ^ 59
def prefixEnd_4666083 : Nat := 4983230072969 + 3 ^ 40 * 4666083 * 2
def baseEnd_4666083 : Nat := 266215928085908073611509

theorem tailTrace_4666083 : CollatzResearch.WordTrace tailWord_4666083 prefixEnd_4666083 266215928085908073611509 := by
  unfold tailWord_4666083
  simp only [CollatzResearch.WordTrace]
  refine ⟨170186028354585669376778903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113457352236390446251185935 170186028354585669376778903)
  ·
    refine ⟨255279042531878504065168355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170186028354585669376778903 255279042531878504065168355)
    ·
      refine ⟨382918563797817756097752533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255279042531878504065168355 382918563797817756097752533)
      ·
        refine ⟨8974653839011353658541075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 382918563797817756097752533 8974653839011353658541075)
        ·
          refine ⟨13461980758517030487811613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8974653839011353658541075 13461980758517030487811613)
          ·
            refine ⟨5048242784443886432929355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13461980758517030487811613 5048242784443886432929355)
            ·
              refine ⟨7572364176665829649394033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5048242784443886432929355 7572364176665829649394033)
              ·
                refine ⟨5679273132499372237045525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7572364176665829649394033 5679273132499372237045525)
                ·
                  refine ⟨266215928085908073611509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5679273132499372237045525 266215928085908073611509)
                  ·
                    rfl

theorem cell23_4666083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 6].length) (baseStart_4666083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666083 prefixEnd_4666083 := by exact prefixLift 4666083
  have htrace : WordTrace (prefixWord ++ tailWord_4666083) baseStart_4666083 baseEnd_4666083 := by
    simpa [prefixWord, tailWord_4666083, baseEnd_4666083] using wordTrace_append hprefix tailTrace_4666083
  have hstable : (prefixWord ++ tailWord_4666083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666083).length < 2 ^ (prefixWord ++ tailWord_4666083).sum := by decide
  have hdescent : baseEnd_4666083 < baseStart_4666083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666110 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_4666110 : Nat := 118140960795 + 4666110 * 2 ^ 59
def prefixEnd_4666110 : Nat := 4983230072969 + 3 ^ 40 * 4666110 * 2
def baseEnd_4666110 : Nat := 2395957216750844056865957

theorem tailTrace_4666110 : CollatzResearch.WordTrace tailWord_4666110 prefixEnd_4666110 2395957216750844056865957 := by
  unfold tailWord_4666110
  simp only [CollatzResearch.WordTrace]
  refine ⟨21273376640685981623501473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113458008750325235325341189 21273376640685981623501473)
  ·
    refine ⟨15955032480514486217626105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21273376640685981623501473 15955032480514486217626105)
    ·
      refine ⟨11966274360385864663219579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15955032480514486217626105 11966274360385864663219579)
      ·
        refine ⟨17949411540578796994829369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11966274360385864663219579 17949411540578796994829369)
        ·
          refine ⟨13462058655434097746122027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17949411540578796994829369 13462058655434097746122027)
          ·
            refine ⟨20193087983151146619183041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13462058655434097746122027 20193087983151146619183041)
            ·
              refine ⟨15144815987363359964387281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20193087983151146619183041 15144815987363359964387281)
              ·
                refine ⟨11358611990522519973290461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15144815987363359964387281 11358611990522519973290461)
                ·
                  refine ⟨4259479496445944989983923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11358611990522519973290461 4259479496445944989983923)
                  ·
                    refine ⟨6389219244668917484975885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4259479496445944989983923 6389219244668917484975885)
                    ·
                      refine ⟨2395957216750844056865957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6389219244668917484975885 2395957216750844056865957)
                      ·
                        rfl

theorem cell23_4666110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_4666110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666110 prefixEnd_4666110 := by exact prefixLift 4666110
  have htrace : WordTrace (prefixWord ++ tailWord_4666110) baseStart_4666110 baseEnd_4666110 := by
    simpa [prefixWord, tailWord_4666110, baseEnd_4666110] using wordTrace_append hprefix tailTrace_4666110
  have hstable : (prefixWord ++ tailWord_4666110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666110).length < 2 ^ (prefixWord ++ tailWord_4666110).sum := by decide
  have hdescent : baseEnd_4666110 < baseStart_4666110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666136 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 5, 2, 3]
def baseStart_4666136 : Nat := 118140960795 + 4666136 * 2 ^ 59
def prefixEnd_4666136 : Nat := 4983230072969 + 3 ^ 40 * 4666136 * 2
def baseEnd_4666136 : Nat := 2395970567247860955140837

theorem tailTrace_4666136 : CollatzResearch.WordTrace tailWord_4666136 prefixEnd_4666136 2395970567247860955140837 := by
  unfold tailWord_4666136
  simp only [CollatzResearch.WordTrace]
  refine ⟨85093980711696829714229131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113458640948929106285638841 85093980711696829714229131)
  ·
    refine ⟨127640971067545244571343697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85093980711696829714229131 127640971067545244571343697)
    ·
      refine ⟨95730728300658933428507773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127640971067545244571343697 95730728300658933428507773)
      ·
        refine ⟨35899023112747100035690415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95730728300658933428507773 35899023112747100035690415)
        ·
          refine ⟨53848534669120650053535623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35899023112747100035690415 53848534669120650053535623)
          ·
            refine ⟨80772802003680975080303435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53848534669120650053535623 80772802003680975080303435)
            ·
              refine ⟨121159203005521462620455153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80772802003680975080303435 121159203005521462620455153)
              ·
                refine ⟨90869402254141096965341365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121159203005521462620455153 90869402254141096965341365)
                ·
                  refine ⟨8519006461325727840500753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90869402254141096965341365 8519006461325727840500753)
                  ·
                    refine ⟨6389254845994295880375565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8519006461325727840500753 6389254845994295880375565)
                    ·
                      refine ⟨2395970567247860955140837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6389254845994295880375565 2395970567247860955140837)
                      ·
                        rfl

theorem cell23_4666136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_4666136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666136 prefixEnd_4666136 := by exact prefixLift 4666136
  have htrace : WordTrace (prefixWord ++ tailWord_4666136) baseStart_4666136 baseEnd_4666136 := by
    simpa [prefixWord, tailWord_4666136, baseEnd_4666136] using wordTrace_append hprefix tailTrace_4666136
  have hstable : (prefixWord ++ tailWord_4666136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666136).length < 2 ^ (prefixWord ++ tailWord_4666136).sum := by decide
  have hdescent : baseEnd_4666136 < baseStart_4666136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666146 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_4666146 : Nat := 118140960795 + 4666146 * 2 ^ 59
def prefixEnd_4666146 : Nat := 4983230072969 + 3 ^ 40 * 4666146 * 2
def baseEnd_4666146 : Nat := 2395975702054405916015791

theorem tailTrace_4666146 : CollatzResearch.WordTrace tailWord_4666146 prefixEnd_4666146 2395975702054405916015791 := by
  unfold tailWord_4666146
  simp only [CollatzResearch.WordTrace]
  refine ⟨42547081538339357784080573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113458884102238287424214861 42547081538339357784080573)
  ·
    refine ⟨15955155576877259169030215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42547081538339357784080573 15955155576877259169030215)
    ·
      refine ⟨23932733365315888753545323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15955155576877259169030215 23932733365315888753545323)
      ·
        refine ⟨35899100047973833130317985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23932733365315888753545323 35899100047973833130317985)
        ·
          refine ⟨26924325035980374847738489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35899100047973833130317985 26924325035980374847738489)
          ·
            refine ⟨20193243776985281135803867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26924325035980374847738489 20193243776985281135803867)
            ·
              refine ⟨30289865665477921703705801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20193243776985281135803867 30289865665477921703705801)
              ·
                refine ⟨22717399249108441277779351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30289865665477921703705801 22717399249108441277779351)
                ·
                  refine ⟨34076098873662661916669027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22717399249108441277779351 34076098873662661916669027)
                  ·
                    refine ⟨51114148310493992875003541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34076098873662661916669027 51114148310493992875003541)
                    ·
                      refine ⟨2395975702054405916015791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51114148310493992875003541 2395975702054405916015791)
                      ·
                        rfl

theorem cell23_4666146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_4666146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666146 prefixEnd_4666146 := by exact prefixLift 4666146
  have htrace : WordTrace (prefixWord ++ tailWord_4666146) baseStart_4666146 baseEnd_4666146 := by
    simpa [prefixWord, tailWord_4666146, baseEnd_4666146] using wordTrace_append hprefix tailTrace_4666146
  have hstable : (prefixWord ++ tailWord_4666146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666146).length < 2 ^ (prefixWord ++ tailWord_4666146).sum := by decide
  have hdescent : baseEnd_4666146 < baseStart_4666146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666216 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 1, 8]
def baseStart_4666216 : Nat := 118140960795 + 4666216 * 2 ^ 59
def prefixEnd_4666216 : Nat := 4983230072969 + 3 ^ 40 * 4666216 * 2
def baseEnd_4666216 : Nat := 798670548566740214046823

theorem tailTrace_4666216 : CollatzResearch.WordTrace tailWord_4666216 prefixEnd_4666216 798670548566740214046823 := by
  unfold tailWord_4666216
  simp only [CollatzResearch.WordTrace]
  refine ⟨85095439631551916545685251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113460586175402555394247001 85095439631551916545685251)
  ·
    refine ⟨127643159447327874818527877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85095439631551916545685251 127643159447327874818527877)
    ·
      refine ⟨23933092396373976528473977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127643159447327874818527877 23933092396373976528473977)
      ·
        refine ⟨17949819297280482396355483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23933092396373976528473977 17949819297280482396355483)
        ·
          refine ⟨26924728945920723594533225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17949819297280482396355483 26924728945920723594533225)
          ·
            refine ⟨20193546709440542695899919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26924728945920723594533225 20193546709440542695899919)
            ·
              refine ⟨30290320064160814043849879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20193546709440542695899919 30290320064160814043849879)
              ·
                refine ⟨45435480096241221065774819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30290320064160814043849879 45435480096241221065774819)
                ·
                  refine ⟨68153220144361831598662229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45435480096241221065774819 68153220144361831598662229)
                  ·
                    refine ⟨798670548566740214046823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68153220144361831598662229 798670548566740214046823)
                    ·
                      rfl

theorem cell23_4666216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_4666216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666216 prefixEnd_4666216 := by exact prefixLift 4666216
  have htrace : WordTrace (prefixWord ++ tailWord_4666216) baseStart_4666216 baseEnd_4666216 := by
    simpa [prefixWord, tailWord_4666216, baseEnd_4666216] using wordTrace_append hprefix tailTrace_4666216
  have hstable : (prefixWord ++ tailWord_4666216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666216).length < 2 ^ (prefixWord ++ tailWord_4666216).sum := by decide
  have hdescent : baseEnd_4666216 < baseStart_4666216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666226 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_4666226 : Nat := 118140960795 + 4666226 * 2 ^ 59
def prefixEnd_4666226 : Nat := 4983230072969 + 3 ^ 40 * 4666226 * 2
def baseEnd_4666226 : Nat := 2396016780506765603015423

theorem tailTrace_4666226 : CollatzResearch.WordTrace tailWord_4666226 prefixEnd_4666226 2396016780506765603015423 := by
  unfold tailWord_4666226
  simp only [CollatzResearch.WordTrace]
  refine ⟨42547810998266901199808633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113460829328711736532823021 42547810998266901199808633)
  ·
    refine ⟨31910858248700175899856475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42547810998266901199808633 31910858248700175899856475)
    ·
      refine ⟨47866287373050263849784713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31910858248700175899856475 47866287373050263849784713)
      ·
        refine ⟨35899715529787697887338535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47866287373050263849784713 35899715529787697887338535)
        ·
          refine ⟨53849573294681546831007803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35899715529787697887338535 53849573294681546831007803)
          ·
            refine ⟨80774359942022320246511705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53849573294681546831007803 80774359942022320246511705)
            ·
              refine ⟨60580769956516740184883779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80774359942022320246511705 60580769956516740184883779)
              ·
                refine ⟨90871154934775110277325669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60580769956516740184883779 90871154934775110277325669)
                ·
                  refine ⟨17038341550270333176998563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90871154934775110277325669 17038341550270333176998563)
                  ·
                    refine ⟨25557512325405499765497845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17038341550270333176998563 25557512325405499765497845)
                    ·
                      refine ⟨2396016780506765603015423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25557512325405499765497845 2396016780506765603015423)
                      ·
                        rfl

theorem cell23_4666226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_4666226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666226 prefixEnd_4666226 := by exact prefixLift 4666226
  have htrace : WordTrace (prefixWord ++ tailWord_4666226) baseStart_4666226 baseEnd_4666226 := by
    simpa [prefixWord, tailWord_4666226, baseEnd_4666226] using wordTrace_append hprefix tailTrace_4666226
  have hstable : (prefixWord ++ tailWord_4666226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666226).length < 2 ^ (prefixWord ++ tailWord_4666226).sum := by decide
  have hdescent : baseEnd_4666226 < baseStart_4666226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666263 : List Nat := [1, 1, 3, 3, 1, 2, 1, 6, 5]
def baseStart_4666263 : Nat := 118140960795 + 4666263 * 2 ^ 59
def prefixEnd_4666263 : Nat := 4983230072969 + 3 ^ 40 * 4666263 * 2
def baseEnd_4666263 : Nat := 266226197698997995361417

theorem tailTrace_4666263 : CollatzResearch.WordTrace tailWord_4666263 prefixEnd_4666263 266226197698997995361417 := by
  unfold tailWord_4666263
  simp only [CollatzResearch.WordTrace]
  refine ⟨170192593493933560118331443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113461728995955706745554295 170192593493933560118331443)
  ·
    refine ⟨255288890240900340177497165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170192593493933560118331443 255288890240900340177497165)
    ·
      refine ⟨95733333840337627566561437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255288890240900340177497165 95733333840337627566561437)
      ·
        refine ⟨35900000190126610337460539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95733333840337627566561437 35900000190126610337460539)
        ·
          refine ⟨53850000285189915506190809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35900000190126610337460539 53850000285189915506190809)
          ·
            refine ⟨40387500213892436629643107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53850000285189915506190809 40387500213892436629643107)
            ·
              refine ⟨60581250320838654944464661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40387500213892436629643107 60581250320838654944464661)
              ·
                refine ⟨2839746108789311950521781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60581250320838654944464661 2839746108789311950521781)
                ·
                  refine ⟨266226197698997995361417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2839746108789311950521781 266226197698997995361417)
                  ·
                    rfl

theorem cell23_4666263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 5].length) (baseStart_4666263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666263 prefixEnd_4666263 := by exact prefixLift 4666263
  have htrace : WordTrace (prefixWord ++ tailWord_4666263) baseStart_4666263 baseEnd_4666263 := by
    simpa [prefixWord, tailWord_4666263, baseEnd_4666263] using wordTrace_append hprefix tailTrace_4666263
  have hstable : (prefixWord ++ tailWord_4666263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666263).length < 2 ^ (prefixWord ++ tailWord_4666263).sum := by decide
  have hdescent : baseEnd_4666263 < baseStart_4666263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666276 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_4666276 : Nat := 118140960795 + 4666276 * 2 ^ 59
def prefixEnd_4666276 : Nat := 4983230072969 + 3 ^ 40 * 4666276 * 2
def baseEnd_4666276 : Nat := 798680818179830135796731

theorem tailTrace_4666276 : CollatzResearch.WordTrace tailWord_4666276 prefixEnd_4666276 798680818179830135796731 := by
  unfold tailWord_4666276
  simp only [CollatzResearch.WordTrace]
  refine ⟨85096533821443231669277341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113462045095257642225703121 85096533821443231669277341)
  ·
    refine ⟨31911200183041211875979003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85096533821443231669277341 31911200183041211875979003)
    ·
      refine ⟨47866800274561817813968505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31911200183041211875979003 47866800274561817813968505)
      ·
        refine ⟨35900100205921363360476379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47866800274561817813968505 35900100205921363360476379)
        ·
          refine ⟨53850150308882045040714569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35900100205921363360476379 53850150308882045040714569)
          ·
            refine ⟨40387612731661533780535927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53850150308882045040714569 40387612731661533780535927)
            ·
              refine ⟨60581419097492300670803891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40387612731661533780535927 60581419097492300670803891)
              ·
                refine ⟨90872128646238451006205837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60581419097492300670803891 90872128646238451006205837)
                ·
                  refine ⟨34077048242339419127327189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90872128646238451006205837 34077048242339419127327189)
                  ·
                    refine ⟨798680818179830135796731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34077048242339419127327189 798680818179830135796731)
                    ·
                      rfl

theorem cell23_4666276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_4666276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666276 prefixEnd_4666276 := by exact prefixLift 4666276
  have htrace : WordTrace (prefixWord ++ tailWord_4666276) baseStart_4666276 baseEnd_4666276 := by
    simpa [prefixWord, tailWord_4666276, baseEnd_4666276] using wordTrace_append hprefix tailTrace_4666276
  have hstable : (prefixWord ++ tailWord_4666276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666276).length < 2 ^ (prefixWord ++ tailWord_4666276).sum := by decide
  have hdescent : baseEnd_4666276 < baseStart_4666276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666293 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_4666293 : Nat := 118140960795 + 4666293 * 2 ^ 59
def prefixEnd_4666293 : Nat := 4983230072969 + 3 ^ 40 * 4666293 * 2
def baseEnd_4666293 : Nat := 798683727903538946959205

theorem tailTrace_4666293 : CollatzResearch.WordTrace tailWord_4666293 prefixEnd_4666293 798683727903538946959205 := by
  unfold tailWord_4666293
  simp only [CollatzResearch.WordTrace]
  refine ⟨170193687683824875241923533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113462458455883250161282355 170193687683824875241923533)
  ·
    refine ⟨63822632881434328215721325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170193687683824875241923533 63822632881434328215721325)
    ·
      refine ⟨23933487330537873080895497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63822632881434328215721325 23933487330537873080895497)
      ·
        refine ⟨17950115497903404810671623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23933487330537873080895497 17950115497903404810671623)
        ·
          refine ⟨26925173246855107216007435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17950115497903404810671623 26925173246855107216007435)
          ·
            refine ⟨40387759870282660824011153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26925173246855107216007435 40387759870282660824011153)
            ·
              refine ⟨30290819902711995618008365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40387759870282660824011153 30290819902711995618008365)
              ·
                refine ⟨11359057463516998356753137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30290819902711995618008365 11359057463516998356753137)
                ·
                  refine ⟨8519293097637748767564853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11359057463516998356753137 8519293097637748767564853)
                  ·
                    refine ⟨798683727903538946959205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8519293097637748767564853 798683727903538946959205)
                    ·
                      rfl

theorem cell23_4666293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_4666293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666293 prefixEnd_4666293 := by exact prefixLift 4666293
  have htrace : WordTrace (prefixWord ++ tailWord_4666293) baseStart_4666293 baseEnd_4666293 := by
    simpa [prefixWord, tailWord_4666293, baseEnd_4666293] using wordTrace_append hprefix tailTrace_4666293
  have hstable : (prefixWord ++ tailWord_4666293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666293).length < 2 ^ (prefixWord ++ tailWord_4666293).sum := by decide
  have hdescent : baseEnd_4666293 < baseStart_4666293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666294 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4666294 : Nat := 118140960795 + 4666294 * 2 ^ 59
def prefixEnd_4666294 : Nat := 4983230072969 + 3 ^ 40 * 4666294 * 2
def baseEnd_4666294 : Nat := 2396051697191271336965111

theorem tailTrace_4666294 : CollatzResearch.WordTrace tailWord_4666294 prefixEnd_4666294 2396051697191271336965111 := by
  unfold tailWord_4666294
  simp only [CollatzResearch.WordTrace]
  refine ⟨10637107759801328275794371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113462482771214168275139957 10637107759801328275794371)
  ·
    refine ⟨15955661639701992413691557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10637107759801328275794371 15955661639701992413691557)
    ·
      refine ⟨2991686557444123577567167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15955661639701992413691557 2991686557444123577567167)
      ·
        refine ⟨4487529836166185366350751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2991686557444123577567167 4487529836166185366350751)
        ·
          refine ⟨6731294754249278049526127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4487529836166185366350751 6731294754249278049526127)
          ·
            refine ⟨10096942131373917074289191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6731294754249278049526127 10096942131373917074289191)
            ·
              refine ⟨15145413197060875611433787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10096942131373917074289191 15145413197060875611433787)
              ·
                refine ⟨22718119795591313417150681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15145413197060875611433787 22718119795591313417150681)
                ·
                  refine ⟨17038589846693485062863011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22718119795591313417150681 17038589846693485062863011)
                  ·
                    refine ⟨25557884770040227594294517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17038589846693485062863011 25557884770040227594294517)
                    ·
                      refine ⟨2396051697191271336965111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25557884770040227594294517 2396051697191271336965111)
                      ·
                        rfl

theorem cell23_4666294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4666294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666294 prefixEnd_4666294 := by exact prefixLift 4666294
  have htrace : WordTrace (prefixWord ++ tailWord_4666294) baseStart_4666294 baseEnd_4666294 := by
    simpa [prefixWord, tailWord_4666294, baseEnd_4666294] using wordTrace_append hprefix tailTrace_4666294
  have hstable : (prefixWord ++ tailWord_4666294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666294).length < 2 ^ (prefixWord ++ tailWord_4666294).sum := by decide
  have hdescent : baseEnd_4666294 < baseStart_4666294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666423 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_4666423 : Nat := 118140960795 + 4666423 * 2 ^ 59
def prefixEnd_4666423 : Nat := 4983230072969 + 3 ^ 40 * 4666423 * 2
def baseEnd_4666423 : Nat := 2396117936195701332252017

theorem tailTrace_4666423 : CollatzResearch.WordTrace tailWord_4666423 prefixEnd_4666423 2396117936195701332252017 := by
  unfold tailWord_4666423
  simp only [CollatzResearch.WordTrace]
  refine ⟨170198429173353907444155923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113465619448902604962770615 170198429173353907444155923)
  ·
    refine ⟨255297643760030861166233885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170198429173353907444155923 255297643760030861166233885)
    ·
      refine ⟨95736616410011572937337707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255297643760030861166233885 95736616410011572937337707)
      ·
        refine ⟨143604924615017359406006561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95736616410011572937337707 143604924615017359406006561)
        ·
          refine ⟨107703693461263019554504921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143604924615017359406006561 107703693461263019554504921)
          ·
            refine ⟨80777770095947264665878691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107703693461263019554504921 80777770095947264665878691)
            ·
              refine ⟨121166655143920896998818037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80777770095947264665878691 121166655143920896998818037)
              ·
                refine ⟨11359373919742584093639191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121166655143920896998818037 11359373919742584093639191)
                ·
                  refine ⟨17039060879613876140458787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11359373919742584093639191 17039060879613876140458787)
                  ·
                    refine ⟨25558591319420814210688181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17039060879613876140458787 25558591319420814210688181)
                    ·
                      refine ⟨2396117936195701332252017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25558591319420814210688181 2396117936195701332252017)
                      ·
                        rfl

theorem cell23_4666423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_4666423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666423 prefixEnd_4666423 := by exact prefixLift 4666423
  have htrace : WordTrace (prefixWord ++ tailWord_4666423) baseStart_4666423 baseEnd_4666423 := by
    simpa [prefixWord, tailWord_4666423, baseEnd_4666423] using wordTrace_append hprefix tailTrace_4666423
  have hstable : (prefixWord ++ tailWord_4666423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666423).length < 2 ^ (prefixWord ++ tailWord_4666423).sum := by decide
  have hdescent : baseEnd_4666423 < baseStart_4666423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666437 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 3, 2, 2]
def baseStart_4666437 : Nat := 118140960795 + 4666437 * 2 ^ 59
def prefixEnd_4666437 : Nat := 4983230072969 + 3 ^ 40 * 4666437 * 2
def baseEnd_4666437 : Nat := 2396125124924864277476953

theorem tailTrace_4666437 : CollatzResearch.WordTrace tailWord_4666437 prefixEnd_4666437 2396125124924864277476953 := by
  unfold tailWord_4666437
  simp only [CollatzResearch.WordTrace]
  refine ⟨170198939795303187835165565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113465959863535458556777043 170198939795303187835165565)
  ·
    refine ⟨63824602423238695438187087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170198939795303187835165565 63824602423238695438187087)
    ·
      refine ⟨95736903634858043157280631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63824602423238695438187087 95736903634858043157280631)
      ·
        refine ⟨143605355452287064735920947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95736903634858043157280631 143605355452287064735920947)
        ·
          refine ⟨215408033178430597103881421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143605355452287064735920947 215408033178430597103881421)
          ·
            refine ⟨80778012441911473913955533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215408033178430597103881421 80778012441911473913955533)
            ·
              refine ⟨30291754665716802717733325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80778012441911473913955533 30291754665716802717733325)
              ·
                refine ⟨11359407999643801019149997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30291754665716802717733325 11359407999643801019149997)
                ·
                  refine ⟨4259777999866425382181249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11359407999643801019149997 4259777999866425382181249)
                  ·
                    refine ⟨3194833499899819036635937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4259777999866425382181249 3194833499899819036635937)
                    ·
                      refine ⟨2396125124924864277476953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194833499899819036635937 2396125124924864277476953)
                      ·
                        rfl

theorem cell23_4666437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 2, 2].length) (baseStart_4666437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666437 prefixEnd_4666437 := by exact prefixLift 4666437
  have htrace : WordTrace (prefixWord ++ tailWord_4666437) baseStart_4666437 baseEnd_4666437 := by
    simpa [prefixWord, tailWord_4666437, baseEnd_4666437] using wordTrace_append hprefix tailTrace_4666437
  have hstable : (prefixWord ++ tailWord_4666437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666437).length < 2 ^ (prefixWord ++ tailWord_4666437).sum := by decide
  have hdescent : baseEnd_4666437 < baseStart_4666437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666450 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_4666450 : Nat := 118140960795 + 4666450 * 2 ^ 59
def prefixEnd_4666450 : Nat := 4983230072969 + 3 ^ 40 * 4666450 * 2
def baseEnd_4666450 : Nat := 2396131800173372726614393

theorem tailTrace_4666450 : CollatzResearch.WordTrace tailWord_4666450 prefixEnd_4666450 2396131800173372726614393 := by
  unfold tailWord_4666450
  simp only [CollatzResearch.WordTrace]
  refine ⟨42549853486064022763847201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113466275962837394036925869 42549853486064022763847201)
  ·
    refine ⟨31912390114548017072885401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42549853486064022763847201 31912390114548017072885401)
    ·
      refine ⟨23934292585911012804664051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31912390114548017072885401 23934292585911012804664051)
      ·
        refine ⟨35901438878866519206996077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23934292585911012804664051 35901438878866519206996077)
        ·
          refine ⟨13463039579574944702623529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35901438878866519206996077 13463039579574944702623529)
          ·
            refine ⟨10097279684681208526967647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13463039579574944702623529 10097279684681208526967647)
            ·
              refine ⟨15145919527021812790451471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10097279684681208526967647 15145919527021812790451471)
              ·
                refine ⟨22718879290532719185677207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15145919527021812790451471 22718879290532719185677207)
                ·
                  refine ⟨34078318935799078778515811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22718879290532719185677207 34078318935799078778515811)
                  ·
                    refine ⟨51117478403698618167773717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34078318935799078778515811 51117478403698618167773717)
                    ·
                      refine ⟨2396131800173372726614393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51117478403698618167773717 2396131800173372726614393)
                      ·
                        rfl

theorem cell23_4666450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_4666450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666450 prefixEnd_4666450 := by exact prefixLift 4666450
  have htrace : WordTrace (prefixWord ++ tailWord_4666450) baseStart_4666450 baseEnd_4666450 := by
    simpa [prefixWord, tailWord_4666450, baseEnd_4666450] using wordTrace_append hprefix tailTrace_4666450
  have hstable : (prefixWord ++ tailWord_4666450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666450).length < 2 ^ (prefixWord ++ tailWord_4666450).sum := by decide
  have hdescent : baseEnd_4666450 < baseStart_4666450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666471 : List Nat := [1, 1, 5, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_4666471 : Nat := 118140960795 + 4666471 * 2 ^ 59
def prefixEnd_4666471 : Nat := 4983230072969 + 3 ^ 40 * 4666471 * 2
def baseEnd_4666471 : Nat := 2396142583267117144451797

theorem tailTrace_4666471 : CollatzResearch.WordTrace tailWord_4666471 prefixEnd_4666471 2396142583267117144451797 := by
  unfold tailWord_4666471
  simp only [CollatzResearch.WordTrace]
  refine ⟨170200179877180011641903267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113466786584786674427935511 170200179877180011641903267)
  ·
    refine ⟨255300269815770017462854901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170200179877180011641903267 255300269815770017462854901)
    ·
      refine ⟨23934400295228439137142647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 255300269815770017462854901 23934400295228439137142647)
      ·
        refine ⟨35901600442842658705713971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23934400295228439137142647 35901600442842658705713971)
        ·
          refine ⟨53852400664263988058570957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35901600442842658705713971 53852400664263988058570957)
          ·
            refine ⟨20194650249098995521964109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53852400664263988058570957 20194650249098995521964109)
            ·
              refine ⟨7572993843412123320736541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20194650249098995521964109 7572993843412123320736541)
              ·
                refine ⟨2839872691279546245276203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7572993843412123320736541 2839872691279546245276203)
                ·
                  refine ⟨4259809036919319367914305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2839872691279546245276203 4259809036919319367914305)
                  ·
                    refine ⟨3194856777689489525935729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4259809036919319367914305 3194856777689489525935729)
                    ·
                      refine ⟨2396142583267117144451797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194856777689489525935729 2396142583267117144451797)
                      ·
                        rfl

theorem cell23_4666471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_4666471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666471 prefixEnd_4666471 := by exact prefixLift 4666471
  have htrace : WordTrace (prefixWord ++ tailWord_4666471) baseStart_4666471 baseEnd_4666471 := by
    simpa [prefixWord, tailWord_4666471, baseEnd_4666471] using wordTrace_append hprefix tailTrace_4666471
  have hstable : (prefixWord ++ tailWord_4666471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666471).length < 2 ^ (prefixWord ++ tailWord_4666471).sum := by decide
  have hdescent : baseEnd_4666471 < baseStart_4666471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666487 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 2, 1, 3]
def baseStart_4666487 : Nat := 118140960795 + 4666487 * 2 ^ 59
def prefixEnd_4666487 : Nat := 4983230072969 + 3 ^ 40 * 4666487 * 2
def baseEnd_4666487 : Nat := 2396150798957589081851723

theorem tailTrace_4666487 : CollatzResearch.WordTrace tailWord_4666487 prefixEnd_4666487 2396150798957589081851723 := by
  unfold tailWord_4666487
  simp only [CollatzResearch.WordTrace]
  refine ⟨170200763445122046374485715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113467175630081364249657143 170200763445122046374485715)
  ·
    refine ⟨255301145167683069561728573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170200763445122046374485715 255301145167683069561728573)
    ·
      refine ⟨95737929437881151085648215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255301145167683069561728573 95737929437881151085648215)
      ·
        refine ⟨143606894156821726628472323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95737929437881151085648215 143606894156821726628472323)
        ·
          refine ⟨215410341235232589942708485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143606894156821726628472323 215410341235232589942708485)
          ·
            refine ⟨40389438981606110614257841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215410341235232589942708485 40389438981606110614257841)
            ·
              refine ⟨30292079236204582960693381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40389438981606110614257841 30292079236204582960693381)
              ·
                refine ⟨5679764856788359305130009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30292079236204582960693381 5679764856788359305130009)
                ·
                  refine ⟨4259823642591269478847507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5679764856788359305130009 4259823642591269478847507)
                  ·
                    refine ⟨6389735463886904218271261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4259823642591269478847507 6389735463886904218271261)
                    ·
                      refine ⟨2396150798957589081851723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6389735463886904218271261 2396150798957589081851723)
                      ·
                        rfl

theorem cell23_4666487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_4666487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666487 prefixEnd_4666487 := by exact prefixLift 4666487
  have htrace : WordTrace (prefixWord ++ tailWord_4666487) baseStart_4666487 baseEnd_4666487 := by
    simpa [prefixWord, tailWord_4666487, baseEnd_4666487] using wordTrace_append hprefix tailTrace_4666487
  have hstable : (prefixWord ++ tailWord_4666487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666487).length < 2 ^ (prefixWord ++ tailWord_4666487).sum := by decide
  have hdescent : baseEnd_4666487 < baseStart_4666487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666503 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 1, 8]
def baseStart_4666503 : Nat := 118140960795 + 4666503 * 2 ^ 59
def prefixEnd_4666503 : Nat := 4983230072969 + 3 ^ 40 * 4666503 * 2
def baseEnd_4666503 : Nat := 798719671549353673083883

theorem tailTrace_4666503 : CollatzResearch.WordTrace tailWord_4666503 prefixEnd_4666503 798719671549353673083883 := by
  unfold tailWord_4666503
  simp only [CollatzResearch.WordTrace]
  refine ⟨170201347013064081107068163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113467564675376054071378775 170201347013064081107068163)
  ·
    refine ⟨255302020519596121660602245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170201347013064081107068163 255302020519596121660602245)
    ·
      refine ⟨47869128847424272811362921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255302020519596121660602245 47869128847424272811362921)
      ·
        refine ⟨35901846635568204608522191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47869128847424272811362921 35901846635568204608522191)
        ·
          refine ⟨53852769953352306912783287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35901846635568204608522191 53852769953352306912783287)
          ·
            refine ⟨80779154930028460369174931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53852769953352306912783287 80779154930028460369174931)
            ·
              refine ⟨121168732395042690553762397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80779154930028460369174931 121168732395042690553762397)
              ·
                refine ⟨45438274648141008957660899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121168732395042690553762397 45438274648141008957660899)
                ·
                  refine ⟨68157411972211513436491349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45438274648141008957660899 68157411972211513436491349)
                  ·
                    refine ⟨798719671549353673083883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68157411972211513436491349 798719671549353673083883)
                    ·
                      rfl

theorem cell23_4666503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_4666503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666503 prefixEnd_4666503 := by exact prefixLift 4666503
  have htrace : WordTrace (prefixWord ++ tailWord_4666503) baseStart_4666503 baseEnd_4666503 := by
    simpa [prefixWord, tailWord_4666503, baseEnd_4666503] using wordTrace_append hprefix tailTrace_4666503
  have hstable : (prefixWord ++ tailWord_4666503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666503).length < 2 ^ (prefixWord ++ tailWord_4666503).sum := by decide
  have hdescent : baseEnd_4666503 < baseStart_4666503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666514 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_4666514 : Nat := 118140960795 + 4666514 * 2 ^ 59
def prefixEnd_4666514 : Nat := 4983230072969 + 3 ^ 40 * 4666514 * 2
def baseEnd_4666514 : Nat := 2396164662935260476214099

theorem tailTrace_4666514 : CollatzResearch.WordTrace tailWord_4666514 prefixEnd_4666514 2396164662935260476214099 := by
  unfold tailWord_4666514
  simp only [CollatzResearch.WordTrace]
  refine ⟨42550437054006057496429649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113467832144016153323812397 42550437054006057496429649)
  ·
    refine ⟨31912827790504543122322237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42550437054006057496429649 31912827790504543122322237)
    ·
      refine ⟨11967310421439203670870839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31912827790504543122322237 11967310421439203670870839)
      ·
        refine ⟨17950965632158805506306259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11967310421439203670870839 17950965632158805506306259)
        ·
          refine ⟨26926448448238208259459389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17950965632158805506306259 26926448448238208259459389)
          ·
            refine ⟨10097418168089328097297271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26926448448238208259459389 10097418168089328097297271)
            ·
              refine ⟨15146127252133992145945907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10097418168089328097297271 15146127252133992145945907)
              ·
                refine ⟨22719190878200988218918861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15146127252133992145945907 22719190878200988218918861)
                ·
                  refine ⟨8519696579325370582094573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22719190878200988218918861 8519696579325370582094573)
                  ·
                    refine ⟨3194886217247013968285465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8519696579325370582094573 3194886217247013968285465)
                    ·
                      refine ⟨2396164662935260476214099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194886217247013968285465 2396164662935260476214099)
                      ·
                        rfl

theorem cell23_4666514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_4666514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666514 prefixEnd_4666514 := by exact prefixLift 4666514
  have htrace : WordTrace (prefixWord ++ tailWord_4666514) baseStart_4666514 baseEnd_4666514 := by
    simpa [prefixWord, tailWord_4666514, baseEnd_4666514] using wordTrace_append hprefix tailTrace_4666514
  have hstable : (prefixWord ++ tailWord_4666514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666514).length < 2 ^ (prefixWord ++ tailWord_4666514).sum := by decide
  have hdescent : baseEnd_4666514 < baseStart_4666514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666543 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_4666543 : Nat := 118140960795 + 4666543 * 2 ^ 59
def prefixEnd_4666543 : Nat := 4983230072969 + 3 ^ 40 * 4666543 * 2
def baseEnd_4666543 : Nat := 2396179553874240862751465

theorem tailTrace_4666543 : CollatzResearch.WordTrace tailWord_4666543 prefixEnd_4666543 2396179553874240862751465 := by
  unfold tailWord_4666543
  simp only [CollatzResearch.WordTrace]
  refine ⟨170202805932919167938524283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113468537288612778625682855 170202805932919167938524283)
  ·
    refine ⟨255304208899378751907786425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170202805932919167938524283 255304208899378751907786425)
    ·
      refine ⟨191478156674534063930839819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255304208899378751907786425 191478156674534063930839819)
      ·
        refine ⟨287217235011801095896259729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191478156674534063930839819 287217235011801095896259729)
        ·
          refine ⟨215412926258850821922194797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287217235011801095896259729 215412926258850821922194797)
          ·
            refine ⟨80779847347069058220823049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215412926258850821922194797 80779847347069058220823049)
            ·
              refine ⟨60584885510301793665617287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80779847347069058220823049 60584885510301793665617287)
              ·
                refine ⟨90877328265452690498425931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60584885510301793665617287 90877328265452690498425931)
                ·
                  refine ⟨136315992398179035747638897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90877328265452690498425931 136315992398179035747638897)
                  ·
                    refine ⟨102236994298634276810729173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 136315992398179035747638897 102236994298634276810729173)
                    ·
                      refine ⟨2396179553874240862751465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102236994298634276810729173 2396179553874240862751465)
                      ·
                        rfl

theorem cell23_4666543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_4666543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666543 prefixEnd_4666543 := by exact prefixLift 4666543
  have htrace : WordTrace (prefixWord ++ tailWord_4666543) baseStart_4666543 baseEnd_4666543 := by
    simpa [prefixWord, tailWord_4666543, baseEnd_4666543] using wordTrace_append hprefix tailTrace_4666543
  have hstable : (prefixWord ++ tailWord_4666543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666543).length < 2 ^ (prefixWord ++ tailWord_4666543).sum := by decide
  have hdescent : baseEnd_4666543 < baseStart_4666543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666561 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_4666561 : Nat := 118140960795 + 4666561 * 2 ^ 59
def prefixEnd_4666561 : Nat := 4983230072969 + 3 ^ 40 * 4666561 * 2
def baseEnd_4666561 : Nat := 2396188796526021792326383

theorem tailTrace_4666561 : CollatzResearch.WordTrace tailWord_4666561 prefixEnd_4666561 2396188796526021792326383 := by
  unfold tailWord_4666561
  simp only [CollatzResearch.WordTrace]
  refine ⟨170203462446853957012679537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113468974964569304675119691 170203462446853957012679537)
  ·
    refine ⟨127652596835140467759509653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170203462446853957012679537 127652596835140467759509653)
    ·
      refine ⟨5983715476647209426227015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127652596835140467759509653 5983715476647209426227015)
      ·
        refine ⟨8975573214970814139340523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5983715476647209426227015 8975573214970814139340523)
        ·
          refine ⟨13463359822456221209010785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8975573214970814139340523 13463359822456221209010785)
          ·
            refine ⟨10097519866842165906758089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13463359822456221209010785 10097519866842165906758089)
            ·
              refine ⟨7573139900131624430068567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10097519866842165906758089 7573139900131624430068567)
              ·
                refine ⟨11359709850197436645102851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7573139900131624430068567 11359709850197436645102851)
                ·
                  refine ⟨17039564775296154967654277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11359709850197436645102851 17039564775296154967654277)
                  ·
                    refine ⟨3194918395368029056435177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17039564775296154967654277 3194918395368029056435177)
                    ·
                      refine ⟨2396188796526021792326383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194918395368029056435177 2396188796526021792326383)
                      ·
                        rfl

theorem cell23_4666561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_4666561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666561 prefixEnd_4666561 := by exact prefixLift 4666561
  have htrace : WordTrace (prefixWord ++ tailWord_4666561) baseStart_4666561 baseEnd_4666561 := by
    simpa [prefixWord, tailWord_4666561, baseEnd_4666561] using wordTrace_append hprefix tailTrace_4666561
  have hstable : (prefixWord ++ tailWord_4666561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666561).length < 2 ^ (prefixWord ++ tailWord_4666561).sum := by decide
  have hdescent : baseEnd_4666561 < baseStart_4666561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666582 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_4666582 : Nat := 118140960795 + 4666582 * 2 ^ 59
def prefixEnd_4666582 : Nat := 4983230072969 + 3 ^ 40 * 4666582 * 2
def baseEnd_4666582 : Nat := 2396199579619766210163787

theorem tailTrace_4666582 : CollatzResearch.WordTrace tailWord_4666582 prefixEnd_4666582 2396199579619766210163787 := by
  unfold tailWord_4666582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10637764273736117349949625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113469485586518585066129333 10637764273736117349949625)
  ·
    refine ⟨7978323205302088012462219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10637764273736117349949625 7978323205302088012462219)
    ·
      refine ⟨11967484807953132018693329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7978323205302088012462219 11967484807953132018693329)
      ·
        refine ⟨8975613605964849014019997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11967484807953132018693329 8975613605964849014019997)
        ·
          refine ⟨3365855102236818380257499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8975613605964849014019997 3365855102236818380257499)
          ·
            refine ⟨5048782653355227570386249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365855102236818380257499 5048782653355227570386249)
            ·
              refine ⟨3786586990016420677789687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5048782653355227570386249 3786586990016420677789687)
              ·
                refine ⟨5679880485024631016684531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3786586990016420677789687 5679880485024631016684531)
                ·
                  refine ⟨8519820727536946525026797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5679880485024631016684531 8519820727536946525026797)
                  ·
                    refine ⟨3194932772826354946885049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8519820727536946525026797 3194932772826354946885049)
                    ·
                      refine ⟨2396199579619766210163787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194932772826354946885049 2396199579619766210163787)
                      ·
                        rfl

theorem cell23_4666582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_4666582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666582 prefixEnd_4666582 := by exact prefixLift 4666582
  have htrace : WordTrace (prefixWord ++ tailWord_4666582) baseStart_4666582 baseEnd_4666582 := by
    simpa [prefixWord, tailWord_4666582, baseEnd_4666582] using wordTrace_append hprefix tailTrace_4666582
  have hstable : (prefixWord ++ tailWord_4666582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666582).length < 2 ^ (prefixWord ++ tailWord_4666582).sum := by decide
  have hdescent : baseEnd_4666582 < baseStart_4666582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666584 : List Nat := [2, 1, 2, 2, 5, 1, 2, 3, 5]
def baseStart_4666584 : Nat := 118140960795 + 4666584 * 2 ^ 59
def prefixEnd_4666584 : Nat := 4983230072969 + 3 ^ 40 * 4666584 * 2
def baseEnd_4666584 : Nat := 266244511842341689148753

theorem tailTrace_4666584 : CollatzResearch.WordTrace tailWord_4666584 prefixEnd_4666584 266244511842341689148753 := by
  unfold tailWord_4666584
  simp only [CollatzResearch.WordTrace]
  refine ⟨85102150662885315970383403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113469534217180421293844537 85102150662885315970383403)
  ·
    refine ⟨127653225994327973955575105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85102150662885315970383403 127653225994327973955575105)
    ·
      refine ⟨95739919495745980466681329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127653225994327973955575105 95739919495745980466681329)
      ·
        refine ⟨71804939621809485350010997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95739919495745980466681329 71804939621809485350010997)
        ·
          refine ⟨6731713089544639251563531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71804939621809485350010997 6731713089544639251563531)
          ·
            refine ⟨10097569634316958877345297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6731713089544639251563531 10097569634316958877345297)
            ·
              refine ⟨7573177225737719158008973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10097569634316958877345297 7573177225737719158008973)
              ·
                refine ⟨2839941459651644684253365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7573177225737719158008973 2839941459651644684253365)
                ·
                  refine ⟨266244511842341689148753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2839941459651644684253365 266244511842341689148753)
                  ·
                    rfl

theorem cell23_4666584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 5].length) (baseStart_4666584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666584 prefixEnd_4666584 := by exact prefixLift 4666584
  have htrace : WordTrace (prefixWord ++ tailWord_4666584) baseStart_4666584 baseEnd_4666584 := by
    simpa [prefixWord, tailWord_4666584, baseEnd_4666584] using wordTrace_append hprefix tailTrace_4666584
  have hstable : (prefixWord ++ tailWord_4666584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666584).length < 2 ^ (prefixWord ++ tailWord_4666584).sum := by decide
  have hdescent : baseEnd_4666584 < baseStart_4666584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666612 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4666612 : Nat := 118140960795 + 4666612 * 2 ^ 59
def prefixEnd_4666612 : Nat := 4983230072969 + 3 ^ 40 * 4666612 * 2
def baseEnd_4666612 : Nat := 2396214984039401092788649

theorem tailTrace_4666612 : CollatzResearch.WordTrace tailWord_4666612 prefixEnd_4666612 2396214984039401092788649 := by
  unfold tailWord_4666612
  simp only [CollatzResearch.WordTrace]
  refine ⟨85102661284834596361393045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113470215046446128481857393 85102661284834596361393045)
  ·
    refine ⟨3989187247726621704440299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85102661284834596361393045 3989187247726621704440299)
    ·
      refine ⟨5983780871589932556660449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3989187247726621704440299 5983780871589932556660449)
      ·
        refine ⟨4487835653692449417495337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5983780871589932556660449 4487835653692449417495337)
        ·
          refine ⟨3365876740269337063121503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4487835653692449417495337 3365876740269337063121503)
          ·
            refine ⟨5048815110404005594682255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365876740269337063121503 5048815110404005594682255)
            ·
              refine ⟨7573222665606008392023383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5048815110404005594682255 7573222665606008392023383)
              ·
                refine ⟨11359833998409012588035075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7573222665606008392023383 11359833998409012588035075)
                ·
                  refine ⟨17039750997613518882052613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11359833998409012588035075 17039750997613518882052613)
                  ·
                    refine ⟨3194953312052534790384865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17039750997613518882052613 3194953312052534790384865)
                    ·
                      refine ⟨2396214984039401092788649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194953312052534790384865 2396214984039401092788649)
                      ·
                        rfl

theorem cell23_4666612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4666612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666612 prefixEnd_4666612 := by exact prefixLift 4666612
  have htrace : WordTrace (prefixWord ++ tailWord_4666612) baseStart_4666612 baseEnd_4666612 := by
    simpa [prefixWord, tailWord_4666612, baseEnd_4666612] using wordTrace_append hprefix tailTrace_4666612
  have hstable : (prefixWord ++ tailWord_4666612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666612).length < 2 ^ (prefixWord ++ tailWord_4666612).sum := by decide
  have hdescent : baseEnd_4666612 < baseStart_4666612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666617 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 2, 4, 2]
def baseStart_4666617 : Nat := 118140960795 + 4666617 * 2 ^ 59
def prefixEnd_4666617 : Nat := 4983230072969 + 3 ^ 40 * 4666617 * 2
def baseEnd_4666617 : Nat := 2396217551442673573226125

theorem tailTrace_4666617 : CollatzResearch.WordTrace tailWord_4666617 prefixEnd_4666617 2396217551442673573226125 := by
  unfold tailWord_4666617
  simp only [CollatzResearch.WordTrace]
  refine ⟨170205504934651078576718105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113470336623100719051145403 170205504934651078576718105)
  ·
    refine ⟨127654128700988308932538579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170205504934651078576718105 127654128700988308932538579)
    ·
      refine ⟨191481193051482463398807869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127654128700988308932538579 191481193051482463398807869)
      ·
        refine ⟨71805447394305923774552951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191481193051482463398807869 71805447394305923774552951)
        ·
          refine ⟨107708171091458885661829427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71805447394305923774552951 107708171091458885661829427)
          ·
            refine ⟨161562256637188328492744141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107708171091458885661829427 161562256637188328492744141)
            ·
              refine ⟨60585846238945623184779053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161562256637188328492744141 60585846238945623184779053)
              ·
                refine ⟨22719692339604608694292145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60585846238945623184779053 22719692339604608694292145)
                ·
                  refine ⟨17039769254703456520719109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22719692339604608694292145 17039769254703456520719109)
                  ·
                    refine ⟨3194956735256898097634833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17039769254703456520719109 3194956735256898097634833)
                    ·
                      refine ⟨2396217551442673573226125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3194956735256898097634833 2396217551442673573226125)
                      ·
                        rfl

theorem cell23_4666617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_4666617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666617 prefixEnd_4666617 := by exact prefixLift 4666617
  have htrace : WordTrace (prefixWord ++ tailWord_4666617) baseStart_4666617 baseEnd_4666617 := by
    simpa [prefixWord, tailWord_4666617, baseEnd_4666617] using wordTrace_append hprefix tailTrace_4666617
  have hstable : (prefixWord ++ tailWord_4666617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666617).length < 2 ^ (prefixWord ++ tailWord_4666617).sum := by decide
  have hdescent : baseEnd_4666617 < baseStart_4666617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666627 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 3, 4]
def baseStart_4666627 : Nat := 118140960795 + 4666627 * 2 ^ 59
def prefixEnd_4666627 : Nat := 4983230072969 + 3 ^ 40 * 4666627 * 2
def baseEnd_4666627 : Nat := 798740895416406178033693

theorem tailTrace_4666627 : CollatzResearch.WordTrace tailWord_4666627 prefixEnd_4666627 798740895416406178033693 := by
  unfold tailWord_4666627
  simp only [CollatzResearch.WordTrace]
  refine ⟨170205869664614850284582135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113470579776409900189721423 170205869664614850284582135)
  ·
    refine ⟨255308804496922275426873203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170205869664614850284582135 255308804496922275426873203)
    ·
      refine ⟨382963206745383413140309805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255308804496922275426873203 382963206745383413140309805)
      ·
        refine ⟨143611202529518779927616177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 382963206745383413140309805 143611202529518779927616177)
        ·
          refine ⟨107708401897139084945712133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143611202529518779927616177 107708401897139084945712133)
          ·
            refine ⟨20195325355713578427321025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107708401897139084945712133 20195325355713578427321025)
            ·
              refine ⟨15146494016785183820490769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20195325355713578427321025 15146494016785183820490769)
              ·
                refine ⟨11359870512588887865368077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15146494016785183820490769 11359870512588887865368077)
                ·
                  refine ⟨4259951442220832949513029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11359870512588887865368077 4259951442220832949513029)
                  ·
                    refine ⟨798740895416406178033693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4259951442220832949513029 798740895416406178033693)
                    ·
                      rfl

theorem cell23_4666627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 4].length) (baseStart_4666627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666627 prefixEnd_4666627 := by exact prefixLift 4666627
  have htrace : WordTrace (prefixWord ++ tailWord_4666627) baseStart_4666627 baseEnd_4666627 := by
    simpa [prefixWord, tailWord_4666627, baseEnd_4666627] using wordTrace_append hprefix tailTrace_4666627
  have hstable : (prefixWord ++ tailWord_4666627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666627).length < 2 ^ (prefixWord ++ tailWord_4666627).sum := by decide
  have hdescent : baseEnd_4666627 < baseStart_4666627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666667 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 9, 1, 3]
def baseStart_4666667 : Nat := 118140960795 + 4666667 * 2 ^ 59
def prefixEnd_4666667 : Nat := 4983230072969 + 3 ^ 40 * 4666667 * 2
def baseEnd_4666667 : Nat := 2396243225475398377600895

theorem tailTrace_4666667 : CollatzResearch.WordTrace tailWord_4666667 prefixEnd_4666667 2396243225475398377600895 := by
  unfold tailWord_4666667
  simp only [CollatzResearch.WordTrace]
  refine ⟨170207328584469937116038255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113471552389646624744025503 170207328584469937116038255)
  ·
    refine ⟨255310992876704905674057383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170207328584469937116038255 255310992876704905674057383)
    ·
      refine ⟨382966489315057358511086075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255310992876704905674057383 382966489315057358511086075)
      ·
        refine ⟨574449733972586037766629113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382966489315057358511086075 574449733972586037766629113)
        ·
          refine ⟨430837300479439528324971835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 574449733972586037766629113 430837300479439528324971835)
          ·
            refine ⟨646255950719159292487457753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430837300479439528324971835 646255950719159292487457753)
            ·
              refine ⟨484691963039369469365593315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646255950719159292487457753 484691963039369469365593315)
              ·
                refine ⟨727037944559054204048389973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484691963039369469365593315 727037944559054204048389973)
                ·
                  refine ⟨4259987956400708226846035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 727037944559054204048389973 4259987956400708226846035)
                  ·
                    refine ⟨6389981934601062340269053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4259987956400708226846035 6389981934601062340269053)
                    ·
                      refine ⟨2396243225475398377600895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6389981934601062340269053 2396243225475398377600895)
                      ·
                        rfl

theorem cell23_4666667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 1, 3].length) (baseStart_4666667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666667 prefixEnd_4666667 := by exact prefixLift 4666667
  have htrace : WordTrace (prefixWord ++ tailWord_4666667) baseStart_4666667 baseEnd_4666667 := by
    simpa [prefixWord, tailWord_4666667, baseEnd_4666667] using wordTrace_append hprefix tailTrace_4666667
  have hstable : (prefixWord ++ tailWord_4666667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666667).length < 2 ^ (prefixWord ++ tailWord_4666667).sum := by decide
  have hdescent : baseEnd_4666667 < baseStart_4666667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666674 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 6]
def baseStart_4666674 : Nat := 118140960795 + 4666674 * 2 ^ 59
def prefixEnd_4666674 : Nat := 4983230072969 + 3 ^ 40 * 4666674 * 2
def baseEnd_4666674 : Nat := 266249646648886650023707

theorem tailTrace_4666674 : CollatzResearch.WordTrace tailWord_4666674 prefixEnd_4666674 266249646648886650023707 := by
  unfold tailWord_4666674
  simp only [CollatzResearch.WordTrace]
  refine ⟨42551895973861144327885769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113471722596963051541028717 42551895973861144327885769)
  ·
    refine ⟨31913921980395858245914327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42551895973861144327885769 31913921980395858245914327)
    ·
      refine ⟨47870882970593787368871491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31913921980395858245914327 47870882970593787368871491)
      ·
        refine ⟨71806324455890681053307237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47870882970593787368871491 71806324455890681053307237)
        ·
          refine ⟨13463685835479502697495107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71806324455890681053307237 13463685835479502697495107)
          ·
            refine ⟨20195528753219254046242661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13463685835479502697495107 20195528753219254046242661)
            ·
              refine ⟨3786661641228610133670499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20195528753219254046242661 3786661641228610133670499)
              ·
                refine ⟨5679992461842915200505749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3786661641228610133670499 5679992461842915200505749)
                ·
                  refine ⟨266249646648886650023707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5679992461842915200505749 266249646648886650023707)
                  ·
                    rfl

theorem cell23_4666674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_4666674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666674 prefixEnd_4666674 := by exact prefixLift 4666674
  have htrace : WordTrace (prefixWord ++ tailWord_4666674) baseStart_4666674 baseEnd_4666674 := by
    simpa [prefixWord, tailWord_4666674, baseEnd_4666674] using wordTrace_append hprefix tailTrace_4666674
  have hstable : (prefixWord ++ tailWord_4666674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666674).length < 2 ^ (prefixWord ++ tailWord_4666674).sum := by decide
  have hdescent : baseEnd_4666674 < baseStart_4666674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666687 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 3, 5]
def baseStart_4666687 : Nat := 118140960795 + 4666687 * 2 ^ 59
def prefixEnd_4666687 : Nat := 4983230072969 + 3 ^ 40 * 4666687 * 2
def baseEnd_4666687 : Nat := 798751165029496099783601

theorem tailTrace_4666687 : CollatzResearch.WordTrace tailWord_4666687 prefixEnd_4666687 798751165029496099783601 := by
  unfold tailWord_4666687
  simp only [CollatzResearch.WordTrace]
  refine ⟨170208058044397480531766315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113472038696264987021177543 170208058044397480531766315)
  ·
    refine ⟨255312087066596220797649473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170208058044397480531766315 255312087066596220797649473)
    ·
      refine ⟨191484065299947165598237105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255312087066596220797649473 191484065299947165598237105)
      ·
        refine ⟨143613048974960374198677829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191484065299947165598237105 143613048974960374198677829)
        ·
          refine ⟨26927446682805070162252093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143613048974960374198677829 26927446682805070162252093)
          ·
            refine ⟨10097792506051901310844535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26927446682805070162252093 10097792506051901310844535)
            ·
              refine ⟨15146688759077851966266803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10097792506051901310844535 15146688759077851966266803)
              ·
                refine ⟨22720033138616777949400205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15146688759077851966266803 22720033138616777949400205)
                ·
                  refine ⟨8520012426981291731025077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22720033138616777949400205 8520012426981291731025077)
                  ·
                    refine ⟨798751165029496099783601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8520012426981291731025077 798751165029496099783601)
                    ·
                      rfl

theorem cell23_4666687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_4666687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666687 prefixEnd_4666687 := by exact prefixLift 4666687
  have htrace : WordTrace (prefixWord ++ tailWord_4666687) baseStart_4666687 baseEnd_4666687 := by
    simpa [prefixWord, tailWord_4666687, baseEnd_4666687] using wordTrace_append hprefix tailTrace_4666687
  have hstable : (prefixWord ++ tailWord_4666687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666687).length < 2 ^ (prefixWord ++ tailWord_4666687).sum := by decide
  have hdescent : baseEnd_4666687 < baseStart_4666687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666704 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 1, 5]
def baseStart_4666704 : Nat := 118140960795 + 4666704 * 2 ^ 59
def prefixEnd_4666704 : Nat := 4983230072969 + 3 ^ 40 * 4666704 * 2
def baseEnd_4666704 : Nat := 798754074753204910946075

theorem tailTrace_4666704 : CollatzResearch.WordTrace tailWord_4666704 prefixEnd_4666704 798754074753204910946075 := by
  unfold tailWord_4666704
  simp only [CollatzResearch.WordTrace]
  refine ⟨85104339042667946217567583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113472452056890594956756777 85104339042667946217567583)
  ·
    refine ⟨127656508564001919326351375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85104339042667946217567583 127656508564001919326351375)
    ·
      refine ⟨191484762846002878989527063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127656508564001919326351375 191484762846002878989527063)
      ·
        refine ⟨287227144269004318484290595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191484762846002878989527063 287227144269004318484290595)
        ·
          refine ⟨430840716403506477726435893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287227144269004318484290595 430840716403506477726435893)
          ·
            refine ⟨40391317162828732286853365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 430840716403506477726435893 40391317162828732286853365)
            ·
              refine ⟨3786685984015193651892503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40391317162828732286853365 3786685984015193651892503)
              ·
                refine ⟨5680028976022790477838755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3786685984015193651892503 5680028976022790477838755)
                ·
                  refine ⟨8520043464034185716758133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5680028976022790477838755 8520043464034185716758133)
                  ·
                    refine ⟨798754074753204910946075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8520043464034185716758133 798754074753204910946075)
                    ·
                      rfl

theorem cell23_4666704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 5].length) (baseStart_4666704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666704 prefixEnd_4666704 := by exact prefixLift 4666704
  have htrace : WordTrace (prefixWord ++ tailWord_4666704) baseStart_4666704 baseEnd_4666704 := by
    simpa [prefixWord, tailWord_4666704, baseEnd_4666704] using wordTrace_append hprefix tailTrace_4666704
  have hstable : (prefixWord ++ tailWord_4666704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666704).length < 2 ^ (prefixWord ++ tailWord_4666704).sum := by decide
  have hdescent : baseEnd_4666704 < baseStart_4666704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666737 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_4666737 : Nat := 118140960795 + 4666737 * 2 ^ 59
def prefixEnd_4666737 : Nat := 4983230072969 + 3 ^ 40 * 4666737 * 2
def baseEnd_4666737 : Nat := 2396279169121213103725573

theorem tailTrace_4666737 : CollatzResearch.WordTrace tailWord_4666737 prefixEnd_4666737 2396279169121213103725573 := by
  unfold tailWord_4666737
  simp only [CollatzResearch.WordTrace]
  refine ⟨170209881694216339071086465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113473254462810892714057643 170209881694216339071086465)
  ·
    refine ⟨127657411270662254303314849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170209881694216339071086465 127657411270662254303314849)
    ·
      refine ⟨95743058452996690727486137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127657411270662254303314849 95743058452996690727486137)
      ·
        refine ⟨71807293839747518045614603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95743058452996690727486137 71807293839747518045614603)
        ·
          refine ⟨107710940759621277068421905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71807293839747518045614603 107710940759621277068421905)
          ·
            refine ⟨80783205569715957801316429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107710940759621277068421905 80783205569715957801316429)
            ·
              refine ⟨30293702088643484175493661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80783205569715957801316429 30293702088643484175493661)
              ·
                refine ⟨11360138283241306565810123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30293702088643484175493661 11360138283241306565810123)
                ·
                  refine ⟨17040207424861959848715185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11360138283241306565810123 17040207424861959848715185)
                  ·
                    refine ⟨12780155568646469886536389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17040207424861959848715185 12780155568646469886536389)
                    ·
                      refine ⟨2396279169121213103725573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12780155568646469886536389 2396279169121213103725573)
                      ·
                        rfl

theorem cell23_4666737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_4666737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666737 prefixEnd_4666737 := by exact prefixLift 4666737
  have htrace : WordTrace (prefixWord ++ tailWord_4666737) baseStart_4666737 baseEnd_4666737 := by
    simpa [prefixWord, tailWord_4666737, baseEnd_4666737] using wordTrace_append hprefix tailTrace_4666737
  have hstable : (prefixWord ++ tailWord_4666737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666737).length < 2 ^ (prefixWord ++ tailWord_4666737).sum := by decide
  have hdescent : baseEnd_4666737 < baseStart_4666737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666747 : List Nat := [1, 1, 1, 1, 1, 6, 5, 7]
def baseStart_4666747 : Nat := 118140960795 + 4666747 * 2 ^ 59
def prefixEnd_4666747 : Nat := 4983230072969 + 3 ^ 40 * 4666747 * 2
def baseEnd_4666747 : Nat := 88751270515842891281501

theorem tailTrace_4666747 : CollatzResearch.WordTrace tailWord_4666747 prefixEnd_4666747 88751270515842891281501 := by
  unfold tailWord_4666747
  simp only [CollatzResearch.WordTrace]
  refine ⟨170210246424180110778950495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113473497616120073852633663 170210246424180110778950495)
  ·
    refine ⟨255315369636270166168425743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170210246424180110778950495 255315369636270166168425743)
    ·
      refine ⟨382973054454405249252638615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255315369636270166168425743 382973054454405249252638615)
      ·
        refine ⟨574459581681607873878957923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382973054454405249252638615 574459581681607873878957923)
        ·
          refine ⟨861689372522411810818436885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574459581681607873878957923 861689372522411810818436885)
          ·
            refine ⟨40391689336988053632114229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 861689372522411810818436885 40391689336988053632114229)
            ·
              refine ⟨3786720875342630028010709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40391689336988053632114229 3786720875342630028010709)
              ·
                refine ⟨88751270515842891281501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3786720875342630028010709 88751270515842891281501)
                ·
                  rfl

theorem cell23_4666747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 7].length) (baseStart_4666747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666747 prefixEnd_4666747 := by exact prefixLift 4666747
  have htrace : WordTrace (prefixWord ++ tailWord_4666747) baseStart_4666747 baseEnd_4666747 := by
    simpa [prefixWord, tailWord_4666747, baseEnd_4666747] using wordTrace_append hprefix tailTrace_4666747
  have hstable : (prefixWord ++ tailWord_4666747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666747).length < 2 ^ (prefixWord ++ tailWord_4666747).sum := by decide
  have hdescent : baseEnd_4666747 < baseStart_4666747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666761 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 1, 2, 3]
def baseStart_4666761 : Nat := 118140960795 + 4666761 * 2 ^ 59
def prefixEnd_4666761 : Nat := 4983230072969 + 3 ^ 40 * 4666761 * 2
def baseEnd_4666761 : Nat := 2396291492656921009825463

theorem tailTrace_4666761 : CollatzResearch.WordTrace tailWord_4666761 prefixEnd_4666761 2396291492656921009825463 := by
  unfold tailWord_4666761
  simp only [CollatzResearch.WordTrace]
  refine ⟨170210757046129391169960137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113473838030752927446640091 170210757046129391169960137)
  ·
    refine ⟨127658067784597043377470103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170210757046129391169960137 127658067784597043377470103)
    ·
      refine ⟨191487101676895565066205155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127658067784597043377470103 191487101676895565066205155)
      ·
        refine ⟨287230652515343347599307733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191487101676895565066205155 287230652515343347599307733)
        ·
          refine ⟨6731968418328359709358775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 287230652515343347599307733 6731968418328359709358775)
          ·
            refine ⟨10097952627492539564038163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6731968418328359709358775 10097952627492539564038163)
            ·
              refine ⟨15146928941238809346057245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10097952627492539564038163 15146928941238809346057245)
              ·
                refine ⟨5680098352964553504771467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15146928941238809346057245 5680098352964553504771467)
                ·
                  refine ⟨8520147529446830257157201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5680098352964553504771467 8520147529446830257157201)
                  ·
                    refine ⟨6390110647085122692867901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8520147529446830257157201 6390110647085122692867901)
                    ·
                      refine ⟨2396291492656921009825463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6390110647085122692867901 2396291492656921009825463)
                      ·
                        rfl

theorem cell23_4666761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 2, 3].length) (baseStart_4666761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666761 prefixEnd_4666761 := by exact prefixLift 4666761
  have htrace : WordTrace (prefixWord ++ tailWord_4666761) baseStart_4666761 baseEnd_4666761 := by
    simpa [prefixWord, tailWord_4666761, baseEnd_4666761] using wordTrace_append hprefix tailTrace_4666761
  have hstable : (prefixWord ++ tailWord_4666761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666761).length < 2 ^ (prefixWord ++ tailWord_4666761).sum := by decide
  have hdescent : baseEnd_4666761 < baseStart_4666761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666827 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 4]
def baseStart_4666827 : Nat := 118140960795 + 4666827 * 2 ^ 59
def prefixEnd_4666827 : Nat := 4983230072969 + 3 ^ 40 * 4666827 * 2
def baseEnd_4666827 : Nat := 2396325382380117751600159

theorem tailTrace_4666827 : CollatzResearch.WordTrace tailWord_4666827 prefixEnd_4666827 2396325382380117751600159 := by
  unfold tailWord_4666827
  simp only [CollatzResearch.WordTrace]
  refine ⟨170213164263890284441862735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113475442842593522961241823 170213164263890284441862735)
  ·
    refine ⟨255319746395835426662794103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170213164263890284441862735 255319746395835426662794103)
    ·
      refine ⟨382979619593753139994191155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255319746395835426662794103 382979619593753139994191155)
      ·
        refine ⟨574469429390629709991286733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382979619593753139994191155 574469429390629709991286733)
        ·
          refine ⟨215426036021486141246732525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 574469429390629709991286733 215426036021486141246732525)
          ·
            refine ⟨80784763508057302967524697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215426036021486141246732525 80784763508057302967524697)
            ·
              refine ⟨60588572631042977225643523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80784763508057302967524697 60588572631042977225643523)
              ·
                refine ⟨90882858946564465838465285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60588572631042977225643523 90882858946564465838465285)
                ·
                  refine ⟨17040536052480837344712241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90882858946564465838465285 17040536052480837344712241)
                  ·
                    refine ⟨12780402039360628008534181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17040536052480837344712241 12780402039360628008534181)
                    ·
                      refine ⟨2396325382380117751600159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12780402039360628008534181 2396325382380117751600159)
                      ·
                        rfl

theorem cell23_4666827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 4].length) (baseStart_4666827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666827 prefixEnd_4666827 := by exact prefixLift 4666827
  have htrace : WordTrace (prefixWord ++ tailWord_4666827) baseStart_4666827 baseEnd_4666827 := by
    simpa [prefixWord, tailWord_4666827, baseEnd_4666827] using wordTrace_append hprefix tailTrace_4666827
  have hstable : (prefixWord ++ tailWord_4666827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666827).length < 2 ^ (prefixWord ++ tailWord_4666827).sum := by decide
  have hdescent : baseEnd_4666827 < baseStart_4666827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666831 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 4, 2, 2]
def baseStart_4666831 : Nat := 118140960795 + 4666831 * 2 ^ 59
def prefixEnd_4666831 : Nat := 4983230072969 + 3 ^ 40 * 4666831 * 2
def baseEnd_4666831 : Nat := 2396327436302735735950141

theorem tailTrace_4666831 : CollatzResearch.WordTrace tailWord_4666831 prefixEnd_4666831 2396327436302735735950141 := by
  unfold tailWord_4666831
  simp only [CollatzResearch.WordTrace]
  refine ⟨170213310155875793125008347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113475540103917195416672231 170213310155875793125008347)
  ·
    refine ⟨255319965233813689687512521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170213310155875793125008347 255319965233813689687512521)
    ·
      refine ⟨191489973925360267265634391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255319965233813689687512521 191489973925360267265634391)
      ·
        refine ⟨287234960888040400898451587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191489973925360267265634391 287234960888040400898451587)
        ·
          refine ⟨430852441332060601347677381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287234960888040400898451587 430852441332060601347677381)
          ·
            refine ⟨80784832749761362752689509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 430852441332060601347677381 80784832749761362752689509)
            ·
              refine ⟨15147156140580255516129283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80784832749761362752689509 15147156140580255516129283)
              ·
                refine ⟨22720734210870383274193925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15147156140580255516129283 22720734210870383274193925)
                ·
                  refine ⟨4260137664538196863911361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22720734210870383274193925 4260137664538196863911361)
                  ·
                    refine ⟨3195103248403647647933521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4260137664538196863911361 3195103248403647647933521)
                    ·
                      refine ⟨2396327436302735735950141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3195103248403647647933521 2396327436302735735950141)
                      ·
                        rfl

theorem cell23_4666831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 2, 2].length) (baseStart_4666831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666831 prefixEnd_4666831 := by exact prefixLift 4666831
  have htrace : WordTrace (prefixWord ++ tailWord_4666831) baseStart_4666831 baseEnd_4666831 := by
    simpa [prefixWord, tailWord_4666831, baseEnd_4666831] using wordTrace_append hprefix tailTrace_4666831
  have hstable : (prefixWord ++ tailWord_4666831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666831).length < 2 ^ (prefixWord ++ tailWord_4666831).sum := by decide
  have hdescent : baseEnd_4666831 < baseStart_4666831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666882 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_4666882 : Nat := 118140960795 + 4666882 * 2 ^ 59
def prefixEnd_4666882 : Nat := 4983230072969 + 3 ^ 40 * 4666882 * 2
def baseEnd_4666882 : Nat := 2396353623816115036412407

theorem tailTrace_4666882 : CollatzResearch.WordTrace tailWord_4666882 prefixEnd_4666882 2396353623816115036412407 := by
  unfold tailWord_4666882
  simp only [CollatzResearch.WordTrace]
  refine ⟨42553792569672757208778725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113476780185794019223409933 42553792569672757208778725)
  ·
    refine ⟨7978836106813641976646011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42553792569672757208778725 7978836106813641976646011)
    ·
      refine ⟨11968254160220462964969017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7978836106813641976646011 11968254160220462964969017)
      ·
        refine ⟨8976190620165347223726763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11968254160220462964969017 8976190620165347223726763)
        ·
          refine ⟨13464285930248020835590145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8976190620165347223726763 13464285930248020835590145)
          ·
            refine ⟨10098214447686015626692609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13464285930248020835590145 10098214447686015626692609)
            ·
              refine ⟨7573660835764511720019457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10098214447686015626692609 7573660835764511720019457)
              ·
                refine ⟨5680245626823383790014593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7573660835764511720019457 5680245626823383790014593)
                ·
                  refine ⟨4260184220117537842510945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5680245626823383790014593 4260184220117537842510945)
                  ·
                    refine ⟨3195138165088153381883209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4260184220117537842510945 3195138165088153381883209)
                    ·
                      refine ⟨2396353623816115036412407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3195138165088153381883209 2396353623816115036412407)
                      ·
                        rfl

theorem cell23_4666882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_4666882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666882 prefixEnd_4666882 := by exact prefixLift 4666882
  have htrace : WordTrace (prefixWord ++ tailWord_4666882) baseStart_4666882 baseEnd_4666882 := by
    simpa [prefixWord, tailWord_4666882, baseEnd_4666882] using wordTrace_append hprefix tailTrace_4666882
  have hstable : (prefixWord ++ tailWord_4666882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666882).length < 2 ^ (prefixWord ++ tailWord_4666882).sum := by decide
  have hdescent : baseEnd_4666882 < baseStart_4666882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666961 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 6]
def baseStart_4666961 : Nat := 118140960795 + 4666961 * 2 ^ 59
def prefixEnd_4666961 : Nat := 4983230072969 + 3 ^ 40 * 4666961 * 2
def baseEnd_4666961 : Nat := 266266020976424469702727

theorem tailTrace_4666961 : CollatzResearch.WordTrace tailWord_4666961 prefixEnd_4666961 266266020976424469702727 := by
  unfold tailWord_4666961
  simp only [CollatzResearch.WordTrace]
  refine ⟨170218051645404825327240737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113478701096936550218160491 170218051645404825327240737)
  ·
    refine ⟨127663538734053618995430553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170218051645404825327240737 127663538734053618995430553)
    ·
      refine ⟨95747654050540214246572915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127663538734053618995430553 95747654050540214246572915)
      ·
        refine ⟨143621481075810321369859373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95747654050540214246572915 143621481075810321369859373)
        ·
          refine ⟨53858055403428870513697265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143621481075810321369859373 53858055403428870513697265)
          ·
            refine ⟨40393541552571652885272949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53858055403428870513697265 40393541552571652885272949)
            ·
              refine ⟨3786894520553592457994339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40393541552571652885272949 3786894520553592457994339)
              ·
                refine ⟨5680341780830388686991509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3786894520553592457994339 5680341780830388686991509)
                ·
                  refine ⟨266266020976424469702727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5680341780830388686991509 266266020976424469702727)
                  ·
                    rfl

theorem cell23_4666961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 6].length) (baseStart_4666961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666961 prefixEnd_4666961 := by exact prefixLift 4666961
  have htrace : WordTrace (prefixWord ++ tailWord_4666961) baseStart_4666961 baseEnd_4666961 := by
    simpa [prefixWord, tailWord_4666961, baseEnd_4666961] using wordTrace_append hprefix tailTrace_4666961
  have hstable : (prefixWord ++ tailWord_4666961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666961).length < 2 ^ (prefixWord ++ tailWord_4666961).sum := by decide
  have hdescent : baseEnd_4666961 < baseStart_4666961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4666964 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_4666964 : Nat := 118140960795 + 4666964 * 2 ^ 59
def prefixEnd_4666964 : Nat := 4983230072969 + 3 ^ 40 * 4666964 * 2
def baseEnd_4666964 : Nat := 2396395729229783715587029

theorem tailTrace_4666964 : CollatzResearch.WordTrace tailWord_4666964 prefixEnd_4666964 2396395729229783715587029 := by
  unfold tailWord_4666964
  simp only [CollatzResearch.WordTrace]
  refine ⟨85109080532196978419799973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113478774042929304559733297 85109080532196978419799973)
  ·
    refine ⟨15957952599786933453712495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85109080532196978419799973 15957952599786933453712495)
    ·
      refine ⟨23936928899680400180568743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15957952599786933453712495 23936928899680400180568743)
      ·
        refine ⟨35905393349520600270853115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23936928899680400180568743 35905393349520600270853115)
        ·
          refine ⟨53858090024280900406279673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35905393349520600270853115 53858090024280900406279673)
          ·
            refine ⟨40393567518210675304709755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53858090024280900406279673 40393567518210675304709755)
            ·
              refine ⟨60590351277316012957064633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40393567518210675304709755 60590351277316012957064633)
              ·
                refine ⟨45442763457987009717798475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60590351277316012957064633 45442763457987009717798475)
                ·
                  refine ⟨68164145186980514576697713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45442763457987009717798475 68164145186980514576697713)
                  ·
                    refine ⟨51123108890235385932523285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68164145186980514576697713 51123108890235385932523285)
                    ·
                      refine ⟨2396395729229783715587029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51123108890235385932523285 2396395729229783715587029)
                      ·
                        rfl

theorem cell23_4666964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_4666964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4666964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4666964 prefixEnd_4666964 := by exact prefixLift 4666964
  have htrace : WordTrace (prefixWord ++ tailWord_4666964) baseStart_4666964 baseEnd_4666964 := by
    simpa [prefixWord, tailWord_4666964, baseEnd_4666964] using wordTrace_append hprefix tailTrace_4666964
  have hstable : (prefixWord ++ tailWord_4666964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4666964).length < 2 ^ (prefixWord ++ tailWord_4666964).sum := by decide
  have hdescent : baseEnd_4666964 < baseStart_4666964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4666964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667005 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_4667005 : Nat := 118140960795 + 4667005 * 2 ^ 59
def prefixEnd_4667005 : Nat := 4983230072969 + 3 ^ 40 * 4667005 * 2
def baseEnd_4667005 : Nat := 2396416781936618055174341

theorem tailTrace_4667005 : CollatzResearch.WordTrace tailWord_4667005 prefixEnd_4667005 2396416781936618055174341 := by
  unfold tailWord_4667005
  simp only [CollatzResearch.WordTrace]
  refine ⟨170219656457245420841842469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113479770971496947227894979 170219656457245420841842469)
  ·
    refine ⟨31916185585733516407845463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170219656457245420841842469 31916185585733516407845463)
    ·
      refine ⟨47874278378600274611768195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31916185585733516407845463 47874278378600274611768195)
      ·
        refine ⟨71811417567900411917652293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47874278378600274611768195 71811417567900411917652293)
        ·
          refine ⟨13464640793981327234559805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71811417567900411917652293 13464640793981327234559805)
          ·
            refine ⟨5049240297742997712959927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13464640793981327234559805 5049240297742997712959927)
            ·
              refine ⟨7573860446614496569439891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049240297742997712959927 7573860446614496569439891)
              ·
                refine ⟨11360790669921744854159837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7573860446614496569439891 11360790669921744854159837)
                ·
                  refine ⟨4260296501220654320309939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11360790669921744854159837 4260296501220654320309939)
                  ·
                    refine ⟨6390444751830981480464909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4260296501220654320309939 6390444751830981480464909)
                    ·
                      refine ⟨2396416781936618055174341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6390444751830981480464909 2396416781936618055174341)
                      ·
                        rfl

theorem cell23_4667005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_4667005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667005 prefixEnd_4667005 := by exact prefixLift 4667005
  have htrace : WordTrace (prefixWord ++ tailWord_4667005) baseStart_4667005 baseEnd_4667005 := by
    simpa [prefixWord, tailWord_4667005, baseEnd_4667005] using wordTrace_append hprefix tailTrace_4667005
  have hstable : (prefixWord ++ tailWord_4667005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667005).length < 2 ^ (prefixWord ++ tailWord_4667005).sum := by decide
  have hdescent : baseEnd_4667005 < baseStart_4667005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667024 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 4]
def baseStart_4667024 : Nat := 118140960795 + 4667024 * 2 ^ 59
def prefixEnd_4667024 : Nat := 4983230072969 + 3 ^ 40 * 4667024 * 2
def baseEnd_4667024 : Nat := 2396426538069053480836753

theorem tailTrace_4667024 : CollatzResearch.WordTrace tailWord_4667024 prefixEnd_4667024 2396426538069053480836753 := by
  unfold tailWord_4667024
  simp only [CollatzResearch.WordTrace]
  refine ⟨85110174722088293543392063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113480232962784391391189417 85110174722088293543392063)
  ·
    refine ⟨127665262083132440315088095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85110174722088293543392063 127665262083132440315088095)
    ·
      refine ⟨191497893124698660472632143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127665262083132440315088095 191497893124698660472632143)
      ·
        refine ⟨287246839687047990708948215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191497893124698660472632143 287246839687047990708948215)
        ·
          refine ⟨430870259530571986063422323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287246839687047990708948215 430870259530571986063422323)
          ·
            refine ⟨646305389295857979095133485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430870259530571986063422323 646305389295857979095133485)
            ·
              refine ⟨242364520985946742160675057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 646305389295857979095133485 242364520985946742160675057)
              ·
                refine ⟨181773390739460056620506293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242364520985946742160675057 181773390739460056620506293)
                ·
                  refine ⟨17041255381824380308172465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 181773390739460056620506293 17041255381824380308172465)
                  ·
                    refine ⟨12780941536368285231129349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17041255381824380308172465 12780941536368285231129349)
                    ·
                      refine ⟨2396426538069053480836753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12780941536368285231129349 2396426538069053480836753)
                      ·
                        rfl

theorem cell23_4667024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_4667024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667024 prefixEnd_4667024 := by exact prefixLift 4667024
  have htrace : WordTrace (prefixWord ++ tailWord_4667024) baseStart_4667024 baseEnd_4667024 := by
    simpa [prefixWord, tailWord_4667024, baseEnd_4667024] using wordTrace_append hprefix tailTrace_4667024
  have hstable : (prefixWord ++ tailWord_4667024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667024).length < 2 ^ (prefixWord ++ tailWord_4667024).sum := by decide
  have hdescent : baseEnd_4667024 < baseStart_4667024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667038 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_4667038 : Nat := 118140960795 + 4667038 * 2 ^ 59
def prefixEnd_4667038 : Nat := 4983230072969 + 3 ^ 40 * 4667038 * 2
def baseEnd_4667038 : Nat := 798811242266072142020563

theorem tailTrace_4667038 : CollatzResearch.WordTrace tailWord_4667038 prefixEnd_4667038 798811242266072142020563 := by
  unfold tailWord_4667038
  simp only [CollatzResearch.WordTrace]
  refine ⟨21277607508265733434724221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113480573377417244985195845 21277607508265733434724221)
  ·
    refine ⟨7979102815599650038021583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21277607508265733434724221 7979102815599650038021583)
    ·
      refine ⟨11968654223399475057032375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7979102815599650038021583 11968654223399475057032375)
      ·
        refine ⟨17952981335099212585548563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11968654223399475057032375 17952981335099212585548563)
        ·
          refine ⟨26929472002648818878322845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17952981335099212585548563 26929472002648818878322845)
          ·
            refine ⟨10098552000993307079371067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26929472002648818878322845 10098552000993307079371067)
            ·
              refine ⟨15147828001489960619056601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10098552000993307079371067 15147828001489960619056601)
              ·
                refine ⟨11360871001117470464292451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15147828001489960619056601 11360871001117470464292451)
                ·
                  refine ⟨17041306501676205696438677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11360871001117470464292451 17041306501676205696438677)
                  ·
                    refine ⟨798811242266072142020563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17041306501676205696438677 798811242266072142020563)
                    ·
                      rfl

theorem cell23_4667038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_4667038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667038 prefixEnd_4667038 := by exact prefixLift 4667038
  have htrace : WordTrace (prefixWord ++ tailWord_4667038) baseStart_4667038 baseEnd_4667038 := by
    simpa [prefixWord, tailWord_4667038, baseEnd_4667038] using wordTrace_append hprefix tailTrace_4667038
  have hstable : (prefixWord ++ tailWord_4667038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667038).length < 2 ^ (prefixWord ++ tailWord_4667038).sum := by decide
  have hdescent : baseEnd_4667038 < baseStart_4667038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667041 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_4667041 : Nat := 118140960795 + 4667041 * 2 ^ 59
def prefixEnd_4667041 : Nat := 4983230072969 + 3 ^ 40 * 4667041 * 2
def baseEnd_4667041 : Nat := 2396435267240179914324175

theorem tailTrace_4667041 : CollatzResearch.WordTrace tailWord_4667041 prefixEnd_4667041 2396435267240179914324175 := by
  unfold tailWord_4667041
  simp only [CollatzResearch.WordTrace]
  refine ⟨170220969485114998990152977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113480646323409999326768651 170220969485114998990152977)
  ·
    refine ⟨127665727113836249242614733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170220969485114998990152977 127665727113836249242614733)
    ·
      refine ⟨47874647667688593465980525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127665727113836249242614733 47874647667688593465980525)
      ·
        refine ⟨17952992875383222549742697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47874647667688593465980525 17952992875383222549742697)
        ·
          refine ⟨13464744656537416912307023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17952992875383222549742697 13464744656537416912307023)
          ·
            refine ⟨20197116984806125368460535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13464744656537416912307023 20197116984806125368460535)
            ·
              refine ⟨30295675477209188052690803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20197116984806125368460535 30295675477209188052690803)
              ·
                refine ⟨45443513215813782079036205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30295675477209188052690803 45443513215813782079036205)
                ·
                  refine ⟨17041317455930168279638577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45443513215813782079036205 17041317455930168279638577)
                  ·
                    refine ⟨12780988091947626209728933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17041317455930168279638577 12780988091947626209728933)
                    ·
                      refine ⟨2396435267240179914324175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12780988091947626209728933 2396435267240179914324175)
                      ·
                        rfl

theorem cell23_4667041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_4667041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667041 prefixEnd_4667041 := by exact prefixLift 4667041
  have htrace : WordTrace (prefixWord ++ tailWord_4667041) baseStart_4667041 baseEnd_4667041 := by
    simpa [prefixWord, tailWord_4667041, baseEnd_4667041] using wordTrace_append hprefix tailTrace_4667041
  have hstable : (prefixWord ++ tailWord_4667041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667041).length < 2 ^ (prefixWord ++ tailWord_4667041).sum := by decide
  have hdescent : baseEnd_4667041 < baseStart_4667041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
