import V185TrunkScan22Chunk187

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1677385 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 1, 6]
def baseStart_1677385 : Nat := 118140960795 + 1677385 * 2 ^ 59
def prefixEnd_1677385 : Nat := 4983230072969 + 3 ^ 40 * 1677385 * 2
def baseEnd_1677385 : Nat := 574203165094683304782235

theorem tailTrace_1677385 : CollatzResearch.WordTrace tailWord_1677385 prefixEnd_1677385 574203165094683304782235 := by
  unfold tailWord_1677385
  simp only [CollatzResearch.WordTrace]
  refine ⟨61179257028128094395705609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40786171352085396263803739 61179257028128094395705609)
  ·
    refine ⟨45884442771096070796779207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61179257028128094395705609 45884442771096070796779207)
    ·
      refine ⟨68826664156644106195168811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45884442771096070796779207 68826664156644106195168811)
      ·
        refine ⟨103239996234966159292753217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68826664156644106195168811 103239996234966159292753217)
        ·
          refine ⟨77429997176224619469564913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103239996234966159292753217 77429997176224619469564913)
          ·
            refine ⟨58072497882168464602173685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77429997176224619469564913 58072497882168464602173685)
            ·
              refine ⟨5444296676453293556453783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58072497882168464602173685 5444296676453293556453783)
              ·
                refine ⟨8166445014679940334680675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5444296676453293556453783 8166445014679940334680675)
                ·
                  refine ⟨12249667522019910502021013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8166445014679940334680675 12249667522019910502021013)
                  ·
                    refine ⟨574203165094683304782235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12249667522019910502021013 574203165094683304782235)
                    ·
                      rfl

theorem cell22_1677385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_1677385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677385 prefixEnd_1677385 := by exact prefixLift 1677385
  have htrace : WordTrace (prefixWord ++ tailWord_1677385) baseStart_1677385 baseEnd_1677385 := by
    simpa [prefixWord, tailWord_1677385, baseEnd_1677385] using wordTrace_append hprefix tailTrace_1677385
  have hstable : (prefixWord ++ tailWord_1677385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677385).length < 2 ^ (prefixWord ++ tailWord_1677385).sum := by decide
  have hdescent : baseEnd_1677385 < baseStart_1677385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677400 : List Nat := [2, 1, 2, 2, 1, 5, 9]
def baseStart_1677400 : Nat := 118140960795 + 1677400 * 2 ^ 59
def prefixEnd_1677400 : Nat := 4983230072969 + 3 ^ 40 * 1677400 * 2
def baseEnd_1677400 : Nat := 21266974070415861691007

theorem tailTrace_1677400 : CollatzResearch.WordTrace tailWord_1677400 prefixEnd_1677400 21266974070415861691007 := by
  unfold tailWord_1677400
  simp only [CollatzResearch.WordTrace]
  refine ⟨30589902061536875978750827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40786536082049167971667769 30589902061536875978750827)
  ·
    refine ⟨45884853092305313968126241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30589902061536875978750827 45884853092305313968126241)
    ·
      refine ⟨34413639819228985476094681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45884853092305313968126241 34413639819228985476094681)
      ·
        refine ⟨25810229864421739107071011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34413639819228985476094681 25810229864421739107071011)
        ·
          refine ⟨38715344796632608660606517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25810229864421739107071011 38715344796632608660606517)
          ·
            refine ⟨3629563574684307061931861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38715344796632608660606517 3629563574684307061931861)
            ·
              refine ⟨21266974070415861691007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3629563574684307061931861 21266974070415861691007)
              ·
                rfl

theorem cell22_1677400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 9].length) (baseStart_1677400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677400 prefixEnd_1677400 := by exact prefixLift 1677400
  have htrace : WordTrace (prefixWord ++ tailWord_1677400) baseStart_1677400 baseEnd_1677400 := by
    simpa [prefixWord, tailWord_1677400, baseEnd_1677400] using wordTrace_append hprefix tailTrace_1677400
  have hstable : (prefixWord ++ tailWord_1677400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677400).length < 2 ^ (prefixWord ++ tailWord_1677400).sum := by decide
  have hdescent : baseEnd_1677400 < baseStart_1677400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677404 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1677404 : Nat := 118140960795 + 1677404 * 2 ^ 59
def prefixEnd_1677404 : Nat := 4983230072969 + 3 ^ 40 * 1677404 * 2
def baseEnd_1677404 : Nat := 574209669182973588557177

theorem tailTrace_1677404 : CollatzResearch.WordTrace tailWord_1677404 prefixEnd_1677404 574209669182973588557177 := by
  unfold tailWord_1677404
  simp only [CollatzResearch.WordTrace]
  refine ⟨30589975007529630320323633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40786633343372840427098177 30589975007529630320323633)
  ·
    refine ⟨22942481255647222740242725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30589975007529630320323633 22942481255647222740242725)
    ·
      refine ⟨4301715235433854263795511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22942481255647222740242725 4301715235433854263795511)
      ·
        refine ⟨6452572853150781395693267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4301715235433854263795511 6452572853150781395693267)
        ·
          refine ⟨9678859279726172093539901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6452572853150781395693267 9678859279726172093539901)
          ·
            refine ⟨3629572229897314535077463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9678859279726172093539901 3629572229897314535077463)
            ·
              refine ⟨5444358344845971802616195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3629572229897314535077463 5444358344845971802616195)
              ·
                refine ⟨8166537517268957703924293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5444358344845971802616195 8166537517268957703924293)
                ·
                  refine ⟨1531225784487929569485805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8166537517268957703924293 1531225784487929569485805)
                  ·
                    refine ⟨574209669182973588557177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531225784487929569485805 574209669182973588557177)
                    ·
                      rfl

theorem cell22_1677404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1677404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677404 prefixEnd_1677404 := by exact prefixLift 1677404
  have htrace : WordTrace (prefixWord ++ tailWord_1677404) baseStart_1677404 baseEnd_1677404 := by
    simpa [prefixWord, tailWord_1677404, baseEnd_1677404] using wordTrace_append hprefix tailTrace_1677404
  have hstable : (prefixWord ++ tailWord_1677404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677404).length < 2 ^ (prefixWord ++ tailWord_1677404).sum := by decide
  have hdescent : baseEnd_1677404 < baseStart_1677404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677421 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_1677421 : Nat := 118140960795 + 1677421 * 2 ^ 59
def prefixEnd_1677421 : Nat := 4983230072969 + 3 ^ 40 * 1677421 * 2
def baseEnd_1677421 : Nat := 574215488630391210882125

theorem tailTrace_1677421 : CollatzResearch.WordTrace tailWord_1677421 prefixEnd_1677421 574215488630391210882125 := by
  unfold tailWord_1677421
  simp only [CollatzResearch.WordTrace]
  refine ⟨61180570055997672544016117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40787046703998448362677411 61180570055997672544016117)
  ·
    refine ⟨5735678442749781801001511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61180570055997672544016117 5735678442749781801001511)
    ·
      refine ⟨8603517664124672701502267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5735678442749781801001511 8603517664124672701502267)
      ·
        refine ⟨12905276496187009052253401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8603517664124672701502267 12905276496187009052253401)
        ·
          refine ⟨9678957372140256789190051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12905276496187009052253401 9678957372140256789190051)
          ·
            refine ⟨14518436058210385183785077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9678957372140256789190051 14518436058210385183785077)
            ·
              refine ⟨1361103380457223610979851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14518436058210385183785077 1361103380457223610979851)
              ·
                refine ⟨2041655070685835416469777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361103380457223610979851 2041655070685835416469777)
                ·
                  refine ⟨1531241303014376562352333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2041655070685835416469777 1531241303014376562352333)
                  ·
                    refine ⟨574215488630391210882125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531241303014376562352333 574215488630391210882125)
                    ·
                      rfl

theorem cell22_1677421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_1677421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677421 prefixEnd_1677421 := by exact prefixLift 1677421
  have htrace : WordTrace (prefixWord ++ tailWord_1677421) baseStart_1677421 baseEnd_1677421 := by
    simpa [prefixWord, tailWord_1677421, baseEnd_1677421] using wordTrace_append hprefix tailTrace_1677421
  have hstable : (prefixWord ++ tailWord_1677421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677421).length < 2 ^ (prefixWord ++ tailWord_1677421).sum := by decide
  have hdescent : baseEnd_1677421 < baseStart_1677421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677475 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 1, 10]
def baseStart_1677475 : Nat := 118140960795 + 1677475 * 2 ^ 59
def prefixEnd_1677475 : Nat := 4983230072969 + 3 ^ 40 * 1677475 * 2
def baseEnd_1677475 : Nat := 574233973933953070031959

theorem tailTrace_1677475 : CollatzResearch.WordTrace tailWord_1677475 prefixEnd_1677475 574233973933953070031959 := by
  unfold tailWord_1677475
  simp only [CollatzResearch.WordTrace]
  refine ⟨61182539597802039766481879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40788359731868026510987919 61182539597802039766481879)
  ·
    refine ⟨91773809396703059649722819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61182539597802039766481879 91773809396703059649722819)
    ·
      refine ⟨137660714095054589474584229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91773809396703059649722819 137660714095054589474584229)
      ·
        refine ⟨25811383892822735526484543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137660714095054589474584229 25811383892822735526484543)
        ·
          refine ⟨38717075839234103289726815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25811383892822735526484543 38717075839234103289726815)
          ·
            refine ⟨58075613758851154934590223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38717075839234103289726815 58075613758851154934590223)
            ·
              refine ⟨87113420638276732401885335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58075613758851154934590223 87113420638276732401885335)
              ·
                refine ⟨130670130957415098602828003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87113420638276732401885335 130670130957415098602828003)
                ·
                  refine ⟨196005196436122647904242005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130670130957415098602828003 196005196436122647904242005)
                  ·
                    refine ⟨574233973933953070031959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 196005196436122647904242005 574233973933953070031959)
                    ·
                      rfl

theorem cell22_1677475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_1677475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677475 prefixEnd_1677475 := by exact prefixLift 1677475
  have htrace : WordTrace (prefixWord ++ tailWord_1677475) baseStart_1677475 baseEnd_1677475 := by
    simpa [prefixWord, tailWord_1677475, baseEnd_1677475] using wordTrace_append hprefix tailTrace_1677475
  have hstable : (prefixWord ++ tailWord_1677475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677475).length < 2 ^ (prefixWord ++ tailWord_1677475).sum := by decide
  have hdescent : baseEnd_1677475 < baseStart_1677475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677526 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1677526 : Nat := 118140960795 + 1677526 * 2 ^ 59
def prefixEnd_1677526 : Nat := 4983230072969 + 3 ^ 40 * 1677526 * 2
def baseEnd_1677526 : Nat := 574251432276205937006803

theorem tailTrace_1677526 : CollatzResearch.WordTrace tailWord_1677526 prefixEnd_1677526 574251432276205937006803 := by
  unfold tailWord_1677526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824024982538579717286777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40789599813744850317725621 3824024982538579717286777)
  ·
    refine ⟨2868018736903934787965083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3824024982538579717286777 2868018736903934787965083)
    ·
      refine ⟨4302028105355902181947625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2868018736903934787965083 4302028105355902181947625)
      ·
        refine ⟨3226521079016926636460719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4302028105355902181947625 3226521079016926636460719)
        ·
          refine ⟨4839781618525389954691079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3226521079016926636460719 4839781618525389954691079)
          ·
            refine ⟨7259672427788084932036619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4839781618525389954691079 7259672427788084932036619)
            ·
              refine ⟨10889508641682127398054929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7259672427788084932036619 10889508641682127398054929)
              ·
                refine ⟨8167131481261595548541197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10889508641682127398054929 8167131481261595548541197)
                ·
                  refine ⟨3062674305473098330702949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8167131481261595548541197 3062674305473098330702949)
                  ·
                    refine ⟨574251432276205937006803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3062674305473098330702949 574251432276205937006803)
                    ·
                      rfl

theorem cell22_1677526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1677526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677526 prefixEnd_1677526 := by exact prefixLift 1677526
  have htrace : WordTrace (prefixWord ++ tailWord_1677526) baseStart_1677526 baseEnd_1677526 := by
    simpa [prefixWord, tailWord_1677526, baseEnd_1677526] using wordTrace_append hprefix tailTrace_1677526
  have hstable : (prefixWord ++ tailWord_1677526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677526).length < 2 ^ (prefixWord ++ tailWord_1677526).sum := by decide
  have hdescent : baseEnd_1677526 < baseStart_1677526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677537 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1677537 : Nat := 118140960795 + 1677537 * 2 ^ 59
def prefixEnd_1677537 : Nat := 4983230072969 + 3 ^ 40 * 1677537 * 2
def baseEnd_1677537 : Nat := 574255197801005574981769

theorem tailTrace_1677537 : CollatzResearch.WordTrace tailWord_1677537 prefixEnd_1677537 574255197801005574981769 := by
  unfold tailWord_1677537
  simp only [CollatzResearch.WordTrace]
  refine ⟨61184800923577424355238865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40789867282384949570159243 61184800923577424355238865)
  ·
    refine ⟨45888600692683068266429149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61184800923577424355238865 45888600692683068266429149)
    ·
      refine ⟨17208225259756150599910931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45888600692683068266429149 17208225259756150599910931)
      ·
        refine ⟨25812337889634225899866397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17208225259756150599910931 25812337889634225899866397)
        ·
          refine ⟨9679626708612834712449899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25812337889634225899866397 9679626708612834712449899)
          ·
            refine ⟨14519440062919252068674849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9679626708612834712449899 14519440062919252068674849)
            ·
              refine ⟨10889580047189439051506137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14519440062919252068674849 10889580047189439051506137)
              ·
                refine ⟨8167185035392079288629603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10889580047189439051506137 8167185035392079288629603)
                ·
                  refine ⟨12250777553088118932944405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8167185035392079288629603 12250777553088118932944405)
                  ·
                    refine ⟨574255197801005574981769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12250777553088118932944405 574255197801005574981769)
                    ·
                      rfl

theorem cell22_1677537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1677537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677537 prefixEnd_1677537 := by exact prefixLift 1677537
  have htrace : WordTrace (prefixWord ++ tailWord_1677537) baseStart_1677537 baseEnd_1677537 := by
    simpa [prefixWord, tailWord_1677537, baseEnd_1677537] using wordTrace_append hprefix tailTrace_1677537
  have hstable : (prefixWord ++ tailWord_1677537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677537).length < 2 ^ (prefixWord ++ tailWord_1677537).sum := by decide
  have hdescent : baseEnd_1677537 < baseStart_1677537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677554 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_1677554 : Nat := 118140960795 + 1677554 * 2 ^ 59
def prefixEnd_1677554 : Nat := 4983230072969 + 3 ^ 40 * 1677554 * 2
def baseEnd_1677554 : Nat := 574261017248423197306717

theorem tailTrace_1677554 : CollatzResearch.WordTrace tailWord_1677554 prefixEnd_1677554 574261017248423197306717 := by
  unfold tailWord_1677554
  simp only [CollatzResearch.WordTrace]
  refine ⟨15296355241128959064651929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40790280643010557505738477 15296355241128959064651929)
  ·
    refine ⟨11472266430846719298488947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15296355241128959064651929 11472266430846719298488947)
    ·
      refine ⟨17208399646270078947733421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11472266430846719298488947 17208399646270078947733421)
      ·
        refine ⟨6453149867351279605400033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17208399646270078947733421 6453149867351279605400033)
        ·
          refine ⟨4839862400513459704050025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6453149867351279605400033 4839862400513459704050025)
          ·
            refine ⟨3629896800385094778037519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4839862400513459704050025 3629896800385094778037519)
            ·
              refine ⟨5444845200577642167056279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3629896800385094778037519 5444845200577642167056279)
              ·
                refine ⟨8167267800866463250584419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5444845200577642167056279 8167267800866463250584419)
                ·
                  refine ⟨12250901701299694875876629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8167267800866463250584419 12250901701299694875876629)
                  ·
                    refine ⟨574261017248423197306717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12250901701299694875876629 574261017248423197306717)
                    ·
                      rfl

theorem cell22_1677554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_1677554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677554 prefixEnd_1677554 := by exact prefixLift 1677554
  have htrace : WordTrace (prefixWord ++ tailWord_1677554) baseStart_1677554 baseEnd_1677554 := by
    simpa [prefixWord, tailWord_1677554, baseEnd_1677554] using wordTrace_append hprefix tailTrace_1677554
  have hstable : (prefixWord ++ tailWord_1677554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677554).length < 2 ^ (prefixWord ++ tailWord_1677554).sum := by decide
  have hdescent : baseEnd_1677554 < baseStart_1677554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677612 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_1677612 : Nat := 118140960795 + 1677612 * 2 ^ 59
def prefixEnd_1677612 : Nat := 4983230072969 + 3 ^ 40 * 1677612 * 2
def baseEnd_1677612 : Nat := 574280871833730379356539

theorem tailTrace_1677612 : CollatzResearch.WordTrace tailWord_1677612 prefixEnd_1677612 574280871833730379356539 := by
  unfold tailWord_1677612
  simp only [CollatzResearch.WordTrace]
  refine ⟨30593768199152856082109545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40791690932203808109479393 30593768199152856082109545)
  ·
    refine ⟨22945326149364642061582159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30593768199152856082109545 22945326149364642061582159)
    ·
      refine ⟨34417989224046963092373239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22945326149364642061582159 34417989224046963092373239)
      ·
        refine ⟨51626983836070444638559859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34417989224046963092373239 51626983836070444638559859)
        ·
          refine ⟨77440475754105666957839789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51626983836070444638559859 77440475754105666957839789)
          ·
            refine ⟨29040178407789625109189921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77440475754105666957839789 29040178407789625109189921)
            ·
              refine ⟨21780133805842218831892441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29040178407789625109189921 21780133805842218831892441)
              ·
                refine ⟨16335100354381664123919331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21780133805842218831892441 16335100354381664123919331)
                ·
                  refine ⟨24502650531572496185878997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16335100354381664123919331 24502650531572496185878997)
                  ·
                    refine ⟨574280871833730379356539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24502650531572496185878997 574280871833730379356539)
                    ·
                      rfl

theorem cell22_1677612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_1677612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677612 prefixEnd_1677612 := by exact prefixLift 1677612
  have htrace : WordTrace (prefixWord ++ tailWord_1677612) baseStart_1677612 baseEnd_1677612 := by
    simpa [prefixWord, tailWord_1677612, baseEnd_1677612] using wordTrace_append hprefix tailTrace_1677612
  have hstable : (prefixWord ++ tailWord_1677612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677612).length < 2 ^ (prefixWord ++ tailWord_1677612).sum := by decide
  have hdescent : baseEnd_1677612 < baseStart_1677612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677644 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_1677644 : Nat := 118140960795 + 1677644 * 2 ^ 59
def prefixEnd_1677644 : Nat := 4983230072969 + 3 ^ 40 * 1677644 * 2
def baseEnd_1677644 : Nat := 574291826087692962556441

theorem tailTrace_1677644 : CollatzResearch.WordTrace tailWord_1677644 prefixEnd_1677644 574291826087692962556441 := by
  unfold tailWord_1677644
  simp only [CollatzResearch.WordTrace]
  refine ⟨30594351767094890814691993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40792469022793187752922657 30594351767094890814691993)
  ·
    refine ⟨22945763825321168111018995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30594351767094890814691993 22945763825321168111018995)
    ·
      refine ⟨34418645737981752166528493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22945763825321168111018995 34418645737981752166528493)
      ·
        refine ⟨12906992151743157062448185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34418645737981752166528493 12906992151743157062448185)
        ·
          refine ⟨9680244113807367796836139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12906992151743157062448185 9680244113807367796836139)
          ·
            refine ⟨14520366170711051695254209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9680244113807367796836139 14520366170711051695254209)
            ·
              refine ⟨10890274628033288771440657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14520366170711051695254209 10890274628033288771440657)
              ·
                refine ⟨8167705971024966578580493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10890274628033288771440657 8167705971024966578580493)
                ·
                  refine ⟨3062889739134362466967685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8167705971024966578580493 3062889739134362466967685)
                  ·
                    refine ⟨574291826087692962556441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3062889739134362466967685 574291826087692962556441)
                    ·
                      rfl

theorem cell22_1677644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_1677644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677644 prefixEnd_1677644 := by exact prefixLift 1677644
  have htrace : WordTrace (prefixWord ++ tailWord_1677644) baseStart_1677644 baseEnd_1677644 := by
    simpa [prefixWord, tailWord_1677644, baseEnd_1677644] using wordTrace_append hprefix tailTrace_1677644
  have hstable : (prefixWord ++ tailWord_1677644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677644).length < 2 ^ (prefixWord ++ tailWord_1677644).sum := by decide
  have hdescent : baseEnd_1677644 < baseStart_1677644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677686 : List Nat := [5, 1, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_1677686 : Nat := 118140960795 + 1677686 * 2 ^ 59
def prefixEnd_1677686 : Nat := 4983230072969 + 3 ^ 40 * 1677686 * 2
def baseEnd_1677686 : Nat := 574306203546018853006313

theorem tailTrace_1677686 : CollatzResearch.WordTrace tailWord_1677686 prefixEnd_1677686 574306203546018853006313 := by
  unfold tailWord_1677686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824389712502351425150807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40793490266691748534941941 3824389712502351425150807)
  ·
    refine ⟨5736584568753527137726211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3824389712502351425150807 5736584568753527137726211)
    ·
      refine ⟨8604876853130290706589317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5736584568753527137726211 8604876853130290706589317)
      ·
        refine ⟨1613414409961929507485497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8604876853130290706589317 1613414409961929507485497)
        ·
          refine ⟨1210060807471447130614123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1613414409961929507485497 1210060807471447130614123)
          ·
            refine ⟨1815091211207170695921185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210060807471447130614123 1815091211207170695921185)
            ·
              refine ⟨1361318408405378021940889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1815091211207170695921185 1361318408405378021940889)
              ·
                refine ⟨1020988806304033516455667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361318408405378021940889 1020988806304033516455667)
                ·
                  refine ⟨1531483209456050274683501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020988806304033516455667 1531483209456050274683501)
                  ·
                    refine ⟨574306203546018853006313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531483209456050274683501 574306203546018853006313)
                    ·
                      rfl

theorem cell22_1677686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_1677686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677686 prefixEnd_1677686 := by exact prefixLift 1677686
  have htrace : WordTrace (prefixWord ++ tailWord_1677686) baseStart_1677686 baseEnd_1677686 := by
    simpa [prefixWord, tailWord_1677686, baseEnd_1677686] using wordTrace_append hprefix tailTrace_1677686
  have hstable : (prefixWord ++ tailWord_1677686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677686).length < 2 ^ (prefixWord ++ tailWord_1677686).sum := by decide
  have hdescent : baseEnd_1677686 < baseStart_1677686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677691 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 2, 3]
def baseStart_1677691 : Nat := 118140960795 + 1677691 * 2 ^ 59
def prefixEnd_1677691 : Nat := 4983230072969 + 3 ^ 40 * 1677691 * 2
def baseEnd_1677691 : Nat := 574307915148200506631297

theorem tailTrace_1677691 : CollatzResearch.WordTrace tailWord_1677691 prefixEnd_1677691 574307915148200506631297 := by
  unfold tailWord_1677691
  simp only [CollatzResearch.WordTrace]
  refine ⟨61190417765019508656344927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40793611843346339104229951 61190417765019508656344927)
  ·
    refine ⟨91785626647529262984517391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61190417765019508656344927 91785626647529262984517391)
    ·
      refine ⟨137678439971293894476776087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91785626647529262984517391 137678439971293894476776087)
      ·
        refine ⟨206517659956940841715164131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137678439971293894476776087 206517659956940841715164131)
        ·
          refine ⟨309776489935411262572746197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206517659956940841715164131 309776489935411262572746197)
          ·
            refine ⟨7260386482861201466548739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 309776489935411262572746197 7260386482861201466548739)
            ·
              refine ⟨10890579724291802199823109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7260386482861201466548739 10890579724291802199823109)
              ·
                refine ⟨2041983698304712912466833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10890579724291802199823109 2041983698304712912466833)
                ·
                  refine ⟨1531487773728534684350125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2041983698304712912466833 1531487773728534684350125)
                  ·
                    refine ⟨574307915148200506631297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531487773728534684350125 574307915148200506631297)
                    ·
                      rfl

theorem cell22_1677691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 3].length) (baseStart_1677691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677691 prefixEnd_1677691 := by exact prefixLift 1677691
  have htrace : WordTrace (prefixWord ++ tailWord_1677691) baseStart_1677691 baseEnd_1677691 := by
    simpa [prefixWord, tailWord_1677691, baseEnd_1677691] using wordTrace_append hprefix tailTrace_1677691
  have hstable : (prefixWord ++ tailWord_1677691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677691).length < 2 ^ (prefixWord ++ tailWord_1677691).sum := by decide
  have hdescent : baseEnd_1677691 < baseStart_1677691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677693 : List Nat := [1, 4, 1, 1, 2, 3, 4, 2, 4]
def baseStart_1677693 : Nat := 118140960795 + 1677693 * 2 ^ 59
def prefixEnd_1677693 : Nat := 4983230072969 + 3 ^ 40 * 1677693 * 2
def baseEnd_1677693 : Nat := 191436199929691056027097

theorem tailTrace_1677693 : CollatzResearch.WordTrace tailWord_1677693 prefixEnd_1677693 191436199929691056027097 := by
  unfold tailWord_1677693
  simp only [CollatzResearch.WordTrace]
  refine ⟨61190490711012262997917733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40793660474008175331945155 61190490711012262997917733)
  ·
    refine ⟨11473217008314799312109575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61190490711012262997917733 11473217008314799312109575)
    ·
      refine ⟨17209825512472198968164363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11473217008314799312109575 17209825512472198968164363)
      ·
        refine ⟨25814738268708298452246545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17209825512472198968164363 25814738268708298452246545)
        ·
          refine ⟨19361053701531223839184909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25814738268708298452246545 19361053701531223839184909)
          ·
            refine ⟨7260395138074208939694341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19361053701531223839184909 7260395138074208939694341)
            ·
              refine ⟨1361324088388914176192689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7260395138074208939694341 1361324088388914176192689)
              ·
                refine ⟨1020993066291685632144517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361324088388914176192689 1020993066291685632144517)
                ·
                  refine ⟨191436199929691056027097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1020993066291685632144517 191436199929691056027097)
                  ·
                    rfl

theorem cell22_1677693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_1677693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677693 prefixEnd_1677693 := by exact prefixLift 1677693
  have htrace : WordTrace (prefixWord ++ tailWord_1677693) baseStart_1677693 baseEnd_1677693 := by
    simpa [prefixWord, tailWord_1677693, baseEnd_1677693] using wordTrace_append hprefix tailTrace_1677693
  have hstable : (prefixWord ++ tailWord_1677693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677693).length < 2 ^ (prefixWord ++ tailWord_1677693).sum := by decide
  have hdescent : baseEnd_1677693 < baseStart_1677693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677753 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 3, 3]
def baseStart_1677753 : Nat := 118140960795 + 1677753 * 2 ^ 59
def prefixEnd_1677753 : Nat := 4983230072969 + 3 ^ 40 * 1677753 * 2
def baseEnd_1677753 : Nat := 574329139015253011581107

theorem tailTrace_1677753 : CollatzResearch.WordTrace tailWord_1677753 prefixEnd_1677753 574329139015253011581107 := by
  unfold tailWord_1677753
  simp only [CollatzResearch.WordTrace]
  refine ⟨61192679090794893245101913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40795119393863262163401275 61192679090794893245101913)
  ·
    refine ⟨45894509318096169933826435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61192679090794893245101913 45894509318096169933826435)
    ·
      refine ⟨68841763977144254900739653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45894509318096169933826435 68841763977144254900739653)
      ·
        refine ⟨12907830745714547793888685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68841763977144254900739653 12907830745714547793888685)
        ·
          refine ⟨4840436529642955422708257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12907830745714547793888685 4840436529642955422708257)
          ·
            refine ⟨3630327397232216567031193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4840436529642955422708257 3630327397232216567031193)
            ·
              refine ⟨2722745547924162425273395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3630327397232216567031193 2722745547924162425273395)
              ·
                refine ⟨4084118321886243637910093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722745547924162425273395 4084118321886243637910093)
                ·
                  refine ⟨1531544370707341364216285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4084118321886243637910093 1531544370707341364216285)
                  ·
                    refine ⟨574329139015253011581107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531544370707341364216285 574329139015253011581107)
                    ·
                      rfl

theorem cell22_1677753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 3].length) (baseStart_1677753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677753 prefixEnd_1677753 := by exact prefixLift 1677753
  have htrace : WordTrace (prefixWord ++ tailWord_1677753) baseStart_1677753 baseEnd_1677753 := by
    simpa [prefixWord, tailWord_1677753, baseEnd_1677753] using wordTrace_append hprefix tailTrace_1677753
  have hstable : (prefixWord ++ tailWord_1677753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677753).length < 2 ^ (prefixWord ++ tailWord_1677753).sum := by decide
  have hdescent : baseEnd_1677753 < baseStart_1677753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677779 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 9, 4]
def baseStart_1677779 : Nat := 118140960795 + 1677779 * 2 ^ 59
def prefixEnd_1677779 : Nat := 4983230072969 + 3 ^ 40 * 1677779 * 2
def baseEnd_1677779 : Nat := 574338039346597610431027

theorem tailTrace_1677779 : CollatzResearch.WordTrace tailWord_1677779 prefixEnd_1677779 574338039346597610431027 := by
  unfold tailWord_1677779
  simp only [CollatzResearch.WordTrace]
  refine ⟨61193627388700699685548391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40795751592467133123698927 61193627388700699685548391)
  ·
    refine ⟨91790441083051049528322587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61193627388700699685548391 91790441083051049528322587)
    ·
      refine ⟨137685661624576574292483881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91790441083051049528322587 137685661624576574292483881)
      ·
        refine ⟨103264246218432430719362911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137685661624576574292483881 103264246218432430719362911)
        ·
          refine ⟨154896369327648646079044367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103264246218432430719362911 154896369327648646079044367)
          ·
            refine ⟨232344553991472969118566551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154896369327648646079044367 232344553991472969118566551)
            ·
              refine ⟨348516830987209453677849827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232344553991472969118566551 348516830987209453677849827)
              ·
                refine ⟨522775246480814180516774741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348516830987209453677849827 522775246480814180516774741)
                ·
                  refine ⟨3063136209848520588965477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 522775246480814180516774741 3063136209848520588965477)
                  ·
                    refine ⟨574338039346597610431027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3063136209848520588965477 574338039346597610431027)
                    ·
                      rfl

theorem cell22_1677779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 4].length) (baseStart_1677779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677779 prefixEnd_1677779 := by exact prefixLift 1677779
  have htrace : WordTrace (prefixWord ++ tailWord_1677779) baseStart_1677779 baseEnd_1677779 := by
    simpa [prefixWord, tailWord_1677779, baseEnd_1677779] using wordTrace_append hprefix tailTrace_1677779
  have hstable : (prefixWord ++ tailWord_1677779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677779).length < 2 ^ (prefixWord ++ tailWord_1677779).sum := by decide
  have hdescent : baseEnd_1677779 < baseStart_1677779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677847 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 1, 4]
def baseStart_1677847 : Nat := 118140960795 + 1677847 * 2 ^ 59
def prefixEnd_1677847 : Nat := 4983230072969 + 3 ^ 40 * 1677847 * 2
def baseEnd_1677847 : Nat := 574361317136268099730819

theorem tailTrace_1677847 : CollatzResearch.WordTrace tailWord_1677847 prefixEnd_1677847 574361317136268099730819 := by
  unfold tailWord_1677847
  simp only [CollatzResearch.WordTrace]
  refine ⟨61196107552454347299023795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40797405034969564866015863 61196107552454347299023795)
  ·
    refine ⟨91794161328681520948535693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61196107552454347299023795 91794161328681520948535693)
    ·
      refine ⟨34422810498255570355700885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91794161328681520948535693 34422810498255570355700885)
      ·
        refine ⟨1613569242105729860423479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34422810498255570355700885 1613569242105729860423479)
        ·
          refine ⟨2420353863158594790635219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613569242105729860423479 2420353863158594790635219)
          ·
            refine ⟨3630530794737892185952829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420353863158594790635219 3630530794737892185952829)
            ·
              refine ⟨1361449048026709569732311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3630530794737892185952829 1361449048026709569732311)
              ·
                refine ⟨2042173572040064354598467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361449048026709569732311 2042173572040064354598467)
                ·
                  refine ⟨3063260358060096531897701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042173572040064354598467 3063260358060096531897701)
                  ·
                    refine ⟨574361317136268099730819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3063260358060096531897701 574361317136268099730819)
                    ·
                      rfl

theorem cell22_1677847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_1677847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677847 prefixEnd_1677847 := by exact prefixLift 1677847
  have htrace : WordTrace (prefixWord ++ tailWord_1677847) baseStart_1677847 baseEnd_1677847 := by
    simpa [prefixWord, tailWord_1677847, baseEnd_1677847] using wordTrace_append hprefix tailTrace_1677847
  have hstable : (prefixWord ++ tailWord_1677847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677847).length < 2 ^ (prefixWord ++ tailWord_1677847).sum := by decide
  have hdescent : baseEnd_1677847 < baseStart_1677847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677856 : List Nat := [2, 1, 1, 6, 2, 10]
def baseStart_1677856 : Nat := 118140960795 + 1677856 * 2 ^ 59
def prefixEnd_1677856 : Nat := 4983230072969 + 3 ^ 40 * 1677856 * 2
def baseEnd_1677856 : Nat := 7090918494076482422911

theorem tailTrace_1677856 : CollatzResearch.WordTrace tailWord_1677856 prefixEnd_1677856 7090918494076482422911 := by
  unfold tailWord_1677856
  simp only [CollatzResearch.WordTrace]
  refine ⟨30598217904710870918050711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40797623872947827890734281 30598217904710870918050711)
  ·
    refine ⟨45897326857066306377076067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30598217904710870918050711 45897326857066306377076067)
    ·
      refine ⟨68845990285599459565614101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45897326857066306377076067 68845990285599459565614101)
      ·
        refine ⟨3227155794637474667138161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68845990285599459565614101 3227155794637474667138161)
        ·
          refine ⟨2420366845978106000353621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3227155794637474667138161 2420366845978106000353621)
          ·
            refine ⟨7090918494076482422911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2420366845978106000353621 7090918494076482422911)
            ·
              rfl

theorem cell22_1677856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 10].length) (baseStart_1677856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677856 prefixEnd_1677856 := by exact prefixLift 1677856
  have htrace : WordTrace (prefixWord ++ tailWord_1677856) baseStart_1677856 baseEnd_1677856 := by
    simpa [prefixWord, tailWord_1677856, baseEnd_1677856] using wordTrace_append hprefix tailTrace_1677856
  have hstable : (prefixWord ++ tailWord_1677856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677856).length < 2 ^ (prefixWord ++ tailWord_1677856).sum := by decide
  have hdescent : baseEnd_1677856 < baseStart_1677856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677871 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 9, 3]
def baseStart_1677871 : Nat := 118140960795 + 1677871 * 2 ^ 59
def prefixEnd_1677871 : Nat := 4983230072969 + 3 ^ 40 * 1677871 * 2
def baseEnd_1677871 : Nat := 574369532826740037130745

theorem tailTrace_1677871 : CollatzResearch.WordTrace tailWord_1677871 prefixEnd_1677871 574369532826740037130745 := by
  unfold tailWord_1677871
  simp only [CollatzResearch.WordTrace]
  refine ⟨61196982904367399397897467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40797988602911599598598311 61196982904367399397897467)
  ·
    refine ⟨91795474356551099096846201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61196982904367399397897467 91795474356551099096846201)
    ·
      refine ⟨68846605767413324322634651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91795474356551099096846201 68846605767413324322634651)
      ·
        refine ⟨103269908651119986483951977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68846605767413324322634651 103269908651119986483951977)
        ·
          refine ⟨77452431488339989862963983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103269908651119986483951977 77452431488339989862963983)
          ·
            refine ⟨116178647232509984794445975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77452431488339989862963983 116178647232509984794445975)
            ·
              refine ⟨174267970848764977191668963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116178647232509984794445975 174267970848764977191668963)
              ·
                refine ⟨261401956273147465787503445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174267970848764977191668963 261401956273147465787503445)
                ·
                  refine ⟨1531652087537973432348653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 261401956273147465787503445 1531652087537973432348653)
                  ·
                    refine ⟨574369532826740037130745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531652087537973432348653 574369532826740037130745)
                    ·
                      rfl

theorem cell22_1677871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 3].length) (baseStart_1677871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677871 prefixEnd_1677871 := by exact prefixLift 1677871
  have htrace : WordTrace (prefixWord ++ tailWord_1677871) baseStart_1677871 baseEnd_1677871 := by
    simpa [prefixWord, tailWord_1677871, baseEnd_1677871] using wordTrace_append hprefix tailTrace_1677871
  have hstable : (prefixWord ++ tailWord_1677871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677871).length < 2 ^ (prefixWord ++ tailWord_1677871).sum := by decide
  have hdescent : baseEnd_1677871 < baseStart_1677871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677892 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1677892 : Nat := 118140960795 + 1677892 * 2 ^ 59
def prefixEnd_1677892 : Nat := 4983230072969 + 3 ^ 40 * 1677892 * 2
def baseEnd_1677892 : Nat := 574376721555902982355681

theorem tailTrace_1677892 : CollatzResearch.WordTrace tailWord_1677892 prefixEnd_1677892 574376721555902982355681 := by
  unfold tailWord_1677892
  simp only [CollatzResearch.WordTrace]
  refine ⟨30598874418645659992205965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40798499224860879989607953 30598874418645659992205965)
  ·
    refine ⟨11474577906992122497077237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30598874418645659992205965 11474577906992122497077237)
    ·
      refine ⟨1075741678780511484100991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11474577906992122497077237 1075741678780511484100991)
      ·
        refine ⟨1613612518170767226151487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075741678780511484100991 1613612518170767226151487)
        ·
          refine ⟨2420418777256150839227231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613612518170767226151487 2420418777256150839227231)
          ·
            refine ⟨3630628165884226258840847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420418777256150839227231 3630628165884226258840847)
            ·
              refine ⟨5445942248826339388261271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3630628165884226258840847 5445942248826339388261271)
              ·
                refine ⟨8168913373239509082391907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445942248826339388261271 8168913373239509082391907)
                ·
                  refine ⟨12253370059859263623587861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8168913373239509082391907 12253370059859263623587861)
                  ·
                    refine ⟨574376721555902982355681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12253370059859263623587861 574376721555902982355681)
                    ·
                      rfl

theorem cell22_1677892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1677892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677892 prefixEnd_1677892 := by exact prefixLift 1677892
  have htrace : WordTrace (prefixWord ++ tailWord_1677892) baseStart_1677892 baseEnd_1677892 := by
    simpa [prefixWord, tailWord_1677892, baseEnd_1677892] using wordTrace_append hprefix tailTrace_1677892
  have hstable : (prefixWord ++ tailWord_1677892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677892).length < 2 ^ (prefixWord ++ tailWord_1677892).sum := by decide
  have hdescent : baseEnd_1677892 < baseStart_1677892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677905 : List Nat := [1, 2, 2, 1, 3, 3, 1, 5, 1, 3]
def baseStart_1677905 : Nat := 118140960795 + 1677905 * 2 ^ 59
def prefixEnd_1677905 : Nat := 4983230072969 + 3 ^ 40 * 1677905 * 2
def baseEnd_1677905 : Nat := 574381171721575281780641

theorem tailTrace_1677905 : CollatzResearch.WordTrace tailWord_1677905 prefixEnd_1677905 574381171721575281780641 := by
  unfold tailWord_1677905
  simp only [CollatzResearch.WordTrace]
  refine ⟨61198222986244223204635169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40798815324162815469756779 61198222986244223204635169)
  ·
    refine ⟨45898667239683167403476377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61198222986244223204635169 45898667239683167403476377)
    ·
      refine ⟨34424000429762375552607283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45898667239683167403476377 34424000429762375552607283)
      ·
        refine ⟨51636000644643563328910925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34424000429762375552607283 51636000644643563328910925)
        ·
          refine ⟨19363500241741336248341597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51636000644643563328910925 19363500241741336248341597)
          ·
            refine ⟨7261312590653001093128099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19363500241741336248341597 7261312590653001093128099)
            ·
              refine ⟨10891968885979501639692149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7261312590653001093128099 10891968885979501639692149)
              ·
                refine ⟨1021122083060578278721139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10891968885979501639692149 1021122083060578278721139)
                ·
                  refine ⟨1531683124590867418081709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021122083060578278721139 1531683124590867418081709)
                  ·
                    refine ⟨574381171721575281780641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531683124590867418081709 574381171721575281780641)
                    ·
                      rfl

theorem cell22_1677905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_1677905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677905 prefixEnd_1677905 := by exact prefixLift 1677905
  have htrace : WordTrace (prefixWord ++ tailWord_1677905) baseStart_1677905 baseEnd_1677905 := by
    simpa [prefixWord, tailWord_1677905, baseEnd_1677905] using wordTrace_append hprefix tailTrace_1677905
  have hstable : (prefixWord ++ tailWord_1677905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677905).length < 2 ^ (prefixWord ++ tailWord_1677905).sum := by decide
  have hdescent : baseEnd_1677905 < baseStart_1677905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677931 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 3, 4]
def baseStart_1677931 : Nat := 118140960795 + 1677931 * 2 ^ 59
def prefixEnd_1677931 : Nat := 4983230072969 + 3 ^ 40 * 1677931 * 2
def baseEnd_1677931 : Nat := 574390072052919880630561

theorem tailTrace_1677931 : CollatzResearch.WordTrace tailWord_1677931 prefixEnd_1677931 574390072052919880630561 := by
  unfold tailWord_1677931
  simp only [CollatzResearch.WordTrace]
  refine ⟨61199171284150029645081647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40799447522766686430054431 61199171284150029645081647)
  ·
    refine ⟨91798756926225044467622471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61199171284150029645081647 91798756926225044467622471)
    ·
      refine ⟨137698135389337566701433707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91798756926225044467622471 137698135389337566701433707)
      ·
        refine ⟨206547203084006350052150561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137698135389337566701433707 206547203084006350052150561)
        ·
          refine ⟨154910402313004762539112921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206547203084006350052150561 154910402313004762539112921)
          ·
            refine ⟨116182801734753571904334691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154910402313004762539112921 116182801734753571904334691)
            ·
              refine ⟨174274202602130357856502037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116182801734753571904334691 174274202602130357856502037)
              ·
                refine ⟨8169103246974860524523533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174274202602130357856502037 8169103246974860524523533)
                ·
                  refine ⟨3063413717615572696696325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8169103246974860524523533 3063413717615572696696325)
                  ·
                    refine ⟨574390072052919880630561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3063413717615572696696325 574390072052919880630561)
                    ·
                      rfl

theorem cell22_1677931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 4].length) (baseStart_1677931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677931 prefixEnd_1677931 := by exact prefixLift 1677931
  have htrace : WordTrace (prefixWord ++ tailWord_1677931) baseStart_1677931 baseEnd_1677931 := by
    simpa [prefixWord, tailWord_1677931, baseEnd_1677931] using wordTrace_append hprefix tailTrace_1677931
  have hstable : (prefixWord ++ tailWord_1677931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677931).length < 2 ^ (prefixWord ++ tailWord_1677931).sum := by decide
  have hdescent : baseEnd_1677931 < baseStart_1677931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677933 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1677933 : Nat := 118140960795 + 1677933 * 2 ^ 59
def prefixEnd_1677933 : Nat := 4983230072969 + 3 ^ 40 * 1677933 * 2
def baseEnd_1677933 : Nat := 574390756693792542080555

theorem tailTrace_1677933 : CollatzResearch.WordTrace tailWord_1677933 prefixEnd_1677933 574390756693792542080555 := by
  unfold tailWord_1677933
  simp only [CollatzResearch.WordTrace]
  refine ⟨61199244230142783986654453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40799496153428522657769635 61199244230142783986654453)
  ·
    refine ⟨5737429146575885998748855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61199244230142783986654453 5737429146575885998748855)
    ·
      refine ⟨8606143719863828998123283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5737429146575885998748855 8606143719863828998123283)
      ·
        refine ⟨12909215579795743497184925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8606143719863828998123283 12909215579795743497184925)
        ·
          refine ⟨4840955842423403811444347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12909215579795743497184925 4840955842423403811444347)
          ·
            refine ⟨7261433763635105717166521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4840955842423403811444347 7261433763635105717166521)
            ·
              refine ⟨5446075322726329287874891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7261433763635105717166521 5446075322726329287874891)
              ·
                refine ⟨8169112984089493931812337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5446075322726329287874891 8169112984089493931812337)
                ·
                  refine ⟨6126834738067120448859253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8169112984089493931812337 6126834738067120448859253)
                  ·
                    refine ⟨574390756693792542080555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6126834738067120448859253 574390756693792542080555)
                    ·
                      rfl

theorem cell22_1677933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1677933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677933 prefixEnd_1677933 := by exact prefixLift 1677933
  have htrace : WordTrace (prefixWord ++ tailWord_1677933) baseStart_1677933 baseEnd_1677933 := by
    simpa [prefixWord, tailWord_1677933, baseEnd_1677933] using wordTrace_append hprefix tailTrace_1677933
  have hstable : (prefixWord ++ tailWord_1677933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677933).length < 2 ^ (prefixWord ++ tailWord_1677933).sum := by decide
  have hdescent : baseEnd_1677933 < baseStart_1677933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677948 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_1677948 : Nat := 118140960795 + 1677948 * 2 ^ 59
def prefixEnd_1677948 : Nat := 4983230072969 + 3 ^ 40 * 1677948 * 2
def baseEnd_1677948 : Nat := 574395891500337502955509

theorem tailTrace_1677948 : CollatzResearch.WordTrace tailWord_1677948 prefixEnd_1677948 574395891500337502955509 := by
  unfold tailWord_1677948
  simp only [CollatzResearch.WordTrace]
  refine ⟨30599895662544220774225249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40799860883392294365633665 30599895662544220774225249)
  ·
    refine ⟨22949921746908165580668937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30599895662544220774225249 22949921746908165580668937)
    ·
      refine ⟨17212441310181124185501703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22949921746908165580668937 17212441310181124185501703)
      ·
        refine ⟨25818661965271686278252555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17212441310181124185501703 25818661965271686278252555)
        ·
          refine ⟨38727992947907529417378833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25818661965271686278252555 38727992947907529417378833)
          ·
            refine ⟨29045994710930647063034125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38727992947907529417378833 29045994710930647063034125)
            ·
              refine ⟨10892248016598992648637797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29045994710930647063034125 10892248016598992648637797)
              ·
                refine ⟨2042296503112311121619587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10892248016598992648637797 2042296503112311121619587)
                ·
                  refine ⟨3063444754668466682429381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042296503112311121619587 3063444754668466682429381)
                  ·
                    refine ⟨574395891500337502955509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3063444754668466682429381 574395891500337502955509)
                    ·
                      rfl

theorem cell22_1677948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_1677948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677948 prefixEnd_1677948 := by exact prefixLift 1677948
  have htrace : WordTrace (prefixWord ++ tailWord_1677948) baseStart_1677948 baseEnd_1677948 := by
    simpa [prefixWord, tailWord_1677948, baseEnd_1677948] using wordTrace_append hprefix tailTrace_1677948
  have hstable : (prefixWord ++ tailWord_1677948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677948).length < 2 ^ (prefixWord ++ tailWord_1677948).sum := by decide
  have hdescent : baseEnd_1677948 < baseStart_1677948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677961 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_1677961 : Nat := 118140960795 + 1677961 * 2 ^ 59
def prefixEnd_1677961 : Nat := 4983230072969 + 3 ^ 40 * 1677961 * 2
def baseEnd_1677961 : Nat := 574400341666009802380469

theorem tailTrace_1677961 : CollatzResearch.WordTrace tailWord_1677961 prefixEnd_1677961 574400341666009802380469 := by
  unfold tailWord_1677961
  simp only [CollatzResearch.WordTrace]
  refine ⟨61200265474041344768673737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40800176982694229845782491 61200265474041344768673737)
  ·
    refine ⟨45900199105531008576505303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61200265474041344768673737 45900199105531008576505303)
    ·
      refine ⟨68850298658296512864757955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45900199105531008576505303 68850298658296512864757955)
      ·
        refine ⟨103275447987444769297136933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68850298658296512864757955 103275447987444769297136933)
        ·
          refine ⟨19364146497645894243213175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103275447987444769297136933 19364146497645894243213175)
          ·
            refine ⟨29046219746468841364819763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19364146497645894243213175 29046219746468841364819763)
            ·
              refine ⟨43569329619703262047229645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29046219746468841364819763 43569329619703262047229645)
              ·
                refine ⟨16338498607388723267711117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43569329619703262047229645 16338498607388723267711117)
                ·
                  refine ⟨6126936977770771225391669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16338498607388723267711117 6126936977770771225391669)
                  ·
                    refine ⟨574400341666009802380469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6126936977770771225391669 574400341666009802380469)
                    ·
                      rfl

theorem cell22_1677961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_1677961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677961 prefixEnd_1677961 := by exact prefixLift 1677961
  have htrace : WordTrace (prefixWord ++ tailWord_1677961) baseStart_1677961 baseEnd_1677961 := by
    simpa [prefixWord, tailWord_1677961, baseEnd_1677961] using wordTrace_append hprefix tailTrace_1677961
  have hstable : (prefixWord ++ tailWord_1677961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677961).length < 2 ^ (prefixWord ++ tailWord_1677961).sum := by decide
  have hdescent : baseEnd_1677961 < baseStart_1677961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677963 : List Nat := [1, 1, 1, 1, 4, 1, 2, 7, 4]
def baseStart_1677963 : Nat := 118140960795 + 1677963 * 2 ^ 59
def prefixEnd_1677963 : Nat := 4983230072969 + 3 ^ 40 * 1677963 * 2
def baseEnd_1677963 : Nat := 191467008768960821276821

theorem tailTrace_1677963 : CollatzResearch.WordTrace tailWord_1677963 prefixEnd_1677963 191467008768960821276821 := by
  unfold tailWord_1677963
  simp only [CollatzResearch.WordTrace]
  refine ⟨61200338420034099110246543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40800225613356066073497695 61200338420034099110246543)
  ·
    refine ⟨91800507630051148665369815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61200338420034099110246543 91800507630051148665369815)
    ·
      refine ⟨137700761445076722998054723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91800507630051148665369815 137700761445076722998054723)
      ·
        refine ⟨206551142167615084497082085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137700761445076722998054723 206551142167615084497082085)
        ·
          refine ⟨38728339156427828343202891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206551142167615084497082085 38728339156427828343202891)
          ·
            refine ⟨58092508734641742514804337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38728339156427828343202891 58092508734641742514804337)
            ·
              refine ⟨43569381550981306886103253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58092508734641742514804337 43569381550981306886103253)
              ·
                refine ⟨1021157380101124380143045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43569381550981306886103253 1021157380101124380143045)
                ·
                  refine ⟨191467008768960821276821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1021157380101124380143045 191467008768960821276821)
                  ·
                    rfl

theorem cell22_1677963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 4].length) (baseStart_1677963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677963 prefixEnd_1677963 := by exact prefixLift 1677963
  have htrace : WordTrace (prefixWord ++ tailWord_1677963) baseStart_1677963 baseEnd_1677963 := by
    simpa [prefixWord, tailWord_1677963, baseEnd_1677963] using wordTrace_append hprefix tailTrace_1677963
  have hstable : (prefixWord ++ tailWord_1677963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677963).length < 2 ^ (prefixWord ++ tailWord_1677963).sum := by decide
  have hdescent : baseEnd_1677963 < baseStart_1677963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677980 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 6]
def baseStart_1677980 : Nat := 118140960795 + 1677980 * 2 ^ 59
def prefixEnd_1677980 : Nat := 4983230072969 + 3 ^ 40 * 1677980 * 2
def baseEnd_1677980 : Nat := 191468948584766695385137

theorem tailTrace_1677980 : CollatzResearch.WordTrace tailWord_1677980 prefixEnd_1677980 191468948584766695385137 := by
  unfold tailWord_1677980
  simp only [CollatzResearch.WordTrace]
  refine ⟨30600479230486255506807697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40800638973981674009076929 30600479230486255506807697)
  ·
    refine ⟨22950359422864691630105773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30600479230486255506807697 22950359422864691630105773)
    ·
      refine ⟨8606384783574259361289665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22950359422864691630105773 8606384783574259361289665)
      ·
        refine ⟨6454788587680694520967249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8606384783574259361289665 6454788587680694520967249)
        ·
          refine ⟨4841091440760520890725437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6454788587680694520967249 4841091440760520890725437)
          ·
            refine ⟨1815409290285195334022039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4841091440760520890725437 1815409290285195334022039)
            ·
              refine ⟨2723113935427793001033059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815409290285195334022039 2723113935427793001033059)
              ·
                refine ⟨4084670903141689501549589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723113935427793001033059 4084670903141689501549589)
                ·
                  refine ⟨191468948584766695385137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4084670903141689501549589 191468948584766695385137)
                  ·
                    rfl

theorem cell22_1677980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_1677980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1677980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1677980 prefixEnd_1677980 := by exact prefixLift 1677980
  have htrace : WordTrace (prefixWord ++ tailWord_1677980) baseStart_1677980 baseEnd_1677980 := by
    simpa [prefixWord, tailWord_1677980, baseEnd_1677980] using wordTrace_append hprefix tailTrace_1677980
  have hstable : (prefixWord ++ tailWord_1677980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677980).length < 2 ^ (prefixWord ++ tailWord_1677980).sum := by decide
  have hdescent : baseEnd_1677980 < baseStart_1677980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678021 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_1678021 : Nat := 118140960795 + 1678021 * 2 ^ 59
def prefixEnd_1678021 : Nat := 4983230072969 + 3 ^ 40 * 1678021 * 2
def baseEnd_1678021 : Nat := 574420880892189645880285

theorem tailTrace_1678021 : CollatzResearch.WordTrace tailWord_1678021 prefixEnd_1678021 574420880892189645880285 := by
  unfold tailWord_1678021
  simp only [CollatzResearch.WordTrace]
  refine ⟨61202453853823975015857917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40801635902549316677238611 61202453853823975015857917)
  ·
    refine ⟨22950920195183990630946719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61202453853823975015857917 22950920195183990630946719)
    ·
      refine ⟨34426380292775985946420079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22950920195183990630946719 34426380292775985946420079)
      ·
        refine ⟨51639570439163978919630119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34426380292775985946420079 51639570439163978919630119)
        ·
          refine ⟨77459355658745968379445179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51639570439163978919630119 77459355658745968379445179)
          ·
            refine ⟨116189033488118952569167769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77459355658745968379445179 116189033488118952569167769)
            ·
              refine ⟨87141775116089214426875827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116189033488118952569167769 87141775116089214426875827)
              ·
                refine ⟨130712662674133821640313741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87141775116089214426875827 130712662674133821640313741)
                ·
                  refine ⟨49017248502800183115117653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130712662674133821640313741 49017248502800183115117653)
                  ·
                    refine ⟨574420880892189645880285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49017248502800183115117653 574420880892189645880285)
                    ·
                      rfl

theorem cell22_1678021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_1678021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678021 prefixEnd_1678021 := by exact prefixLift 1678021
  have htrace : WordTrace (prefixWord ++ tailWord_1678021) baseStart_1678021 baseEnd_1678021 := by
    simpa [prefixWord, tailWord_1678021, baseEnd_1678021] using wordTrace_append hprefix tailTrace_1678021
  have hstable : (prefixWord ++ tailWord_1678021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678021).length < 2 ^ (prefixWord ++ tailWord_1678021).sum := by decide
  have hdescent : baseEnd_1678021 < baseStart_1678021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678023 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 7, 3]
def baseStart_1678023 : Nat := 118140960795 + 1678023 * 2 ^ 59
def prefixEnd_1678023 : Nat := 4983230072969 + 3 ^ 40 * 1678023 * 2
def baseEnd_1678023 : Nat := 574421565533062307330279

theorem tailTrace_1678023 : CollatzResearch.WordTrace tailWord_1678023 prefixEnd_1678023 574421565533062307330279 := by
  unfold tailWord_1678023
  simp only [CollatzResearch.WordTrace]
  refine ⟨61202526799816729357430723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40801684533211152904953815 61202526799816729357430723)
  ·
    refine ⟨91803790199725094036146085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61202526799816729357430723 91803790199725094036146085)
    ·
      refine ⟨17213210662448455131777391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91803790199725094036146085 17213210662448455131777391)
      ·
        refine ⟨25819815993672682697666087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17213210662448455131777391 25819815993672682697666087)
        ·
          refine ⟨38729723990509024046499131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25819815993672682697666087 38729723990509024046499131)
          ·
            refine ⟨58094585985763536069748697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38729723990509024046499131 58094585985763536069748697)
            ·
              refine ⟨43570939489322652052311523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58094585985763536069748697 43570939489322652052311523)
              ·
                refine ⟨65356409233983978078467285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43570939489322652052311523 65356409233983978078467285)
                ·
                  refine ⟨1531790841421499486214077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 65356409233983978078467285 1531790841421499486214077)
                  ·
                    refine ⟨574421565533062307330279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531790841421499486214077 574421565533062307330279)
                    ·
                      rfl

theorem cell22_1678023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_1678023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678023 prefixEnd_1678023 := by exact prefixLift 1678023
  have htrace : WordTrace (prefixWord ++ tailWord_1678023) baseStart_1678023 baseEnd_1678023 := by
    simpa [prefixWord, tailWord_1678023, baseEnd_1678023] using wordTrace_append hprefix tailTrace_1678023
  have hstable : (prefixWord ++ tailWord_1678023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678023).length < 2 ^ (prefixWord ++ tailWord_1678023).sum := by decide
  have hdescent : baseEnd_1678023 < baseStart_1678023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678087 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 5]
def baseStart_1678087 : Nat := 118140960795 + 1678087 * 2 ^ 59
def prefixEnd_1678087 : Nat := 4983230072969 + 3 ^ 40 * 1678087 * 2
def baseEnd_1678087 : Nat := 191481158013662491243361

theorem tailTrace_1678087 : CollatzResearch.WordTrace tailWord_1678087 prefixEnd_1678087 191481158013662491243361 := by
  unfold tailWord_1678087
  simp only [CollatzResearch.WordTrace]
  refine ⟨61204861071584868287760515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40803240714389912191840343 61204861071584868287760515)
  ·
    refine ⟨91807291607377302431640773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61204861071584868287760515 91807291607377302431640773)
    ·
      refine ⟨17213867176383244205932645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91807291607377302431640773 17213867176383244205932645)
      ·
        refine ⟨3227600095571858288612371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17213867176383244205932645 3227600095571858288612371)
        ·
          refine ⟨4841400143357787432918557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3227600095571858288612371 4841400143357787432918557)
          ·
            refine ⟨1815525053759170287344459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4841400143357787432918557 1815525053759170287344459)
            ·
              refine ⟨2723287580638755431016689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815525053759170287344459 2723287580638755431016689)
              ·
                refine ⟨2042465685479066573262517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2723287580638755431016689 2042465685479066573262517)
                ·
                  refine ⟨191481158013662491243361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2042465685479066573262517 191481158013662491243361)
                  ·
                    rfl

theorem cell22_1678087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 5].length) (baseStart_1678087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678087 prefixEnd_1678087 := by exact prefixLift 1678087
  have htrace : WordTrace (prefixWord ++ tailWord_1678087) baseStart_1678087 baseEnd_1678087 := by
    simpa [prefixWord, tailWord_1678087, baseEnd_1678087] using wordTrace_append hprefix tailTrace_1678087
  have hstable : (prefixWord ++ tailWord_1678087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678087).length < 2 ^ (prefixWord ++ tailWord_1678087).sum := by decide
  have hdescent : baseEnd_1678087 < baseStart_1678087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678125 : List Nat := [1, 5, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1678125 : Nat := 118140960795 + 1678125 * 2 ^ 59
def prefixEnd_1678125 : Nat := 4983230072969 + 3 ^ 40 * 1678125 * 2
def baseEnd_1678125 : Nat := 574456482217568041279967

theorem tailTrace_1678125 : CollatzResearch.WordTrace tailWord_1678125 prefixEnd_1678125 574456482217568041279967 := by
  unfold tailWord_1678125
  simp only [CollatzResearch.WordTrace]
  refine ⟨61206247045447200777643829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40804164696964800518429219 61206247045447200777643829)
  ·
    refine ⟨5738085660510675072904109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61206247045447200777643829 5738085660510675072904109)
    ·
      refine ⟨2151782122691503152339041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5738085660510675072904109 2151782122691503152339041)
      ·
        refine ⟨1613836592018627364254281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2151782122691503152339041 1613836592018627364254281)
        ·
          refine ⟨1210377444013970523190711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1613836592018627364254281 1210377444013970523190711)
          ·
            refine ⟨1815566166020955784786067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210377444013970523190711 1815566166020955784786067)
            ·
              refine ⟨2723349249031433677179101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815566166020955784786067 2723349249031433677179101)
              ·
                refine ⟨1021255968386787628942163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2723349249031433677179101 1021255968386787628942163)
                ·
                  refine ⟨1531883952580181443413245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021255968386787628942163 1531883952580181443413245)
                  ·
                    refine ⟨574456482217568041279967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531883952580181443413245 574456482217568041279967)
                    ·
                      rfl

theorem cell22_1678125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1678125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678125 prefixEnd_1678125 := by exact prefixLift 1678125
  have htrace : WordTrace (prefixWord ++ tailWord_1678125) baseStart_1678125 baseEnd_1678125 := by
    simpa [prefixWord, tailWord_1678125, baseEnd_1678125] using wordTrace_append hprefix tailTrace_1678125
  have hstable : (prefixWord ++ tailWord_1678125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678125).length < 2 ^ (prefixWord ++ tailWord_1678125).sum := by decide
  have hdescent : baseEnd_1678125 < baseStart_1678125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678128 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 6, 4]
def baseStart_1678128 : Nat := 118140960795 + 1678128 * 2 ^ 59
def prefixEnd_1678128 : Nat := 4983230072969 + 3 ^ 40 * 1678128 * 2
def baseEnd_1678128 : Nat := 574457509178877033454957

theorem tailTrace_1678128 : CollatzResearch.WordTrace tailWord_1678128 prefixEnd_1678128 574457509178877033454957 := by
  unfold tailWord_1678128
  simp only [CollatzResearch.WordTrace]
  refine ⟨30603178232218166145001519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40804237642957554860002025 30603178232218166145001519)
  ·
    refine ⟨45904767348327249217502279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30603178232218166145001519 45904767348327249217502279)
    ·
      refine ⟨68857151022490873826253419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45904767348327249217502279 68857151022490873826253419)
      ·
        refine ⟨103285726533736310739380129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68857151022490873826253419 103285726533736310739380129)
        ·
          refine ⟨77464294900302233054535097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103285726533736310739380129 77464294900302233054535097)
          ·
            refine ⟨58098221175226674790901323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77464294900302233054535097 58098221175226674790901323)
            ·
              refine ⟨87147331762840012186351985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58098221175226674790901323 87147331762840012186351985)
              ·
                refine ⟨65360498822130009139763989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87147331762840012186351985 65360498822130009139763989)
                ·
                  refine ⟨3063773382287344178426437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65360498822130009139763989 3063773382287344178426437)
                  ·
                    refine ⟨574457509178877033454957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3063773382287344178426437 574457509178877033454957)
                    ·
                      rfl

theorem cell22_1678128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_1678128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678128 prefixEnd_1678128 := by exact prefixLift 1678128
  have htrace : WordTrace (prefixWord ++ tailWord_1678128) baseStart_1678128 baseEnd_1678128 := by
    simpa [prefixWord, tailWord_1678128, baseEnd_1678128] using wordTrace_append hprefix tailTrace_1678128
  have hstable : (prefixWord ++ tailWord_1678128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678128).length < 2 ^ (prefixWord ++ tailWord_1678128).sum := by decide
  have hdescent : baseEnd_1678128 < baseStart_1678128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678130 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_1678130 : Nat := 118140960795 + 1678130 * 2 ^ 59
def prefixEnd_1678130 : Nat := 4983230072969 + 3 ^ 40 * 1678130 * 2
def baseEnd_1678130 : Nat := 574458193819749694904951

theorem tailTrace_1678130 : CollatzResearch.WordTrace tailWord_1678130 prefixEnd_1678130 574458193819749694904951 := by
  unfold tailWord_1678130
  simp only [CollatzResearch.WordTrace]
  refine ⟨15301607352607271657893961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40804286273619391087717229 15301607352607271657893961)
  ·
    refine ⟨11476205514455453743420471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15301607352607271657893961 11476205514455453743420471)
    ·
      refine ⟨17214308271683180615130707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11476205514455453743420471 17214308271683180615130707)
      ·
        refine ⟨25821462407524770922696061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17214308271683180615130707 25821462407524770922696061)
        ·
          refine ⟨9683048402821789096011023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25821462407524770922696061 9683048402821789096011023)
          ·
            refine ⟨14524572604232683644016535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9683048402821789096011023 14524572604232683644016535)
            ·
              refine ⟨21786858906349025466024803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14524572604232683644016535 21786858906349025466024803)
              ·
                refine ⟨32680288359523538199037205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21786858906349025466024803 32680288359523538199037205)
                ·
                  refine ⟨1531888516852665853079869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32680288359523538199037205 1531888516852665853079869)
                  ·
                    refine ⟨574458193819749694904951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531888516852665853079869 574458193819749694904951)
                    ·
                      rfl

theorem cell22_1678130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_1678130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678130 prefixEnd_1678130 := by exact prefixLift 1678130
  have htrace : WordTrace (prefixWord ++ tailWord_1678130) baseStart_1678130 baseEnd_1678130 := by
    simpa [prefixWord, tailWord_1678130, baseEnd_1678130] using wordTrace_append hprefix tailTrace_1678130
  have hstable : (prefixWord ++ tailWord_1678130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678130).length < 2 ^ (prefixWord ++ tailWord_1678130).sum := by decide
  have hdescent : baseEnd_1678130 < baseStart_1678130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678143 : List Nat := [1, 1, 2, 2, 5, 1, 10]
def baseStart_1678143 : Nat := 118140960795 + 1678143 * 2 ^ 59
def prefixEnd_1678143 : Nat := 4983230072969 + 3 ^ 40 * 1678143 * 2
def baseEnd_1678143 : Nat := 21276394221682296086293

theorem tailTrace_1678143 : CollatzResearch.WordTrace tailWord_1678143 prefixEnd_1678143 21276394221682296086293 := by
  unfold tailWord_1678143
  simp only [CollatzResearch.WordTrace]
  refine ⟨61206903559381989851799083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40804602372921326567866055 61206903559381989851799083)
  ·
    refine ⟨91810355339072984777698625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61206903559381989851799083 91810355339072984777698625)
    ·
      refine ⟨68857766504304738583273969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91810355339072984777698625 68857766504304738583273969)
      ·
        refine ⟨51643324878228553937455477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68857766504304738583273969 51643324878228553937455477)
        ·
          refine ⟨4841561707333926931636451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51643324878228553937455477 4841561707333926931636451)
          ·
            refine ⟨7262342561000890397454677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4841561707333926931636451 7262342561000890397454677)
            ·
              refine ⟨21276394221682296086293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7262342561000890397454677 21276394221682296086293)
              ·
                rfl

theorem cell22_1678143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 10].length) (baseStart_1678143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678143 prefixEnd_1678143 := by exact prefixLift 1678143
  have htrace : WordTrace (prefixWord ++ tailWord_1678143) baseStart_1678143 baseEnd_1678143 := by
    simpa [prefixWord, tailWord_1678143, baseEnd_1678143] using wordTrace_append hprefix tailTrace_1678143
  have hstable : (prefixWord ++ tailWord_1678143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678143).length < 2 ^ (prefixWord ++ tailWord_1678143).sum := by decide
  have hdescent : baseEnd_1678143 < baseStart_1678143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678164 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1678164 : Nat := 118140960795 + 1678164 * 2 ^ 59
def prefixEnd_1678164 : Nat := 4983230072969 + 3 ^ 40 * 1678164 * 2
def baseEnd_1678164 : Nat := 574469832714584939554847

theorem tailTrace_1678164 : CollatzResearch.WordTrace tailWord_1678164 prefixEnd_1678164 574469832714584939554847 := by
  unfold tailWord_1678164
  simp only [CollatzResearch.WordTrace]
  refine ⟨30603834746152955219156773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40805112994870606958875697 30603834746152955219156773)
  ·
    refine ⟨5738219014903679103591895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30603834746152955219156773 5738219014903679103591895)
    ·
      refine ⟨8607328522355518655387843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5738219014903679103591895 8607328522355518655387843)
      ·
        refine ⟨12910992783533277983081765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8607328522355518655387843 12910992783533277983081765)
        ·
          refine ⟨2420811146912489621827831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12910992783533277983081765 2420811146912489621827831)
          ·
            refine ⟨3631216720368734432741747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420811146912489621827831 3631216720368734432741747)
            ·
              refine ⟨5446825080553101649112621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3631216720368734432741747 5446825080553101649112621)
              ·
                refine ⟨2042559405207413118417233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5446825080553101649112621 2042559405207413118417233)
                ·
                  refine ⟨1531919553905559838812925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2042559405207413118417233 1531919553905559838812925)
                  ·
                    refine ⟨574469832714584939554847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531919553905559838812925 574469832714584939554847)
                    ·
                      rfl

theorem cell22_1678164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1678164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678164 prefixEnd_1678164 := by exact prefixLift 1678164
  have htrace : WordTrace (prefixWord ++ tailWord_1678164) baseStart_1678164 baseEnd_1678164 := by
    simpa [prefixWord, tailWord_1678164, baseEnd_1678164] using wordTrace_append hprefix tailTrace_1678164
  have hstable : (prefixWord ++ tailWord_1678164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678164).length < 2 ^ (prefixWord ++ tailWord_1678164).sum := by decide
  have hdescent : baseEnd_1678164 < baseStart_1678164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678175 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 5, 3]
def baseStart_1678175 : Nat := 118140960795 + 1678175 * 2 ^ 59
def prefixEnd_1678175 : Nat := 4983230072969 + 3 ^ 40 * 1678175 * 2
def baseEnd_1678175 : Nat := 574473598239384577529813

theorem tailTrace_1678175 : CollatzResearch.WordTrace tailWord_1678175 prefixEnd_1678175 574473598239384577529813 := by
  unfold tailWord_1678175
  simp only [CollatzResearch.WordTrace]
  refine ⟨61208070695266059316963979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40805380463510706211309319 61208070695266059316963979)
  ·
    refine ⟨91812106042899088975445969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61208070695266059316963979 91812106042899088975445969)
    ·
      refine ⟨68859079532174316731584477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91812106042899088975445969 68859079532174316731584477)
      ·
        refine ⟨25822154824565368774344179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68859079532174316731584477 25822154824565368774344179)
        ·
          refine ⟨38733232236848053161516269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25822154824565368774344179 38733232236848053161516269)
          ·
            refine ⟨14524962088818019935568601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38733232236848053161516269 14524962088818019935568601)
            ·
              refine ⟨10893721566613514951676451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14524962088818019935568601 10893721566613514951676451)
              ·
                refine ⟨16340582349920272427514677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10893721566613514951676451 16340582349920272427514677)
                ·
                  refine ⟨1531929595305025540079501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16340582349920272427514677 1531929595305025540079501)
                  ·
                    refine ⟨574473598239384577529813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531929595305025540079501 574473598239384577529813)
                    ·
                      rfl

theorem cell22_1678175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 3].length) (baseStart_1678175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678175 prefixEnd_1678175 := by exact prefixLift 1678175
  have htrace : WordTrace (prefixWord ++ tailWord_1678175) baseStart_1678175 baseEnd_1678175 := by
    simpa [prefixWord, tailWord_1678175, baseEnd_1678175] using wordTrace_append hprefix tailTrace_1678175
  have hstable : (prefixWord ++ tailWord_1678175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678175).length < 2 ^ (prefixWord ++ tailWord_1678175).sum := by decide
  have hdescent : baseEnd_1678175 < baseStart_1678175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678205 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 5]
def baseStart_1678205 : Nat := 118140960795 + 1678205 * 2 ^ 59
def prefixEnd_1678205 : Nat := 4983230072969 + 3 ^ 40 * 1678205 * 2
def baseEnd_1678205 : Nat := 191494622617491499759907

theorem tailTrace_1678205 : CollatzResearch.WordTrace tailWord_1678205 prefixEnd_1678205 191494622617491499759907 := by
  unfold tailWord_1678205
  simp only [CollatzResearch.WordTrace]
  refine ⟨61209164885157374440556069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40806109923438249627037379 61209164885157374440556069)
  ·
    refine ⟨11476718415967007707604263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61209164885157374440556069 11476718415967007707604263)
    ·
      refine ⟨17215077623950511561406395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11476718415967007707604263 17215077623950511561406395)
      ·
        refine ⟨25822616435925767342109593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17215077623950511561406395 25822616435925767342109593)
        ·
          refine ⟨19366962326944325506582195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25822616435925767342109593 19366962326944325506582195)
          ·
            refine ⟨29050443490416488259873293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19366962326944325506582195 29050443490416488259873293)
            ·
              refine ⟨10893916308906183097452485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29050443490416488259873293 10893916308906183097452485)
              ·
                refine ⟨2042609307919909330772341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10893916308906183097452485 2042609307919909330772341)
                ·
                  refine ⟨191494622617491499759907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2042609307919909330772341 191494622617491499759907)
                  ·
                    rfl

theorem cell22_1678205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_1678205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678205 prefixEnd_1678205 := by exact prefixLift 1678205
  have htrace : WordTrace (prefixWord ++ tailWord_1678205) baseStart_1678205 baseEnd_1678205 := by
    simpa [prefixWord, tailWord_1678205, baseEnd_1678205] using wordTrace_append hprefix tailTrace_1678205
  have hstable : (prefixWord ++ tailWord_1678205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678205).length < 2 ^ (prefixWord ++ tailWord_1678205).sum := by decide
  have hdescent : baseEnd_1678205 < baseStart_1678205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678301 : List Nat := [1, 4, 3, 1, 2, 3, 1, 3, 4]
def baseStart_1678301 : Nat := 118140960795 + 1678301 * 2 ^ 59
def prefixEnd_1678301 : Nat := 4983230072969 + 3 ^ 40 * 1678301 * 2
def baseEnd_1678301 : Nat := 191505576871454082959809

theorem tailTrace_1678301 : CollatzResearch.WordTrace tailWord_1678301 prefixEnd_1678301 191505576871454082959809 := by
  unfold tailWord_1678301
  simp only [CollatzResearch.WordTrace]
  refine ⟨61212666292809582836050757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40808444195206388557367171 61212666292809582836050757)
  ·
    refine ⟨11477374929901796781759517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61212666292809582836050757 11477374929901796781759517)
    ·
      refine ⟨4304015598713173793159819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11477374929901796781759517 4304015598713173793159819)
      ·
        refine ⟨6456023398069760689739729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4304015598713173793159819 6456023398069760689739729)
        ·
          refine ⟨4842017548552320517304797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6456023398069760689739729 4842017548552320517304797)
          ·
            refine ⟨1815756580707120193989299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4842017548552320517304797 1815756580707120193989299)
            ·
              refine ⟨2723634871060680290983949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815756580707120193989299 2723634871060680290983949)
              ·
                refine ⟨1021363076647755109118981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2723634871060680290983949 1021363076647755109118981)
                ·
                  refine ⟨191505576871454082959809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1021363076647755109118981 191505576871454082959809)
                  ·
                    rfl

theorem cell22_1678301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_1678301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678301 prefixEnd_1678301 := by exact prefixLift 1678301
  have htrace : WordTrace (prefixWord ++ tailWord_1678301) baseStart_1678301 baseEnd_1678301 := by
    simpa [prefixWord, tailWord_1678301, baseEnd_1678301] using wordTrace_append hprefix tailTrace_1678301
  have hstable : (prefixWord ++ tailWord_1678301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678301).length < 2 ^ (prefixWord ++ tailWord_1678301).sum := by decide
  have hdescent : baseEnd_1678301 < baseStart_1678301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678355 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 4, 5]
def baseStart_1678355 : Nat := 118140960795 + 1678355 * 2 ^ 59
def prefixEnd_1678355 : Nat := 4983230072969 + 3 ^ 40 * 1678355 * 2
def baseEnd_1678355 : Nat := 574535215917924108029261

theorem tailTrace_1678355 : CollatzResearch.WordTrace tailWord_1678355 prefixEnd_1678355 574535215917924108029261 := by
  unfold tailWord_1678355
  simp only [CollatzResearch.WordTrace]
  refine ⟨61214635834613950058516519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40809757223075966705677679 61214635834613950058516519)
  ·
    refine ⟨91821953751920925087774779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61214635834613950058516519 91821953751920925087774779)
    ·
      refine ⟨137732930627881387631662169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91821953751920925087774779 137732930627881387631662169)
      ·
        refine ⟨103299697970911040723746627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137732930627881387631662169 103299697970911040723746627)
        ·
          refine ⟨154949546956366561085619941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103299697970911040723746627 154949546956366561085619941)
          ·
            refine ⟨29053040054318730203553739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154949546956366561085619941 29053040054318730203553739)
            ·
              refine ⟨43579560081478095305330609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29053040054318730203553739 43579560081478095305330609)
              ·
                refine ⟨32684670061108571478997957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43579560081478095305330609 32684670061108571478997957)
                ·
                  refine ⟨6128375636457857152312117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32684670061108571478997957 6128375636457857152312117)
                  ·
                    refine ⟨574535215917924108029261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6128375636457857152312117 574535215917924108029261)
                    ·
                      rfl

theorem cell22_1678355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_1678355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678355 prefixEnd_1678355 := by exact prefixLift 1678355
  have htrace : WordTrace (prefixWord ++ tailWord_1678355) baseStart_1678355 baseEnd_1678355 := by
    simpa [prefixWord, tailWord_1678355, baseEnd_1678355] using wordTrace_append hprefix tailTrace_1678355
  have hstable : (prefixWord ++ tailWord_1678355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678355).length < 2 ^ (prefixWord ++ tailWord_1678355).sum := by decide
  have hdescent : baseEnd_1678355 < baseStart_1678355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678378 : List Nat := [3, 1, 4, 1, 3, 1, 1, 4, 1, 3]
def baseStart_1678378 : Nat := 118140960795 + 1678378 * 2 ^ 59
def prefixEnd_1678378 : Nat := 4983230072969 + 3 ^ 40 * 1678378 * 2
def baseEnd_1678378 : Nat := 574543089287959714704191

theorem tailTrace_1678378 : CollatzResearch.WordTrace tailWord_1678378 prefixEnd_1678378 574543089287959714704191 := by
  unfold tailWord_1678378
  simp only [CollatzResearch.WordTrace]
  refine ⟨15303868678382656246650947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40810316475687083324402525 15303868678382656246650947)
  ·
    refine ⟨22955803017573984369976421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15303868678382656246650947 22955803017573984369976421)
    ·
      refine ⟨4304213065795122069370579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22955803017573984369976421 4304213065795122069370579)
      ·
        refine ⟨6456319598692683104055869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4304213065795122069370579 6456319598692683104055869)
        ·
          refine ⟨2421119849509756164020951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6456319598692683104055869 2421119849509756164020951)
          ·
            refine ⟨3631679774264634246031427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2421119849509756164020951 3631679774264634246031427)
            ·
              refine ⟨5447519661396951369047141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3631679774264634246031427 5447519661396951369047141)
              ·
                refine ⟨1021409936511928381696339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5447519661396951369047141 1021409936511928381696339)
                ·
                  refine ⟨1532114904767892572544509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021409936511928381696339 1532114904767892572544509)
                  ·
                    refine ⟨574543089287959714704191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1532114904767892572544509 574543089287959714704191)
                    ·
                      rfl

theorem cell22_1678378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_1678378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678378 prefixEnd_1678378 := by exact prefixLift 1678378
  have htrace : WordTrace (prefixWord ++ tailWord_1678378) baseStart_1678378 baseEnd_1678378 := by
    simpa [prefixWord, tailWord_1678378, baseEnd_1678378] using wordTrace_append hprefix tailTrace_1678378
  have hstable : (prefixWord ++ tailWord_1678378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678378).length < 2 ^ (prefixWord ++ tailWord_1678378).sum := by decide
  have hdescent : baseEnd_1678378 < baseStart_1678378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678417 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 1, 5]
def baseStart_1678417 : Nat := 118140960795 + 1678417 * 2 ^ 59
def prefixEnd_1678417 : Nat := 4983230072969 + 3 ^ 40 * 1678417 * 2
def baseEnd_1678417 : Nat := 574556439784976612979071

theorem tailTrace_1678417 : CollatzResearch.WordTrace tailWord_1678417 prefixEnd_1678417 574556439784976612979071 := by
  unfold tailWord_1678417
  simp only [CollatzResearch.WordTrace]
  refine ⟨61216897160389334647273505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40811264773592889764849003 61216897160389334647273505)
  ·
    refine ⟨45912672870292000985455129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61216897160389334647273505 45912672870292000985455129)
    ·
      refine ⟨34434504652719000739091347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45912672870292000985455129 34434504652719000739091347)
      ·
        refine ⟨51651756979078501108637021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34434504652719000739091347 51651756979078501108637021)
        ·
          refine ⟨19369408867154437915738883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51651756979078501108637021 19369408867154437915738883)
          ·
            refine ⟨29054113300731656873608325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19369408867154437915738883 29054113300731656873608325)
            ·
              refine ⟨5447646243887185663801561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29054113300731656873608325 5447646243887185663801561)
              ·
                refine ⟨4085734682915389247851171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5447646243887185663801561 4085734682915389247851171)
                ·
                  refine ⟨6128602024373083871776757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4085734682915389247851171 6128602024373083871776757)
                  ·
                    refine ⟨574556439784976612979071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6128602024373083871776757 574556439784976612979071)
                    ·
                      rfl

theorem cell22_1678417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_1678417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678417 prefixEnd_1678417 := by exact prefixLift 1678417
  have htrace : WordTrace (prefixWord ++ tailWord_1678417) baseStart_1678417 baseEnd_1678417 := by
    simpa [prefixWord, tailWord_1678417, baseEnd_1678417] using wordTrace_append hprefix tailTrace_1678417
  have hstable : (prefixWord ++ tailWord_1678417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678417).length < 2 ^ (prefixWord ++ tailWord_1678417).sum := by decide
  have hdescent : baseEnd_1678417 < baseStart_1678417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678432 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 4, 4]
def baseStart_1678432 : Nat := 118140960795 + 1678432 * 2 ^ 59
def prefixEnd_1678432 : Nat := 4983230072969 + 3 ^ 40 * 1678432 * 2
def baseEnd_1678432 : Nat := 574561574591521573854025

theorem tailTrace_1678432 : CollatzResearch.WordTrace tailWord_1678432 prefixEnd_1678432 574561574591521573854025 := by
  unfold tailWord_1678432
  simp only [CollatzResearch.WordTrace]
  refine ⟨30608722127667496104534775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40811629503556661472713033 30608722127667496104534775)
  ·
    refine ⟨45913083191501244156802163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30608722127667496104534775 45913083191501244156802163)
    ·
      refine ⟨68869624787251866235203245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45913083191501244156802163 68869624787251866235203245)
      ·
        refine ⟨25826109295219449838201217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68869624787251866235203245 25826109295219449838201217)
        ·
          refine ⟨19369581971414587378650913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25826109295219449838201217 19369581971414587378650913)
          ·
            refine ⟨14527186478560940533988185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19369581971414587378650913 14527186478560940533988185)
            ·
              refine ⟨10895389858920705400491139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14527186478560940533988185 10895389858920705400491139)
              ·
                refine ⟨16343084788381058100736709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10895389858920705400491139 16343084788381058100736709)
                ·
                  refine ⟨3064328397821448393888133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16343084788381058100736709 3064328397821448393888133)
                  ·
                    refine ⟨574561574591521573854025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3064328397821448393888133 574561574591521573854025)
                    ·
                      rfl

theorem cell22_1678432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_1678432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678432 prefixEnd_1678432 := by exact prefixLift 1678432
  have htrace : WordTrace (prefixWord ++ tailWord_1678432) baseStart_1678432 baseEnd_1678432 := by
    simpa [prefixWord, tailWord_1678432, baseEnd_1678432] using wordTrace_append hprefix tailTrace_1678432
  have hstable : (prefixWord ++ tailWord_1678432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678432).length < 2 ^ (prefixWord ++ tailWord_1678432).sum := by decide
  have hdescent : baseEnd_1678432 < baseStart_1678432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678588 : List Nat := [2, 2, 2, 1, 5, 1, 2, 3, 4]
def baseStart_1678588 : Nat := 118140960795 + 1678588 * 2 ^ 59
def prefixEnd_1678588 : Nat := 4983230072969 + 3 ^ 40 * 1678588 * 2
def baseEnd_1678588 : Nat := 191538325526529722317849

theorem tailTrace_1678588 : CollatzResearch.WordTrace tailWord_1678588 prefixEnd_1678588 191538325526529722317849 := by
  unfold tailWord_1678588
  simp only [CollatzResearch.WordTrace]
  refine ⟨30611567021384915425874209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40815422695179887234498945 30611567021384915425874209)
  ·
    refine ⟨22958675266038686569405657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30611567021384915425874209 22958675266038686569405657)
    ·
      refine ⟨17219006449529014927054243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22958675266038686569405657 17219006449529014927054243)
      ·
        refine ⟨25828509674293522390581365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17219006449529014927054243 25828509674293522390581365)
        ·
          refine ⟨2421422781965017724117003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25828509674293522390581365 2421422781965017724117003)
          ·
            refine ⟨3632134172947526586175505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2421422781965017724117003 3632134172947526586175505)
            ·
              refine ⟨2724100629710644939631629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3632134172947526586175505 2724100629710644939631629)
              ·
                refine ⟨1021537736141491852361861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2724100629710644939631629 1021537736141491852361861)
                ·
                  refine ⟨191538325526529722317849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1021537736141491852361861 191538325526529722317849)
                  ·
                    rfl

theorem cell22_1678588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_1678588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678588 prefixEnd_1678588 := by exact prefixLift 1678588
  have htrace : WordTrace (prefixWord ++ tailWord_1678588) baseStart_1678588 baseEnd_1678588 := by
    simpa [prefixWord, tailWord_1678588, baseEnd_1678588] using wordTrace_append hprefix tailTrace_1678588
  have hstable : (prefixWord ++ tailWord_1678588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678588).length < 2 ^ (prefixWord ++ tailWord_1678588).sum := by decide
  have hdescent : baseEnd_1678588 < baseStart_1678588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678590 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1678590 : Nat := 118140960795 + 1678590 * 2 ^ 59
def prefixEnd_1678590 : Nat := 4983230072969 + 3 ^ 40 * 1678590 * 2
def baseEnd_1678590 : Nat := 574615661220461828403541

theorem tailTrace_1678590 : CollatzResearch.WordTrace tailWord_1678590 prefixEnd_1678590 574615661220461828403541 := by
  unfold tailWord_1678590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7652900873595323149165153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40815471325841723462214149 7652900873595323149165153)
  ·
    refine ⟨5739675655196492361873865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7652900873595323149165153 5739675655196492361873865)
    ·
      refine ⟨4304756741397369271405399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5739675655196492361873865 4304756741397369271405399)
      ·
        refine ⟨6457135112096053907108099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4304756741397369271405399 6457135112096053907108099)
        ·
          refine ⟨9685702668144080860662149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6457135112096053907108099 9685702668144080860662149)
          ·
            refine ⟨1816069250277015161374153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9685702668144080860662149 1816069250277015161374153)
            ·
              refine ⟨1362051937707761371030615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1816069250277015161374153 1362051937707761371030615)
              ·
                refine ⟨2043077906561642056545923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1362051937707761371030615 2043077906561642056545923)
                ·
                  refine ⟨3064616859842463084818885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043077906561642056545923 3064616859842463084818885)
                  ·
                    refine ⟨574615661220461828403541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3064616859842463084818885 574615661220461828403541)
                    ·
                      rfl

theorem cell22_1678590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1678590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678590 prefixEnd_1678590 := by exact prefixLift 1678590
  have htrace : WordTrace (prefixWord ++ tailWord_1678590) baseStart_1678590 baseEnd_1678590 := by
    simpa [prefixWord, tailWord_1678590, baseEnd_1678590] using wordTrace_append hprefix tailTrace_1678590
  have hstable : (prefixWord ++ tailWord_1678590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678590).length < 2 ^ (prefixWord ++ tailWord_1678590).sum := by decide
  have hdescent : baseEnd_1678590 < baseStart_1678590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678603 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 2, 3]
def baseStart_1678603 : Nat := 118140960795 + 1678603 * 2 ^ 59
def prefixEnd_1678603 : Nat := 4983230072969 + 3 ^ 40 * 1678603 * 2
def baseEnd_1678603 : Nat := 574620111386134127828501

theorem tailTrace_1678603 : CollatzResearch.WordTrace tailWord_1678603 prefixEnd_1678603 574620111386134127828501 := by
  unfold tailWord_1678603
  simp only [CollatzResearch.WordTrace]
  refine ⟨61223681137715488413544463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40815787425143658942362975 61223681137715488413544463)
  ·
    refine ⟨91835521706573232620316695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61223681137715488413544463 91835521706573232620316695)
    ·
      refine ⟨137753282559859848930475043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91835521706573232620316695 137753282559859848930475043)
      ·
        refine ⟨206629923839789773395712565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137753282559859848930475043 206629923839789773395712565)
        ·
          refine ⟨19371555359980291255848053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206629923839789773395712565 19371555359980291255848053)
          ·
            refine ⟨1816083314998152305235755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19371555359980291255848053 1816083314998152305235755)
            ·
              refine ⟨2724124972497228457853633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816083314998152305235755 2724124972497228457853633)
              ·
                refine ⟨2043093729372921343390225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2724124972497228457853633 2043093729372921343390225)
                ·
                  refine ⟨1532320297029691007542669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2043093729372921343390225 1532320297029691007542669)
                  ·
                    refine ⟨574620111386134127828501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1532320297029691007542669 574620111386134127828501)
                    ·
                      rfl

theorem cell22_1678603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 3].length) (baseStart_1678603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678603 prefixEnd_1678603 := by exact prefixLift 1678603
  have htrace : WordTrace (prefixWord ++ tailWord_1678603) baseStart_1678603 baseEnd_1678603 := by
    simpa [prefixWord, tailWord_1678603, baseEnd_1678603] using wordTrace_append hprefix tailTrace_1678603
  have hstable : (prefixWord ++ tailWord_1678603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678603).length < 2 ^ (prefixWord ++ tailWord_1678603).sum := by decide
  have hdescent : baseEnd_1678603 < baseStart_1678603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678674 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1678674 : Nat := 118140960795 + 1678674 * 2 ^ 59
def prefixEnd_1678674 : Nat := 4983230072969 + 3 ^ 40 * 1678674 * 2
def baseEnd_1678674 : Nat := 574644416137113609303283

theorem tailTrace_1678674 : CollatzResearch.WordTrace tailWord_1678674 prefixEnd_1678674 574644416137113609303283 := by
  unfold tailWord_1678674
  simp only [CollatzResearch.WordTrace]
  refine ⟨15306567680114566884844769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40817513813638845026252717 15306567680114566884844769)
  ·
    refine ⟨11479925760085925163633577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15306567680114566884844769 11479925760085925163633577)
    ·
      refine ⟨8609944320064443872725183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11479925760085925163633577 8609944320064443872725183)
      ·
        refine ⟨12914916480096665809087775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8609944320064443872725183 12914916480096665809087775)
        ·
          refine ⟨19372374720144998713631663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12914916480096665809087775 19372374720144998713631663)
          ·
            refine ⟨29058562080217498070447495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19372374720144998713631663 29058562080217498070447495)
            ·
              refine ⟨43587843120326247105671243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29058562080217498070447495 43587843120326247105671243)
              ·
                refine ⟨65381764680489370658506865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43587843120326247105671243 65381764680489370658506865)
                ·
                  refine ⟨49036323510367027993880149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65381764680489370658506865 49036323510367027993880149)
                  ·
                    refine ⟨574644416137113609303283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49036323510367027993880149 574644416137113609303283)
                    ·
                      rfl

theorem cell22_1678674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1678674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678674 prefixEnd_1678674 := by exact prefixLift 1678674
  have htrace : WordTrace (prefixWord ++ tailWord_1678674) baseStart_1678674 baseEnd_1678674 := by
    simpa [prefixWord, tailWord_1678674, baseEnd_1678674] using wordTrace_append hprefix tailTrace_1678674
  have hstable : (prefixWord ++ tailWord_1678674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678674).length < 2 ^ (prefixWord ++ tailWord_1678674).sum := by decide
  have hdescent : baseEnd_1678674 < baseStart_1678674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678689 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 6]
def baseStart_1678689 : Nat := 118140960795 + 1678689 * 2 ^ 59
def prefixEnd_1678689 : Nat := 4983230072969 + 3 ^ 40 * 1678689 * 2
def baseEnd_1678689 : Nat := 191549850314552856726079

theorem tailTrace_1678689 : CollatzResearch.WordTrace tailWord_1678689 prefixEnd_1678689 191549850314552856726079 := by
  unfold tailWord_1678689
  simp only [CollatzResearch.WordTrace]
  refine ⟨61226817815403925101175121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40817878543602616734116747 61226817815403925101175121)
  ·
    refine ⟨45920113361552943825881341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61226817815403925101175121 45920113361552943825881341)
    ·
      refine ⟨17220042510582353934705503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45920113361552943825881341 17220042510582353934705503)
      ·
        refine ⟨25830063765873530902058255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17220042510582353934705503 25830063765873530902058255)
        ·
          refine ⟨38745095648810296353087383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25830063765873530902058255 38745095648810296353087383)
          ·
            refine ⟨58117643473215444529631075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38745095648810296353087383 58117643473215444529631075)
            ·
              refine ⟨87176465209823166794446613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58117643473215444529631075 87176465209823166794446613)
              ·
                refine ⟨4086396806710460943489685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87176465209823166794446613 4086396806710460943489685)
                ·
                  refine ⟨191549850314552856726079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4086396806710460943489685 191549850314552856726079)
                  ·
                    rfl

theorem cell22_1678689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_1678689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678689 prefixEnd_1678689 := by exact prefixLift 1678689
  have htrace : WordTrace (prefixWord ++ tailWord_1678689) baseStart_1678689 baseEnd_1678689 := by
    simpa [prefixWord, tailWord_1678689, baseEnd_1678689] using wordTrace_append hprefix tailTrace_1678689
  have hstable : (prefixWord ++ tailWord_1678689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678689).length < 2 ^ (prefixWord ++ tailWord_1678689).sum := by decide
  have hdescent : baseEnd_1678689 < baseStart_1678689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678691 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 3, 4]
def baseStart_1678691 : Nat := 118140960795 + 1678691 * 2 ^ 59
def prefixEnd_1678691 : Nat := 4983230072969 + 3 ^ 40 * 1678691 * 2
def baseEnd_1678691 : Nat := 574650235584531231628231

theorem tailTrace_1678691 : CollatzResearch.WordTrace tailWord_1678691 prefixEnd_1678691 574650235584531231628231 := by
  unfold tailWord_1678691
  simp only [CollatzResearch.WordTrace]
  refine ⟨61226890761396679442747927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40817927174264452961831951 61226890761396679442747927)
  ·
    refine ⟨91840336142095019164121891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61226890761396679442747927 91840336142095019164121891)
    ·
      refine ⟨137760504213142528746182837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91840336142095019164121891 137760504213142528746182837)
      ·
        refine ⟨12915047269982112069954641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137760504213142528746182837 12915047269982112069954641)
        ·
          refine ⟨9686285452486584052465981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12915047269982112069954641 9686285452486584052465981)
          ·
            refine ⟨3632357044682469019674743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9686285452486584052465981 3632357044682469019674743)
            ·
              refine ⟨5448535567023703529512115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632357044682469019674743 5448535567023703529512115)
              ·
                refine ⟨8172803350535555294268173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448535567023703529512115 8172803350535555294268173)
                ·
                  refine ⟨3064801256450833235350565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8172803350535555294268173 3064801256450833235350565)
                  ·
                    refine ⟨574650235584531231628231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3064801256450833235350565 574650235584531231628231)
                    ·
                      rfl

theorem cell22_1678691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 4].length) (baseStart_1678691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678691 prefixEnd_1678691 := by exact prefixLift 1678691
  have htrace : WordTrace (prefixWord ++ tailWord_1678691) baseStart_1678691 baseEnd_1678691 := by
    simpa [prefixWord, tailWord_1678691, baseEnd_1678691] using wordTrace_append hprefix tailTrace_1678691
  have hstable : (prefixWord ++ tailWord_1678691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678691).length < 2 ^ (prefixWord ++ tailWord_1678691).sum := by decide
  have hdescent : baseEnd_1678691 < baseStart_1678691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678723 : List Nat := [1, 1, 1, 3, 5, 2, 1, 4, 4]
def baseStart_1678723 : Nat := 118140960795 + 1678723 * 2 ^ 59
def prefixEnd_1678723 : Nat := 4983230072969 + 3 ^ 40 * 1678723 * 2
def baseEnd_1678723 : Nat := 191553729946164604942711

theorem tailTrace_1678723 : CollatzResearch.WordTrace tailWord_1678723 prefixEnd_1678723 191553729946164604942711 := by
  unfold tailWord_1678723
  simp only [CollatzResearch.WordTrace]
  refine ⟨61228057897280748907912823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40818705264853832605275215 61228057897280748907912823)
  ·
    refine ⟨91842086845921123361869235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61228057897280748907912823 91842086845921123361869235)
    ·
      refine ⟨137763130268881685042803853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91842086845921123361869235 137763130268881685042803853)
      ·
        refine ⟨51661173850830631891051445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137763130268881685042803853 51661173850830631891051445)
        ·
          refine ⟨4843235048515371739786073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51661173850830631891051445 4843235048515371739786073)
          ·
            refine ⟨3632426286386528804839555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4843235048515371739786073 3632426286386528804839555)
            ·
              refine ⟨5448639429579793207259333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632426286386528804839555 5448639429579793207259333)
              ·
                refine ⟨1021619893046211226361125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5448639429579793207259333 1021619893046211226361125)
                ·
                  refine ⟨191553729946164604942711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1021619893046211226361125 191553729946164604942711)
                  ·
                    rfl

theorem cell22_1678723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 4].length) (baseStart_1678723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678723 prefixEnd_1678723 := by exact prefixLift 1678723
  have htrace : WordTrace (prefixWord ++ tailWord_1678723) baseStart_1678723 baseEnd_1678723 := by
    simpa [prefixWord, tailWord_1678723, baseEnd_1678723] using wordTrace_append hprefix tailTrace_1678723
  have hstable : (prefixWord ++ tailWord_1678723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678723).length < 2 ^ (prefixWord ++ tailWord_1678723).sum := by decide
  have hdescent : baseEnd_1678723 < baseStart_1678723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678817 : List Nat := [1, 2, 3, 1, 2, 5, 1, 3, 1, 3]
def baseStart_1678817 : Nat := 118140960795 + 1678817 * 2 ^ 59
def prefixEnd_1678817 : Nat := 4983230072969 + 3 ^ 40 * 1678817 * 2
def baseEnd_1678817 : Nat := 574693367959508902977845

theorem tailTrace_1678817 : CollatzResearch.WordTrace tailWord_1678817 prefixEnd_1678817 574693367959508902977845 := by
  unfold tailWord_1678817
  simp only [CollatzResearch.WordTrace]
  refine ⟨61231486358940202961834705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40820990905960135307889803 61231486358940202961834705)
  ·
    refine ⟨45923614769205152221376029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61231486358940202961834705 45923614769205152221376029)
    ·
      refine ⟨17221355538451932083016011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45923614769205152221376029 17221355538451932083016011)
      ·
        refine ⟨25832033307677898124524017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17221355538451932083016011 25832033307677898124524017)
        ·
          refine ⟨19374024980758423593393013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25832033307677898124524017 19374024980758423593393013)
          ·
            refine ⟨1816314841946102211880595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19374024980758423593393013 1816314841946102211880595)
            ·
              refine ⟨2724472262919153317820893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816314841946102211880595 2724472262919153317820893)
              ·
                refine ⟨1021677098594682494182835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2724472262919153317820893 1021677098594682494182835)
                ·
                  refine ⟨1532515647892023741274253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021677098594682494182835 1532515647892023741274253)
                  ·
                    refine ⟨574693367959508902977845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1532515647892023741274253 574693367959508902977845)
                    ·
                      rfl

theorem cell22_1678817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_1678817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678817 prefixEnd_1678817 := by exact prefixLift 1678817
  have htrace : WordTrace (prefixWord ++ tailWord_1678817) baseStart_1678817 baseEnd_1678817 := by
    simpa [prefixWord, tailWord_1678817, baseEnd_1678817] using wordTrace_append hprefix tailTrace_1678817
  have hstable : (prefixWord ++ tailWord_1678817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678817).length < 2 ^ (prefixWord ++ tailWord_1678817).sum := by decide
  have hdescent : baseEnd_1678817 < baseStart_1678817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678834 : List Nat := [3, 2, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_1678834 : Nat := 118140960795 + 1678834 * 2 ^ 59
def prefixEnd_1678834 : Nat := 4983230072969 + 3 ^ 40 * 1678834 * 2
def baseEnd_1678834 : Nat := 574699187406926525302793

theorem tailTrace_1678834 : CollatzResearch.WordTrace tailWord_1678834 prefixEnd_1678834 574699187406926525302793 := by
  unfold tailWord_1678834
  simp only [CollatzResearch.WordTrace]
  refine ⟨15308026599969653716300889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40821404266585743243469037 15308026599969653716300889)
  ·
    refine ⟨11481019949977240287225667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15308026599969653716300889 11481019949977240287225667)
    ·
      refine ⟨17221529924965860430838501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11481019949977240287225667 17221529924965860430838501)
      ·
        refine ⟨3229036860931098830782219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17221529924965860430838501 3229036860931098830782219)
        ·
          refine ⟨4843555291396648246173329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229036860931098830782219 4843555291396648246173329)
          ·
            refine ⟨3632666468547486184629997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4843555291396648246173329 3632666468547486184629997)
            ·
              refine ⟨1362249925705307319236249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3632666468547486184629997 1362249925705307319236249)
              ·
                refine ⟨1021687444278980489427187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362249925705307319236249 1021687444278980489427187)
                ·
                  refine ⟨1532531166418470734140781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021687444278980489427187 1532531166418470734140781)
                  ·
                    refine ⟨574699187406926525302793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1532531166418470734140781 574699187406926525302793)
                    ·
                      rfl

theorem cell22_1678834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_1678834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678834 prefixEnd_1678834 := by exact prefixLift 1678834
  have htrace : WordTrace (prefixWord ++ tailWord_1678834) baseStart_1678834 baseEnd_1678834 := by
    simpa [prefixWord, tailWord_1678834, baseEnd_1678834] using wordTrace_append hprefix tailTrace_1678834
  have hstable : (prefixWord ++ tailWord_1678834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678834).length < 2 ^ (prefixWord ++ tailWord_1678834).sum := by decide
  have hdescent : baseEnd_1678834 < baseStart_1678834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678903 : List Nat := [1, 1, 3, 1, 2, 6, 1, 7]
def baseStart_1678903 : Nat := 118140960795 + 1678903 * 2 ^ 59
def prefixEnd_1678903 : Nat := 4983230072969 + 3 ^ 40 * 1678903 * 2
def baseEnd_1678903 : Nat := 63858089724114816147509

theorem tailTrace_1678903 : CollatzResearch.WordTrace tailWord_1678903 prefixEnd_1678903 63858089724114816147509 := by
  unfold tailWord_1678903
  simp only [CollatzResearch.WordTrace]
  refine ⟨61234623036628639649465363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40823082024419093099643575 61234623036628639649465363)
  ·
    refine ⟨91851934554942959474198045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61234623036628639649465363 91851934554942959474198045)
    ·
      refine ⟨34444475458103609802824267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91851934554942959474198045 34444475458103609802824267)
      ·
        refine ⟨51666713187155414704236401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34444475458103609802824267 51666713187155414704236401)
        ·
          refine ⟨38750034890366561028177301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51666713187155414704236401 38750034890366561028177301)
          ·
            refine ⟨1816407885485932548195811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38750034890366561028177301 1816407885485932548195811)
            ·
              refine ⟨2724611828228898822293717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816407885485932548195811 2724611828228898822293717)
              ·
                refine ⟨63858089724114816147509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2724611828228898822293717 63858089724114816147509)
                ·
                  rfl

theorem cell22_1678903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 7].length) (baseStart_1678903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678903 prefixEnd_1678903 := by exact prefixLift 1678903
  have htrace : WordTrace (prefixWord ++ tailWord_1678903) baseStart_1678903 baseEnd_1678903 := by
    simpa [prefixWord, tailWord_1678903, baseEnd_1678903] using wordTrace_append hprefix tailTrace_1678903
  have hstable : (prefixWord ++ tailWord_1678903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678903).length < 2 ^ (prefixWord ++ tailWord_1678903).sum := by decide
  have hdescent : baseEnd_1678903 < baseStart_1678903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678941 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1678941 : Nat := 118140960795 + 1678941 * 2 ^ 59
def prefixEnd_1678941 : Nat := 4983230072969 + 3 ^ 40 * 1678941 * 2
def baseEnd_1678941 : Nat := 574735815693613912877465

theorem tailTrace_1678941 : CollatzResearch.WordTrace tailWord_1678941 prefixEnd_1678941 574735815693613912877465 := by
  unfold tailWord_1678941
  simp only [CollatzResearch.WordTrace]
  refine ⟨61236009010490972139348677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40824006006993981426232451 61236009010490972139348677)
  ·
    refine ⟨11481751689467057276127877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61236009010490972139348677 11481751689467057276127877)
    ·
      refine ⟨2152828441775073239273977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11481751689467057276127877 2152828441775073239273977)
      ·
        refine ⟨1614621331331304929455483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2152828441775073239273977 1614621331331304929455483)
        ·
          refine ⟨2421931996996957394183225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1614621331331304929455483 2421931996996957394183225)
          ·
            refine ⟨1816448997747718045637419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2421931996996957394183225 1816448997747718045637419)
            ·
              refine ⟨2724673496621577068456129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816448997747718045637419 2724673496621577068456129)
              ·
                refine ⟨2043505122466182801342097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2724673496621577068456129 2043505122466182801342097)
                ·
                  refine ⟨1532628841849637101006573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2043505122466182801342097 1532628841849637101006573)
                  ·
                    refine ⟨574735815693613912877465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1532628841849637101006573 574735815693613912877465)
                    ·
                      rfl

theorem cell22_1678941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1678941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678941 prefixEnd_1678941 := by exact prefixLift 1678941
  have htrace : WordTrace (prefixWord ++ tailWord_1678941) baseStart_1678941 baseEnd_1678941 := by
    simpa [prefixWord, tailWord_1678941, baseEnd_1678941] using wordTrace_append hprefix tailTrace_1678941
  have hstable : (prefixWord ++ tailWord_1678941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678941).length < 2 ^ (prefixWord ++ tailWord_1678941).sum := by decide
  have hdescent : baseEnd_1678941 < baseStart_1678941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678948 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 7]
def baseStart_1678948 : Nat := 118140960795 + 1678948 * 2 ^ 59
def prefixEnd_1678948 : Nat := 4983230072969 + 3 ^ 40 * 1678948 * 2
def baseEnd_1678948 : Nat := 191579403978889409317481

theorem tailTrace_1678948 : CollatzResearch.WordTrace tailWord_1678948 prefixEnd_1678948 191579403978889409317481 := by
  unfold tailWord_1678948
  simp only [CollatzResearch.WordTrace]
  refine ⟨30618132160732806167426749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40824176214310408223235665 30618132160732806167426749)
  ·
    refine ⟨11481799560274802312785031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30618132160732806167426749 11481799560274802312785031)
    ·
      refine ⟨17222699340412203469177547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11481799560274802312785031 17222699340412203469177547)
      ·
        refine ⟨25834049010618305203766321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17222699340412203469177547 25834049010618305203766321)
        ·
          refine ⟨19375536757963728902824741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25834049010618305203766321 19375536757963728902824741)
          ·
            refine ⟨3632913142118199169279639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19375536757963728902824741 3632913142118199169279639)
            ·
              refine ⟨5449369713177298753919459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632913142118199169279639 5449369713177298753919459)
              ·
                refine ⟨8174054569765948130879189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5449369713177298753919459 8174054569765948130879189)
                ·
                  refine ⟨191579403978889409317481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8174054569765948130879189 191579403978889409317481)
                  ·
                    rfl

theorem cell22_1678948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_1678948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678948 prefixEnd_1678948 := by exact prefixLift 1678948
  have htrace : WordTrace (prefixWord ++ tailWord_1678948) baseStart_1678948 baseEnd_1678948 := by
    simpa [prefixWord, tailWord_1678948, baseEnd_1678948] using wordTrace_append hprefix tailTrace_1678948
  have hstable : (prefixWord ++ tailWord_1678948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678948).length < 2 ^ (prefixWord ++ tailWord_1678948).sum := by decide
  have hdescent : baseEnd_1678948 < baseStart_1678948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678952 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 3, 3]
def baseStart_1678952 : Nat := 118140960795 + 1678952 * 2 ^ 59
def prefixEnd_1678952 : Nat := 4983230072969 + 3 ^ 40 * 1678952 * 2
def baseEnd_1678952 : Nat := 574739581218413550852431

theorem tailTrace_1678952 : CollatzResearch.WordTrace tailWord_1678952 prefixEnd_1678952 574739581218413550852431 := by
  unfold tailWord_1678952
  simp only [CollatzResearch.WordTrace]
  refine ⟨30618205106725560508999555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40824273475634080678666073 30618205106725560508999555)
  ·
    refine ⟨45927307660088340763499333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30618205106725560508999555 45927307660088340763499333)
    ·
      refine ⟨8611370186266563893156125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45927307660088340763499333 8611370186266563893156125)
      ·
        refine ⟨3229263819849961459933547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8611370186266563893156125 3229263819849961459933547)
        ·
          refine ⟨4843895729774942189900321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229263819849961459933547 4843895729774942189900321)
          ·
            refine ⟨3632921797331206642425241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4843895729774942189900321 3632921797331206642425241)
            ·
              refine ⟨2724691347998404981818931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3632921797331206642425241 2724691347998404981818931)
              ·
                refine ⟨4087037021997607472728397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724691347998404981818931 4087037021997607472728397)
                ·
                  refine ⟨1532638883249102802273149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4087037021997607472728397 1532638883249102802273149)
                  ·
                    refine ⟨574739581218413550852431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1532638883249102802273149 574739581218413550852431)
                    ·
                      rfl

theorem cell22_1678952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_1678952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1678952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1678952 prefixEnd_1678952 := by exact prefixLift 1678952
  have htrace : WordTrace (prefixWord ++ tailWord_1678952) baseStart_1678952 baseEnd_1678952 := by
    simpa [prefixWord, tailWord_1678952, baseEnd_1678952] using wordTrace_append hprefix tailTrace_1678952
  have hstable : (prefixWord ++ tailWord_1678952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678952).length < 2 ^ (prefixWord ++ tailWord_1678952).sum := by decide
  have hdescent : baseEnd_1678952 < baseStart_1678952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679023 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 4, 4]
def baseStart_1679023 : Nat := 118140960795 + 1679023 * 2 ^ 59
def prefixEnd_1679023 : Nat := 4983230072969 + 3 ^ 40 * 1679023 * 2
def baseEnd_1679023 : Nat := 574763885969393032327213

theorem tailTrace_1679023 : CollatzResearch.WordTrace tailWord_1679023 prefixEnd_1679023 574763885969393032327213 := by
  unfold tailWord_1679023
  simp only [CollatzResearch.WordTrace]
  refine ⟨61238999796193900143833723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40825999864129266762555815 61238999796193900143833723)
  ·
    refine ⟨91858499694290850215750585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61238999796193900143833723 91858499694290850215750585)
    ·
      refine ⟨68893874770718137661812939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91858499694290850215750585 68893874770718137661812939)
      ·
        refine ⟨103340812156077206492719409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68893874770718137661812939 103340812156077206492719409)
        ·
          refine ⟨77505609117057904869539557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103340812156077206492719409 77505609117057904869539557)
          ·
            refine ⟨14532301709448357163038667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77505609117057904869539557 14532301709448357163038667)
            ·
              refine ⟨21798452564172535744558001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14532301709448357163038667 21798452564172535744558001)
              ·
                refine ⟨16348839423129401808418501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21798452564172535744558001 16348839423129401808418501)
                ·
                  refine ⟨3065407391836762839078469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16348839423129401808418501 3065407391836762839078469)
                  ·
                    refine ⟨574763885969393032327213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3065407391836762839078469 574763885969393032327213)
                    ·
                      rfl

theorem cell22_1679023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_1679023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679023 prefixEnd_1679023 := by exact prefixLift 1679023
  have htrace : WordTrace (prefixWord ++ tailWord_1679023) baseStart_1679023 baseEnd_1679023 := by
    simpa [prefixWord, tailWord_1679023, baseEnd_1679023] using wordTrace_append hprefix tailTrace_1679023
  have hstable : (prefixWord ++ tailWord_1679023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679023).length < 2 ^ (prefixWord ++ tailWord_1679023).sum := by decide
  have hdescent : baseEnd_1679023 < baseStart_1679023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679029 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1679029 : Nat := 118140960795 + 1679029 * 2 ^ 59
def prefixEnd_1679029 : Nat := 4983230072969 + 3 ^ 40 * 1679029 * 2
def baseEnd_1679029 : Nat := 574765939892011016677195

theorem tailTrace_1679029 : CollatzResearch.WordTrace tailWord_1679029 prefixEnd_1679029 574765939892011016677195 := by
  unfold tailWord_1679029
  simp only [CollatzResearch.WordTrace]
  refine ⟨61239218634172163168552141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40826145756114775445701427 61239218634172163168552141)
  ·
    refine ⟨22964706987814561188207053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61239218634172163168552141 22964706987814561188207053)
    ·
      refine ⟨8611765120430460445577645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22964706987814561188207053 8611765120430460445577645)
      ·
        refine ⟨3229411920161422667091617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8611765120430460445577645 3229411920161422667091617)
        ·
          refine ⟨2422058940121067000318713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3229411920161422667091617 2422058940121067000318713)
          ·
            refine ⟨1816544205090800250239035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2422058940121067000318713 1816544205090800250239035)
            ·
              refine ⟨2724816307636200375358553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816544205090800250239035 2724816307636200375358553)
              ·
                refine ⟨2043612230727150281518915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2724816307636200375358553 2043612230727150281518915)
                ·
                  refine ⟨3065418346090725422278373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043612230727150281518915 3065418346090725422278373)
                  ·
                    refine ⟨574765939892011016677195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3065418346090725422278373 574765939892011016677195)
                    ·
                      rfl

theorem cell22_1679029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1679029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679029 prefixEnd_1679029 := by exact prefixLift 1679029
  have htrace : WordTrace (prefixWord ++ tailWord_1679029) baseStart_1679029 baseEnd_1679029 := by
    simpa [prefixWord, tailWord_1679029, baseEnd_1679029] using wordTrace_append hprefix tailTrace_1679029
  have hstable : (prefixWord ++ tailWord_1679029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679029).length < 2 ^ (prefixWord ++ tailWord_1679029).sum := by decide
  have hdescent : baseEnd_1679029 < baseStart_1679029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679040 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 2, 4]
def baseStart_1679040 : Nat := 118140960795 + 1679040 * 2 ^ 59
def prefixEnd_1679040 : Nat := 4983230072969 + 3 ^ 40 * 1679040 * 2
def baseEnd_1679040 : Nat := 574769705416810654652161

theorem tailTrace_1679040 : CollatzResearch.WordTrace tailWord_1679040 prefixEnd_1679040 574769705416810654652161 := by
  unfold tailWord_1679040
  simp only [CollatzResearch.WordTrace]
  refine ⟨30619809918566156023601287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40826413224754874698135049 30619809918566156023601287)
  ·
    refine ⟨45929714877849234035401931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30619809918566156023601287 45929714877849234035401931)
    ·
      refine ⟨68894572316773851053102897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45929714877849234035401931 68894572316773851053102897)
      ·
        refine ⟨51670929237580388289827173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68894572316773851053102897 51670929237580388289827173)
        ·
          refine ⟨9688299232046322804342595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51670929237580388289827173 9688299232046322804342595)
          ·
            refine ⟨14532448848069484206513893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9688299232046322804342595 14532448848069484206513893)
            ·
              refine ⟨2724834159013028288721355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14532448848069484206513893 2724834159013028288721355)
              ·
                refine ⟨4087251238519542433082033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724834159013028288721355 4087251238519542433082033)
                ·
                  refine ⟨3065438428889656824811525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4087251238519542433082033 3065438428889656824811525)
                  ·
                    refine ⟨574769705416810654652161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3065438428889656824811525 574769705416810654652161)
                    ·
                      rfl

theorem cell22_1679040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_1679040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679040 prefixEnd_1679040 := by exact prefixLift 1679040
  have htrace : WordTrace (prefixWord ++ tailWord_1679040) baseStart_1679040 baseEnd_1679040 := by
    simpa [prefixWord, tailWord_1679040, baseEnd_1679040] using wordTrace_append hprefix tailTrace_1679040
  have hstable : (prefixWord ++ tailWord_1679040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679040).length < 2 ^ (prefixWord ++ tailWord_1679040).sum := by decide
  have hdescent : baseEnd_1679040 < baseStart_1679040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679098 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_1679098 : Nat := 118140960795 + 1679098 * 2 ^ 59
def prefixEnd_1679098 : Nat := 4983230072969 + 3 ^ 40 * 1679098 * 2
def baseEnd_1679098 : Nat := 574789560002117836701983

theorem tailTrace_1679098 : CollatzResearch.WordTrace tailWord_1679098 prefixEnd_1679098 574789560002117836701983 := by
  unfold tailWord_1679098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15310433817730546988203487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40827823513948125301875965 15310433817730546988203487)
  ·
    refine ⟨22965650726595820482305231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15310433817730546988203487 22965650726595820482305231)
    ·
      refine ⟨34448476089893730723457847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22965650726595820482305231 34448476089893730723457847)
      ·
        refine ⟨51672714134840596085186771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34448476089893730723457847 51672714134840596085186771)
        ·
          refine ⟨77509071202260894127780157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51672714134840596085186771 77509071202260894127780157)
          ·
            refine ⟨29065901700847835297917559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77509071202260894127780157 29065901700847835297917559)
            ·
              refine ⟨43598852551271752946876339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29065901700847835297917559 43598852551271752946876339)
              ·
                refine ⟨65398278826907629420314509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43598852551271752946876339 65398278826907629420314509)
                ·
                  refine ⟨24524354560090361032617941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65398278826907629420314509 24524354560090361032617941)
                  ·
                    refine ⟨574789560002117836701983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24524354560090361032617941 574789560002117836701983)
                    ·
                      rfl

theorem cell22_1679098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_1679098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679098 prefixEnd_1679098 := by exact prefixLift 1679098
  have htrace : WordTrace (prefixWord ++ tailWord_1679098) baseStart_1679098 baseEnd_1679098 := by
    simpa [prefixWord, tailWord_1679098, baseEnd_1679098] using wordTrace_append hprefix tailTrace_1679098
  have hstable : (prefixWord ++ tailWord_1679098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679098).length < 2 ^ (prefixWord ++ tailWord_1679098).sum := by decide
  have hdescent : baseEnd_1679098 < baseStart_1679098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679110 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1679110 : Nat := 118140960795 + 1679110 * 2 ^ 59
def prefixEnd_1679110 : Nat := 4983230072969 + 3 ^ 40 * 1679110 * 2
def baseEnd_1679110 : Nat := 574793667847353805401947

theorem tailTrace_1679110 : CollatzResearch.WordTrace tailWord_1679110 prefixEnd_1679110 574793667847353805401947 := by
  unfold tailWord_1679110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1913817904589959812570337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40828115297919142668167189 1913817904589959812570337)
  ·
    refine ⟨1435363428442469859427753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1913817904589959812570337 1435363428442469859427753)
    ·
      refine ⟨1076522571331852394570815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1435363428442469859427753 1076522571331852394570815)
      ·
        refine ⟨1614783856997778591856223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076522571331852394570815 1614783856997778591856223)
        ·
          refine ⟨2422175785496667887784335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1614783856997778591856223 2422175785496667887784335)
          ·
            refine ⟨3633263678245001831676503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422175785496667887784335 3633263678245001831676503)
            ·
              refine ⟨5449895517367502747514755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633263678245001831676503 5449895517367502747514755)
              ·
                refine ⟨8174843276051254121272133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5449895517367502747514755 8174843276051254121272133)
                ·
                  refine ⟨1532783114259610147738525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8174843276051254121272133 1532783114259610147738525)
                  ·
                    refine ⟨574793667847353805401947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1532783114259610147738525 574793667847353805401947)
                    ·
                      rfl

theorem cell22_1679110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1679110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679110 prefixEnd_1679110 := by exact prefixLift 1679110
  have htrace : WordTrace (prefixWord ++ tailWord_1679110) baseStart_1679110 baseEnd_1679110 := by
    simpa [prefixWord, tailWord_1679110, baseEnd_1679110] using wordTrace_append hprefix tailTrace_1679110
  have hstable : (prefixWord ++ tailWord_1679110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679110).length < 2 ^ (prefixWord ++ tailWord_1679110).sum := by decide
  have hdescent : baseEnd_1679110 < baseStart_1679110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679175 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 4, 4]
def baseStart_1679175 : Nat := 118140960795 + 1679175 * 2 ^ 59
def prefixEnd_1679175 : Nat := 4983230072969 + 3 ^ 40 * 1679175 * 2
def baseEnd_1679175 : Nat := 574815918675715302526747

theorem tailTrace_1679175 : CollatzResearch.WordTrace tailWord_1679175 prefixEnd_1679175 574815918675715302526747 := by
  unfold tailWord_1679175
  simp only [CollatzResearch.WordTrace]
  refine ⟨61244543691643230103366979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40829695794428820068911319 61244543691643230103366979)
  ·
    refine ⟨91866815537464845155050469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61244543691643230103366979 91866815537464845155050469)
    ·
      refine ⟨17225027913274658466571963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91866815537464845155050469 17225027913274658466571963)
      ·
        refine ⟨25837541869911987699857945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17225027913274658466571963 25837541869911987699857945)
        ·
          refine ⟨19378156402433990774893459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25837541869911987699857945 19378156402433990774893459)
          ·
            refine ⟨29067234603650986162340189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19378156402433990774893459 29067234603650986162340189)
            ·
              refine ⟨10900212976369119810877571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29067234603650986162340189 10900212976369119810877571)
              ·
                refine ⟨16350319464553679716316357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10900212976369119810877571 16350319464553679716316357)
                ·
                  refine ⟨3065684899603814946809317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16350319464553679716316357 3065684899603814946809317)
                  ·
                    refine ⟨574815918675715302526747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3065684899603814946809317 574815918675715302526747)
                    ·
                      rfl

theorem cell22_1679175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_1679175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679175 prefixEnd_1679175 := by exact prefixLift 1679175
  have htrace : WordTrace (prefixWord ++ tailWord_1679175) baseStart_1679175 baseEnd_1679175 := by
    simpa [prefixWord, tailWord_1679175, baseEnd_1679175] using wordTrace_append hprefix tailTrace_1679175
  have hstable : (prefixWord ++ tailWord_1679175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679175).length < 2 ^ (prefixWord ++ tailWord_1679175).sum := by decide
  have hdescent : baseEnd_1679175 < baseStart_1679175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679177 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 2, 3]
def baseStart_1679177 : Nat := 118140960795 + 1679177 * 2 ^ 59
def prefixEnd_1679177 : Nat := 4983230072969 + 3 ^ 40 * 1679177 * 2
def baseEnd_1679177 : Nat := 574816603316587963976741

theorem tailTrace_1679177 : CollatzResearch.WordTrace tailWord_1679177 prefixEnd_1679177 574816603316587963976741 := by
  unfold tailWord_1679177
  simp only [CollatzResearch.WordTrace]
  refine ⟨61244616637635984444939785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40829744425090656296626523 61244616637635984444939785)
  ·
    refine ⟨45933462478226988333704839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61244616637635984444939785 45933462478226988333704839)
    ·
      refine ⟨68900193717340482500557259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45933462478226988333704839 68900193717340482500557259)
      ·
        refine ⟨103350290576010723750835889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68900193717340482500557259 103350290576010723750835889)
        ·
          refine ⟨77512717932008042813126917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103350290576010723750835889 77512717932008042813126917)
          ·
            refine ⟨14533634612251508027461297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77512717932008042813126917 14533634612251508027461297)
            ·
              refine ⟨10900225959188631020595973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14533634612251508027461297 10900225959188631020595973)
              ·
                refine ⟨2043792367347868316361745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10900225959188631020595973 2043792367347868316361745)
                ·
                  refine ⟨1532844275510901237271309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2043792367347868316361745 1532844275510901237271309)
                  ·
                    refine ⟨574816603316587963976741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1532844275510901237271309 574816603316587963976741)
                    ·
                      rfl

theorem cell22_1679177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 3].length) (baseStart_1679177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679177 prefixEnd_1679177 := by exact prefixLift 1679177
  have htrace : WordTrace (prefixWord ++ tailWord_1679177) baseStart_1679177 baseEnd_1679177 := by
    simpa [prefixWord, tailWord_1679177, baseEnd_1679177] using wordTrace_append hprefix tailTrace_1679177
  have hstable : (prefixWord ++ tailWord_1679177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679177).length < 2 ^ (prefixWord ++ tailWord_1679177).sum := by decide
  have hdescent : baseEnd_1679177 < baseStart_1679177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679256 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 3, 3]
def baseStart_1679256 : Nat := 118140960795 + 1679256 * 2 ^ 59
def prefixEnd_1679256 : Nat := 4983230072969 + 3 ^ 40 * 1679256 * 2
def baseEnd_1679256 : Nat := 574843646631058091251499

theorem tailTrace_1679256 : CollatzResearch.WordTrace tailWord_1679256 prefixEnd_1679256 574843646631058091251499 := by
  unfold tailWord_1679256
  simp only [CollatzResearch.WordTrace]
  refine ⟨30623749002174890468532811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40831665336233187291377081 30623749002174890468532811)
  ·
    refine ⟨45935623503262335702799217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30623749002174890468532811 45935623503262335702799217)
    ·
      refine ⟨34451717627446751777099413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45935623503262335702799217 34451717627446751777099413)
      ·
        refine ⟨1614924263786566489551535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34451717627446751777099413 1614924263786566489551535)
        ·
          refine ⟨2422386395679849734327303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1614924263786566489551535 2422386395679849734327303)
          ·
            refine ⟨3633579593519774601490955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422386395679849734327303 3633579593519774601490955)
            ·
              refine ⟨5450369390279661902236433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633579593519774601490955 5450369390279661902236433)
              ·
                refine ⟨4087777042709746426677325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450369390279661902236433 4087777042709746426677325)
                ·
                  refine ⟨1532916391016154910003997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4087777042709746426677325 1532916391016154910003997)
                  ·
                    refine ⟨574843646631058091251499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1532916391016154910003997 574843646631058091251499)
                    ·
                      rfl

theorem cell22_1679256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_1679256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679256 prefixEnd_1679256 := by exact prefixLift 1679256
  have htrace : WordTrace (prefixWord ++ tailWord_1679256) baseStart_1679256 baseEnd_1679256 := by
    simpa [prefixWord, tailWord_1679256, baseEnd_1679256] using wordTrace_append hprefix tailTrace_1679256
  have hstable : (prefixWord ++ tailWord_1679256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679256).length < 2 ^ (prefixWord ++ tailWord_1679256).sum := by decide
  have hdescent : baseEnd_1679256 < baseStart_1679256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679312 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 1, 5]
def baseStart_1679312 : Nat := 118140960795 + 1679312 * 2 ^ 59
def prefixEnd_1679312 : Nat := 4983230072969 + 3 ^ 40 * 1679312 * 2
def baseEnd_1679312 : Nat := 574862816575492611851327

theorem tailTrace_1679312 : CollatzResearch.WordTrace tailWord_1679312 prefixEnd_1679312 574862816575492611851327 := by
  unfold tailWord_1679312
  simp only [CollatzResearch.WordTrace]
  refine ⟨30624770246073451250552095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40833026994764601667402793 30624770246073451250552095)
  ·
    refine ⟨45937155369110176875828143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30624770246073451250552095 45937155369110176875828143)
    ·
      refine ⟨68905733053665265313742215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45937155369110176875828143 68905733053665265313742215)
      ·
        refine ⟨103358599580497897970613323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68905733053665265313742215 103358599580497897970613323)
        ·
          refine ⟨155037899370746846955919985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103358599580497897970613323 155037899370746846955919985)
          ·
            refine ⟨116278424528060135216939989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155037899370746846955919985 116278424528060135216939989)
            ·
              refine ⟨2725275574876409419147031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 116278424528060135216939989 2725275574876409419147031)
              ·
                refine ⟨4087913362314614128720547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725275574876409419147031 4087913362314614128720547)
                ·
                  refine ⟨6131870043471921193080821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4087913362314614128720547 6131870043471921193080821)
                  ·
                    refine ⟨574862816575492611851327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6131870043471921193080821 574862816575492611851327)
                    ·
                      rfl

theorem cell22_1679312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_1679312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679312 prefixEnd_1679312 := by exact prefixLift 1679312
  have htrace : WordTrace (prefixWord ++ tailWord_1679312) baseStart_1679312 baseEnd_1679312 := by
    simpa [prefixWord, tailWord_1679312, baseEnd_1679312] using wordTrace_append hprefix tailTrace_1679312
  have hstable : (prefixWord ++ tailWord_1679312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679312).length < 2 ^ (prefixWord ++ tailWord_1679312).sum := by decide
  have hdescent : baseEnd_1679312 < baseStart_1679312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679324 : List Nat := [2, 2, 6, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1679324 : Nat := 118140960795 + 1679324 * 2 ^ 59
def prefixEnd_1679324 : Nat := 4983230072969 + 3 ^ 40 * 1679324 * 2
def baseEnd_1679324 : Nat := 574866924420728580551291

theorem tailTrace_1679324 : CollatzResearch.WordTrace tailWord_1679324 prefixEnd_1679324 574866924420728580551291 := by
  unfold tailWord_1679324
  simp only [CollatzResearch.WordTrace]
  refine ⟨30624989084051714275270513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40833318778735619033694017 30624989084051714275270513)
  ·
    refine ⟨22968741813038785706452885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30624989084051714275270513 22968741813038785706452885)
    ·
      refine ⟨1076659772486193079989979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22968741813038785706452885 1076659772486193079989979)
      ·
        refine ⟨1614989658729289619984969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076659772486193079989979 1614989658729289619984969)
        ·
          refine ⟨1211242244046967214988727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1614989658729289619984969 1211242244046967214988727)
          ·
            refine ⟨1816863366070450822483091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211242244046967214988727 1816863366070450822483091)
            ·
              refine ⟨2725295049105676233724637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816863366070450822483091 2725295049105676233724637)
              ·
                refine ⟨1021985643414628587646739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2725295049105676233724637 1021985643414628587646739)
                ·
                  refine ⟨1532978465121942881470109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021985643414628587646739 1532978465121942881470109)
                  ·
                    refine ⟨574866924420728580551291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1532978465121942881470109 574866924420728580551291)
                    ·
                      rfl

theorem cell22_1679324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1679324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679324 prefixEnd_1679324 := by exact prefixLift 1679324
  have htrace : WordTrace (prefixWord ++ tailWord_1679324) baseStart_1679324 baseEnd_1679324 := by
    simpa [prefixWord, tailWord_1679324, baseEnd_1679324] using wordTrace_append hprefix tailTrace_1679324
  have hstable : (prefixWord ++ tailWord_1679324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679324).length < 2 ^ (prefixWord ++ tailWord_1679324).sum := by decide
  have hdescent : baseEnd_1679324 < baseStart_1679324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679327 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 1, 6]
def baseStart_1679327 : Nat := 118140960795 + 1679327 * 2 ^ 59
def prefixEnd_1679327 : Nat := 4983230072969 + 3 ^ 40 * 1679327 * 2
def baseEnd_1679327 : Nat := 574867951382037572726281

theorem tailTrace_1679327 : CollatzResearch.WordTrace tailWord_1679327 prefixEnd_1679327 574867951382037572726281 := by
  unfold tailWord_1679327
  simp only [CollatzResearch.WordTrace]
  refine ⟨61250087587092560062900235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40833391724728373375266823 61250087587092560062900235)
  ·
    refine ⟨91875131380638840094350353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61250087587092560062900235 91875131380638840094350353)
    ·
      refine ⟨68906348535479130070762765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91875131380638840094350353 68906348535479130070762765)
      ·
        refine ⟨25839880700804673776536037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68906348535479130070762765 25839880700804673776536037)
        ·
          refine ⟨4844977631400876333100507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25839880700804673776536037 4844977631400876333100507)
          ·
            refine ⟨7267466447101314499650761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844977631400876333100507 7267466447101314499650761)
            ·
              refine ⟨5450599835325985874738071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7267466447101314499650761 5450599835325985874738071)
              ·
                refine ⟨8175899752988978812107107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5450599835325985874738071 8175899752988978812107107)
                ·
                  refine ⟨12263849629483468218160661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8175899752988978812107107 12263849629483468218160661)
                  ·
                    refine ⟨574867951382037572726281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12263849629483468218160661 574867951382037572726281)
                    ·
                      rfl

theorem cell22_1679327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_1679327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679327 prefixEnd_1679327 := by exact prefixLift 1679327
  have htrace : WordTrace (prefixWord ++ tailWord_1679327) baseStart_1679327 baseEnd_1679327 := by
    simpa [prefixWord, tailWord_1679327, baseEnd_1679327] using wordTrace_append hprefix tailTrace_1679327
  have hstable : (prefixWord ++ tailWord_1679327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679327).length < 2 ^ (prefixWord ++ tailWord_1679327).sum := by decide
  have hdescent : baseEnd_1679327 < baseStart_1679327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679331 : List Nat := [1, 1, 1, 6, 1, 4, 1, 3, 4]
def baseStart_1679331 : Nat := 118140960795 + 1679331 * 2 ^ 59
def prefixEnd_1679331 : Nat := 4983230072969 + 3 ^ 40 * 1679331 * 2
def baseEnd_1679331 : Nat := 191623106887927631875423

theorem tailTrace_1679331 : CollatzResearch.WordTrace tailWord_1679331 prefixEnd_1679331 191623106887927631875423 := by
  unfold tailWord_1679331
  simp only [CollatzResearch.WordTrace]
  refine ⟨61250233479078068746045847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40833488986052045830697231 61250233479078068746045847)
  ·
    refine ⟨91875350218617103119068771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61250233479078068746045847 91875350218617103119068771)
    ·
      refine ⟨137813025327925654678603157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91875350218617103119068771 137813025327925654678603157)
      ·
        refine ⟨6459985562246515063059523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137813025327925654678603157 6459985562246515063059523)
        ·
          refine ⟨9689978343369772594589285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6459985562246515063059523 9689978343369772594589285)
          ·
            refine ⟨1816870939381832361485491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9689978343369772594589285 1816870939381832361485491)
            ·
              refine ⟨2725306409072748542228237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816870939381832361485491 2725306409072748542228237)
              ·
                refine ⟨1021989903402280703335589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2725306409072748542228237 1021989903402280703335589)
                ·
                  refine ⟨191623106887927631875423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1021989903402280703335589 191623106887927631875423)
                  ·
                    rfl

theorem cell22_1679331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 4].length) (baseStart_1679331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679331 prefixEnd_1679331 := by exact prefixLift 1679331
  have htrace : WordTrace (prefixWord ++ tailWord_1679331) baseStart_1679331 baseEnd_1679331 := by
    simpa [prefixWord, tailWord_1679331, baseEnd_1679331] using wordTrace_append hprefix tailTrace_1679331
  have hstable : (prefixWord ++ tailWord_1679331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679331).length < 2 ^ (prefixWord ++ tailWord_1679331).sum := by decide
  have hdescent : baseEnd_1679331 < baseStart_1679331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679342 : List Nat := [4, 1, 2, 1, 3, 1, 10]
def baseStart_1679342 : Nat := 118140960795 + 1679342 * 2 ^ 59
def prefixEnd_1679342 : Nat := 4983230072969 + 3 ^ 40 * 1679342 * 2
def baseEnd_1679342 : Nat := 21291595784762316059305

theorem tailTrace_1679342 : CollatzResearch.WordTrace tailWord_1679342 prefixEnd_1679342 21291595784762316059305 := by
  unfold tailWord_1679342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7656329335254777203087035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40833756454692145083130853 7656329335254777203087035)
  ·
    refine ⟨11484494002882165804630553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7656329335254777203087035 11484494002882165804630553)
    ·
      refine ⟨8613370502161624353472915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11484494002882165804630553 8613370502161624353472915)
      ·
        refine ⟨12920055753242436530209373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8613370502161624353472915 12920055753242436530209373)
        ·
          refine ⟨4845020907465913698828515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12920055753242436530209373 4845020907465913698828515)
          ·
            refine ⟨7267531361198870548242773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4845020907465913698828515 7267531361198870548242773)
            ·
              refine ⟨21291595784762316059305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7267531361198870548242773 21291595784762316059305)
              ·
                rfl

theorem cell22_1679342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 10].length) (baseStart_1679342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679342 prefixEnd_1679342 := by exact prefixLift 1679342
  have htrace : WordTrace (prefixWord ++ tailWord_1679342) baseStart_1679342 baseEnd_1679342 := by
    simpa [prefixWord, tailWord_1679342, baseEnd_1679342] using wordTrace_append hprefix tailTrace_1679342
  have hstable : (prefixWord ++ tailWord_1679342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679342).length < 2 ^ (prefixWord ++ tailWord_1679342).sum := by decide
  have hdescent : baseEnd_1679342 < baseStart_1679342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679374 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_1679374 : Nat := 118140960795 + 1679374 * 2 ^ 59
def prefixEnd_1679374 : Nat := 4983230072969 + 3 ^ 40 * 1679374 * 2
def baseEnd_1679374 : Nat := 574884040442545116801137

theorem tailTrace_1679374 : CollatzResearch.WordTrace tailWord_1679374 prefixEnd_1679374 574884040442545116801137 := by
  unfold tailWord_1679374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7656475227240285886232647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40834534545281524726574117 7656475227240285886232647)
  ·
    refine ⟨11484712840860428829348971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7656475227240285886232647 11484712840860428829348971)
    ·
      refine ⟨17227069261290643244023457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11484712840860428829348971 17227069261290643244023457)
      ·
        refine ⟨12920301945967982433017593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17227069261290643244023457 12920301945967982433017593)
        ·
          refine ⟨9690226459475986824763195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12920301945967982433017593 9690226459475986824763195)
          ·
            refine ⟨14535339689213980237144793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9690226459475986824763195 14535339689213980237144793)
            ·
              refine ⟨10901504766910485177858595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14535339689213980237144793 10901504766910485177858595)
              ·
                refine ⟨16352257150365727766787893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10901504766910485177858595 16352257150365727766787893)
                ·
                  refine ⟨1533024107846786978136365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16352257150365727766787893 1533024107846786978136365)
                  ·
                    refine ⟨574884040442545116801137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1533024107846786978136365 574884040442545116801137)
                    ·
                      rfl

theorem cell22_1679374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_1679374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679374 prefixEnd_1679374 := by exact prefixLift 1679374
  have htrace : WordTrace (prefixWord ++ tailWord_1679374) baseStart_1679374 baseEnd_1679374 := by
    simpa [prefixWord, tailWord_1679374, baseEnd_1679374] using wordTrace_append hprefix tailTrace_1679374
  have hstable : (prefixWord ++ tailWord_1679374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679374).length < 2 ^ (prefixWord ++ tailWord_1679374).sum := by decide
  have hdescent : baseEnd_1679374 < baseStart_1679374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679391 : List Nat := [1, 1, 2, 4, 1, 2, 2, 5, 1, 3]
def baseStart_1679391 : Nat := 118140960795 + 1679391 * 2 ^ 59
def prefixEnd_1679391 : Nat := 4983230072969 + 3 ^ 40 * 1679391 * 2
def baseEnd_1679391 : Nat := 574889859889962739126085

theorem tailTrace_1679391 : CollatzResearch.WordTrace tailWord_1679391 prefixEnd_1679391 574889859889962739126085 := by
  unfold tailWord_1679391
  simp only [CollatzResearch.WordTrace]
  refine ⟨61252421858860698993230027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40834947905907132662153351 61252421858860698993230027)
  ·
    refine ⟨91878632788291048489845041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61252421858860698993230027 91878632788291048489845041)
    ·
      refine ⟨68908974591218286367383781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91878632788291048489845041 68908974591218286367383781)
      ·
        refine ⟨12920432735853428693884459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68908974591218286367383781 12920432735853428693884459)
        ·
          refine ⟨19380649103780143040826689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12920432735853428693884459 19380649103780143040826689)
          ·
            refine ⟨14535486827835107280620017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19380649103780143040826689 14535486827835107280620017)
            ·
              refine ⟨10901615120876330460465013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14535486827835107280620017 10901615120876330460465013)
              ·
                refine ⟨1022026417582155980668595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10901615120876330460465013 1022026417582155980668595)
                ·
                  refine ⟨1533039626373233971002893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022026417582155980668595 1533039626373233971002893)
                  ·
                    refine ⟨574889859889962739126085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1533039626373233971002893 574889859889962739126085)
                    ·
                      rfl

theorem cell22_1679391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 1, 3].length) (baseStart_1679391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679391 prefixEnd_1679391 := by exact prefixLift 1679391
  have htrace : WordTrace (prefixWord ++ tailWord_1679391) baseStart_1679391 baseEnd_1679391 := by
    simpa [prefixWord, tailWord_1679391, baseEnd_1679391] using wordTrace_append hprefix tailTrace_1679391
  have hstable : (prefixWord ++ tailWord_1679391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679391).length < 2 ^ (prefixWord ++ tailWord_1679391).sum := by decide
  have hdescent : baseEnd_1679391 < baseStart_1679391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679408 : List Nat := [2, 1, 1, 1, 2, 5, 4, 2, 1, 3]
def baseStart_1679408 : Nat := 118140960795 + 1679408 * 2 ^ 59
def prefixEnd_1679408 : Nat := 4983230072969 + 3 ^ 40 * 1679408 * 2
def baseEnd_1679408 : Nat := 574895679337380361451033

theorem tailTrace_1679408 : CollatzResearch.WordTrace tailWord_1679408 prefixEnd_1679408 574895679337380361451033 := by
  unfold tailWord_1679408
  simp only [CollatzResearch.WordTrace]
  refine ⟨30626520949899555448299439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40835361266532740597732585 30626520949899555448299439)
  ·
    refine ⟨45939781424849333172449159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30626520949899555448299439 45939781424849333172449159)
    ·
      refine ⟨68909672137273999758673739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45939781424849333172449159 68909672137273999758673739)
      ·
        refine ⟨103364508205910999638010609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68909672137273999758673739 103364508205910999638010609)
        ·
          refine ⟨77523381154433249728507957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103364508205910999638010609 77523381154433249728507957)
          ·
            refine ⟨7267816983228117162047621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77523381154433249728507957 7267816983228117162047621)
            ·
              refine ⟨1362715684355271967883929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7267816983228117162047621 1362715684355271967883929)
              ·
                refine ⟨1022036763266453975912947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362715684355271967883929 1022036763266453975912947)
                ·
                  refine ⟨1533055144899680963869421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022036763266453975912947 1533055144899680963869421)
                  ·
                    refine ⟨574895679337380361451033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1533055144899680963869421 574895679337380361451033)
                    ·
                      rfl

theorem cell22_1679408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 1, 3].length) (baseStart_1679408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679408 prefixEnd_1679408 := by exact prefixLift 1679408
  have htrace : WordTrace (prefixWord ++ tailWord_1679408) baseStart_1679408 baseEnd_1679408 := by
    simpa [prefixWord, tailWord_1679408, baseEnd_1679408] using wordTrace_append hprefix tailTrace_1679408
  have hstable : (prefixWord ++ tailWord_1679408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679408).length < 2 ^ (prefixWord ++ tailWord_1679408).sum := by decide
  have hdescent : baseEnd_1679408 < baseStart_1679408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679434 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_1679434 : Nat := 118140960795 + 1679434 * 2 ^ 59
def prefixEnd_1679434 : Nat := 4983230072969 + 3 ^ 40 * 1679434 * 2
def baseEnd_1679434 : Nat := 574904579668724960300953

theorem tailTrace_1679434 : CollatzResearch.WordTrace tailWord_1679434 prefixEnd_1679434 574904579668724960300953 := by
  unfold tailWord_1679434
  simp only [CollatzResearch.WordTrace]
  refine ⟨15313497549426229334261339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40835993465136611558030237 15313497549426229334261339)
  ·
    refine ⟨22970246324139344001392009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15313497549426229334261339 22970246324139344001392009)
    ·
      refine ⟨17227684743104508001044007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22970246324139344001392009 17227684743104508001044007)
      ·
        refine ⟨25841527114656762001566011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17227684743104508001044007 25841527114656762001566011)
        ·
          refine ⟨38762290671985143002349017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25841527114656762001566011 38762290671985143002349017)
          ·
            refine ⟨29071718003988857251761763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38762290671985143002349017 29071718003988857251761763)
            ·
              refine ⟨43607577005983285877642645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29071718003988857251761763 43607577005983285877642645)
              ·
                refine ⟨2044105172155466525514499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43607577005983285877642645 2044105172155466525514499)
                ·
                  refine ⟨3066157758233199788271749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044105172155466525514499 3066157758233199788271749)
                  ·
                    refine ⟨574904579668724960300953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3066157758233199788271749 574904579668724960300953)
                    ·
                      rfl

theorem cell22_1679434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_1679434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679434 prefixEnd_1679434 := by exact prefixLift 1679434
  have htrace : WordTrace (prefixWord ++ tailWord_1679434) baseStart_1679434 baseEnd_1679434 := by
    simpa [prefixWord, tailWord_1679434, baseEnd_1679434] using wordTrace_append hprefix tailTrace_1679434
  have hstable : (prefixWord ++ tailWord_1679434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679434).length < 2 ^ (prefixWord ++ tailWord_1679434).sum := by decide
  have hdescent : baseEnd_1679434 < baseStart_1679434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679466 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_1679466 : Nat := 118140960795 + 1679466 * 2 ^ 59
def prefixEnd_1679466 : Nat := 4983230072969 + 3 ^ 40 * 1679466 * 2
def baseEnd_1679466 : Nat := 191638511307562514500285

theorem tailTrace_1679466 : CollatzResearch.WordTrace tailWord_1679466 prefixEnd_1679466 191638511307562514500285 := by
  unfold tailWord_1679466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15313789333397246700552563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40836771555725991201473501 15313789333397246700552563)
  ·
    refine ⟨22970684000095870050828845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15313789333397246700552563 22970684000095870050828845)
    ·
      refine ⟨8614006500035951269060817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22970684000095870050828845 8614006500035951269060817)
      ·
        refine ⟨6460504875026963451795613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8614006500035951269060817 6460504875026963451795613)
        ·
          refine ⟨2422689328135111294423355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6460504875026963451795613 2422689328135111294423355)
          ·
            refine ⟨3634033992202666941635033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422689328135111294423355 3634033992202666941635033)
            ·
              refine ⟨2725525494152000206226275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3634033992202666941635033 2725525494152000206226275)
              ·
                refine ⟨4088288241228000309339413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725525494152000206226275 4088288241228000309339413)
                ·
                  refine ⟨191638511307562514500285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4088288241228000309339413 191638511307562514500285)
                  ·
                    rfl

theorem cell22_1679466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_1679466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679466 prefixEnd_1679466 := by exact prefixLift 1679466
  have htrace : WordTrace (prefixWord ++ tailWord_1679466) baseStart_1679466 baseEnd_1679466 := by
    simpa [prefixWord, tailWord_1679466, baseEnd_1679466] using wordTrace_append hprefix tailTrace_1679466
  have hstable : (prefixWord ++ tailWord_1679466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679466).length < 2 ^ (prefixWord ++ tailWord_1679466).sum := by decide
  have hdescent : baseEnd_1679466 < baseStart_1679466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679481 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 1, 5]
def baseStart_1679481 : Nat := 118140960795 + 1679481 * 2 ^ 59
def prefixEnd_1679481 : Nat := 4983230072969 + 3 ^ 40 * 1679481 * 2
def baseEnd_1679481 : Nat := 574920668729232504375809

theorem tailTrace_1679481 : CollatzResearch.WordTrace tailWord_1679481 prefixEnd_1679481 574920668729232504375809 := by
  unfold tailWord_1679481
  simp only [CollatzResearch.WordTrace]
  refine ⟨61255704428534644364006297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40837136285689762909337531 61255704428534644364006297)
  ·
    refine ⟨45941778321400983273004723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61255704428534644364006297 45941778321400983273004723)
    ·
      refine ⟨68912667482101474909507085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45941778321400983273004723 68912667482101474909507085)
      ·
        refine ⟨25842250305788053091065157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68912667482101474909507085 25842250305788053091065157)
        ·
          refine ⟨4845421932335259954574717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25842250305788053091065157 4845421932335259954574717)
          ·
            refine ⟨1817033224625722482965519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4845421932335259954574717 1817033224625722482965519)
            ·
              refine ⟨2725549836938583724448279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817033224625722482965519 2725549836938583724448279)
              ·
                refine ⟨4088324755407875586672419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725549836938583724448279 4088324755407875586672419)
                ·
                  refine ⟨6132487133111813380008629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088324755407875586672419 6132487133111813380008629)
                  ·
                    refine ⟨574920668729232504375809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6132487133111813380008629 574920668729232504375809)
                    ·
                      rfl

theorem cell22_1679481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 5].length) (baseStart_1679481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679481 prefixEnd_1679481 := by exact prefixLift 1679481
  have htrace : WordTrace (prefixWord ++ tailWord_1679481) baseStart_1679481 baseEnd_1679481 := by
    simpa [prefixWord, tailWord_1679481, baseEnd_1679481] using wordTrace_append hprefix tailTrace_1679481
  have hstable : (prefixWord ++ tailWord_1679481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679481).length < 2 ^ (prefixWord ++ tailWord_1679481).sum := by decide
  have hdescent : baseEnd_1679481 < baseStart_1679481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679507 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 1, 8]
def baseStart_1679507 : Nat := 118140960795 + 1679507 * 2 ^ 59
def prefixEnd_1679507 : Nat := 4983230072969 + 3 ^ 40 * 1679507 * 2
def baseEnd_1679507 : Nat := 574929569060577103225729

theorem tailTrace_1679507 : CollatzResearch.WordTrace tailWord_1679507 prefixEnd_1679507 574929569060577103225729 := by
  unfold tailWord_1679507
  simp only [CollatzResearch.WordTrace]
  refine ⟨61256652726440450804452775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40837768484293633869635183 61256652726440450804452775)
  ·
    refine ⟨91884979089660676206679163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61256652726440450804452775 91884979089660676206679163)
    ·
      refine ⟨137827468634491014310018745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91884979089660676206679163 137827468634491014310018745)
      ·
        refine ⟨103370601475868260732514059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137827468634491014310018745 103370601475868260732514059)
        ·
          refine ⟨155055902213802391098771089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103370601475868260732514059 155055902213802391098771089)
          ·
            refine ⟨116291926660351793324078317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155055902213802391098771089 116291926660351793324078317)
            ·
              refine ⟨43609472497631922496529369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116291926660351793324078317 43609472497631922496529369)
              ·
                refine ⟨32707104373223941872397027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43609472497631922496529369 32707104373223941872397027)
                ·
                  refine ⟨49060656559835912808595541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32707104373223941872397027 49060656559835912808595541)
                  ·
                    refine ⟨574929569060577103225729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49060656559835912808595541 574929569060577103225729)
                    ·
                      rfl

theorem cell22_1679507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_1679507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679507 prefixEnd_1679507 := by exact prefixLift 1679507
  have htrace : WordTrace (prefixWord ++ tailWord_1679507) baseStart_1679507 baseEnd_1679507 := by
    simpa [prefixWord, tailWord_1679507, baseEnd_1679507] using wordTrace_append hprefix tailTrace_1679507
  have hstable : (prefixWord ++ tailWord_1679507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679507).length < 2 ^ (prefixWord ++ tailWord_1679507).sum := by decide
  have hdescent : baseEnd_1679507 < baseStart_1679507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679511 : List Nat := [1, 1, 3, 3, 5, 1, 8]
def baseStart_1679511 : Nat := 118140960795 + 1679511 * 2 ^ 59
def prefixEnd_1679511 : Nat := 4983230072969 + 3 ^ 40 * 1679511 * 2
def baseEnd_1679511 : Nat := 21293738457123052819471

theorem tailTrace_1679511 : CollatzResearch.WordTrace tailWord_1679511 prefixEnd_1679511 21293738457123052819471 := by
  unfold tailWord_1679511
  simp only [CollatzResearch.WordTrace]
  refine ⟨61256798618425959487598387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40837865745617306325065591 61256798618425959487598387)
  ·
    refine ⟨91885197927638939231397581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61256798618425959487598387 91885197927638939231397581)
    ·
      refine ⟨34456949222864602211774093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91885197927638939231397581 34456949222864602211774093)
      ·
        refine ⟨12921355958574225829415285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34456949222864602211774093 12921355958574225829415285)
        ·
          refine ⟨1211377121116333671507683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12921355958574225829415285 1211377121116333671507683)
          ·
            refine ⟨1817065681674500507261525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211377121116333671507683 1817065681674500507261525)
            ·
              refine ⟨21293738457123052819471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1817065681674500507261525 21293738457123052819471)
              ·
                rfl

theorem cell22_1679511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 8].length) (baseStart_1679511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679511 prefixEnd_1679511 := by exact prefixLift 1679511
  have htrace : WordTrace (prefixWord ++ tailWord_1679511) baseStart_1679511 baseEnd_1679511 := by
    simpa [prefixWord, tailWord_1679511, baseEnd_1679511] using wordTrace_append hprefix tailTrace_1679511
  have hstable : (prefixWord ++ tailWord_1679511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679511).length < 2 ^ (prefixWord ++ tailWord_1679511).sum := by decide
  have hdescent : baseEnd_1679511 < baseStart_1679511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679573 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 5]
def baseStart_1679573 : Nat := 118140960795 + 1679573 * 2 ^ 59
def prefixEnd_1679573 : Nat := 4983230072969 + 3 ^ 40 * 1679573 * 2
def baseEnd_1679573 : Nat := 191650720736458310358509

theorem tailTrace_1679573 : CollatzResearch.WordTrace tailWord_1679573 prefixEnd_1679573 191650720736458310358509 := by
  unfold tailWord_1679573
  simp only [CollatzResearch.WordTrace]
  refine ⟨61259059944201344076355373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40839373296134229384236915 61259059944201344076355373)
  ·
    refine ⟨22972147479075504028633265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61259059944201344076355373 22972147479075504028633265)
    ·
      refine ⟨17229110609306628021474949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22972147479075504028633265 17229110609306628021474949)
      ·
        refine ⟨3230458239244992754026553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17229110609306628021474949 3230458239244992754026553)
        ·
          refine ⟨2422843679433744565519915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3230458239244992754026553 2422843679433744565519915)
          ·
            refine ⟨3634265519150616848279873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422843679433744565519915 3634265519150616848279873)
            ·
              refine ⟨2725699139362962636209905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3634265519150616848279873 2725699139362962636209905)
              ·
                refine ⟨2044274354522221977157429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2725699139362962636209905 2044274354522221977157429)
                ·
                  refine ⟨191650720736458310358509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2044274354522221977157429 191650720736458310358509)
                  ·
                    rfl

theorem cell22_1679573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_1679573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679573 prefixEnd_1679573 := by exact prefixLift 1679573
  have htrace : WordTrace (prefixWord ++ tailWord_1679573) baseStart_1679573 baseEnd_1679573 := by
    simpa [prefixWord, tailWord_1679573, baseEnd_1679573] using wordTrace_append hprefix tailTrace_1679573
  have hstable : (prefixWord ++ tailWord_1679573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679573).length < 2 ^ (prefixWord ++ tailWord_1679573).sum := by decide
  have hdescent : baseEnd_1679573 < baseStart_1679573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679584 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 6]
def baseStart_1679584 : Nat := 118140960795 + 1679584 * 2 ^ 59
def prefixEnd_1679584 : Nat := 4983230072969 + 3 ^ 40 * 1679584 * 2
def baseEnd_1679584 : Nat := 191651975911391523016831

theorem tailTrace_1679584 : CollatzResearch.WordTrace tailWord_1679584 prefixEnd_1679584 191651975911391523016831 := by
  unfold tailWord_1679584
  simp only [CollatzResearch.WordTrace]
  refine ⟨30629730573580746477502903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40839640764774328636670537 30629730573580746477502903)
  ·
    refine ⟨45944595860371119716254355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30629730573580746477502903 45944595860371119716254355)
    ·
      refine ⟨68916893790556679574381533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45944595860371119716254355 68916893790556679574381533)
      ·
        refine ⟨25843835171458754840393075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68916893790556679574381533 25843835171458754840393075)
        ·
          refine ⟨38765752757188132260589613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25843835171458754840393075 38765752757188132260589613)
          ·
            refine ⟨14537157283945549597721105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38765752757188132260589613 14537157283945549597721105)
            ·
              refine ⟨10902867962959162198290829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14537157283945549597721105 10902867962959162198290829)
              ·
                refine ⟨4088575486109685824359061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10902867962959162198290829 4088575486109685824359061)
                ·
                  refine ⟨191651975911391523016831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4088575486109685824359061 191651975911391523016831)
                  ·
                    rfl

theorem cell22_1679584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_1679584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679584 prefixEnd_1679584 := by exact prefixLift 1679584
  have htrace : WordTrace (prefixWord ++ tailWord_1679584) baseStart_1679584 baseEnd_1679584 := by
    simpa [prefixWord, tailWord_1679584, baseEnd_1679584] using wordTrace_append hprefix tailTrace_1679584
  have hstable : (prefixWord ++ tailWord_1679584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679584).length < 2 ^ (prefixWord ++ tailWord_1679584).sum := by decide
  have hdescent : baseEnd_1679584 < baseStart_1679584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679633 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 2, 3]
def baseStart_1679633 : Nat := 118140960795 + 1679633 * 2 ^ 59
def prefixEnd_1679633 : Nat := 4983230072969 + 3 ^ 40 * 1679633 * 2
def baseEnd_1679633 : Nat := 574972701435554774575343

theorem tailTrace_1679633 : CollatzResearch.WordTrace tailWord_1679633 prefixEnd_1679633 574972701435554774575343 := by
  unfold tailWord_1679633
  simp only [CollatzResearch.WordTrace]
  refine ⟨61261248323983974323539553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40840832215989316215693035 61261248323983974323539553)
  ·
    refine ⟨45945936242987980742654665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61261248323983974323539553 45945936242987980742654665)
    ·
      refine ⟨34459452182240985556990999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45945936242987980742654665 34459452182240985556990999)
      ·
        refine ⟨51689178273361478335486499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34459452182240985556990999 51689178273361478335486499)
        ·
          refine ⟨77533767410042217503229749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51689178273361478335486499 77533767410042217503229749)
          ·
            refine ⟨7268790694691457890927789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77533767410042217503229749 7268790694691457890927789)
            ·
              refine ⟨2725796510509296709097921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7268790694691457890927789 2725796510509296709097921)
              ·
                refine ⟨2044347382881972531823441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2725796510509296709097921 2044347382881972531823441)
                ·
                  refine ⟨1533260537161479398867581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2044347382881972531823441 1533260537161479398867581)
                  ·
                    refine ⟨574972701435554774575343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1533260537161479398867581 574972701435554774575343)
                    ·
                      rfl

theorem cell22_1679633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_1679633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679633 prefixEnd_1679633 := by exact prefixLift 1679633
  have htrace : WordTrace (prefixWord ++ tailWord_1679633) baseStart_1679633 baseEnd_1679633 := by
    simpa [prefixWord, tailWord_1679633, baseEnd_1679633] using wordTrace_append hprefix tailTrace_1679633
  have hstable : (prefixWord ++ tailWord_1679633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679633).length < 2 ^ (prefixWord ++ tailWord_1679633).sum := by decide
  have hdescent : baseEnd_1679633 < baseStart_1679633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679721 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 3, 4]
def baseStart_1679721 : Nat := 118140960795 + 1679721 * 2 ^ 59
def prefixEnd_1679721 : Nat := 4983230072969 + 3 ^ 40 * 1679721 * 2
def baseEnd_1679721 : Nat := 575002825633951878375073

theorem tailTrace_1679721 : CollatzResearch.WordTrace tailWord_1679721 prefixEnd_1679721 575002825633951878375073 := by
  unfold tailWord_1679721
  simp only [CollatzResearch.WordTrace]
  refine ⟨61264457947665165352743017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40842971965110110235162011 61264457947665165352743017)
  ·
    refine ⟨45948343460748874014557263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61264457947665165352743017 45948343460748874014557263)
    ·
      refine ⟨68922515191123311021835895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45948343460748874014557263 68922515191123311021835895)
      ·
        refine ⟨103383772786684966532753843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68922515191123311021835895 103383772786684966532753843)
        ·
          refine ⟨155075659180027449799130765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103383772786684966532753843 155075659180027449799130765)
          ·
            refine ⟨58153372192510293674674037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155075659180027449799130765 58153372192510293674674037)
            ·
              refine ⟨5451878643047840032000691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58153372192510293674674037 5451878643047840032000691)
              ·
                refine ⟨8177817964571760048001037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451878643047840032000691 8177817964571760048001037)
                ·
                  refine ⟨3066681736714410018000389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8177817964571760048001037 3066681736714410018000389)
                  ·
                    refine ⟨575002825633951878375073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3066681736714410018000389 575002825633951878375073)
                    ·
                      rfl

theorem cell22_1679721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_1679721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679721 prefixEnd_1679721 := by exact prefixLift 1679721
  have htrace : WordTrace (prefixWord ++ tailWord_1679721) baseStart_1679721 baseEnd_1679721 := by
    simpa [prefixWord, tailWord_1679721, baseEnd_1679721] using wordTrace_append hprefix tailTrace_1679721
  have hstable : (prefixWord ++ tailWord_1679721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679721).length < 2 ^ (prefixWord ++ tailWord_1679721).sum := by decide
  have hdescent : baseEnd_1679721 < baseStart_1679721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679751 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 3, 5]
def baseStart_1679751 : Nat := 118140960795 + 1679751 * 2 ^ 59
def prefixEnd_1679751 : Nat := 4983230072969 + 3 ^ 40 * 1679751 * 2
def baseEnd_1679751 : Nat := 575013095247041800124981

theorem tailTrace_1679751 : CollatzResearch.WordTrace tailWord_1679751 prefixEnd_1679751 575013095247041800124981 := by
  unfold tailWord_1679751
  simp only [CollatzResearch.WordTrace]
  refine ⟨61265552137556480476335107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40843701425037653650890071 61265552137556480476335107)
  ·
    refine ⟨91898328206334720714502661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61265552137556480476335107 91898328206334720714502661)
    ·
      refine ⟨17230936538687760133969249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91898328206334720714502661 17230936538687760133969249)
      ·
        refine ⟨12923202404015820100476937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17230936538687760133969249 12923202404015820100476937)
        ·
          refine ⟨9692401803011865075357703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12923202404015820100476937 9692401803011865075357703)
          ·
            refine ⟨14538602704517797613036555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9692401803011865075357703 14538602704517797613036555)
            ·
              refine ⟨21807904056776696419554833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14538602704517797613036555 21807904056776696419554833)
              ·
                refine ⟨16355928042582522314666125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21807904056776696419554833 16355928042582522314666125)
                ·
                  refine ⟨6133473015968445867999797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16355928042582522314666125 6133473015968445867999797)
                  ·
                    refine ⟨575013095247041800124981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6133473015968445867999797 575013095247041800124981)
                    ·
                      rfl

theorem cell22_1679751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_1679751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679751 prefixEnd_1679751 := by exact prefixLift 1679751
  have htrace : WordTrace (prefixWord ++ tailWord_1679751) baseStart_1679751 baseEnd_1679751 := by
    simpa [prefixWord, tailWord_1679751, baseEnd_1679751] using wordTrace_append hprefix tailTrace_1679751
  have hstable : (prefixWord ++ tailWord_1679751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679751).length < 2 ^ (prefixWord ++ tailWord_1679751).sum := by decide
  have hdescent : baseEnd_1679751 < baseStart_1679751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679768 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 1, 5]
def baseStart_1679768 : Nat := 118140960795 + 1679768 * 2 ^ 59
def prefixEnd_1679768 : Nat := 4983230072969 + 3 ^ 40 * 1679768 * 2
def baseEnd_1679768 : Nat := 575018914694459422449929

theorem tailTrace_1679768 : CollatzResearch.WordTrace tailWord_1679768 prefixEnd_1679768 575018914694459422449929 := by
  unfold tailWord_1679768
  simp only [CollatzResearch.WordTrace]
  refine ⟨30633086089247446189851979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40844114785663261586469305 30633086089247446189851979)
  ·
    refine ⟨45949629133871169284777969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30633086089247446189851979 45949629133871169284777969)
    ·
      refine ⟨34462221850403376963583477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45949629133871169284777969 34462221850403376963583477)
      ·
        refine ⟨3230833298475316590335951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34462221850403376963583477 3230833298475316590335951)
        ·
          refine ⟨4846249947712974885503927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3230833298475316590335951 4846249947712974885503927)
          ·
            refine ⟨7269374921569462328255891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4846249947712974885503927 7269374921569462328255891)
            ·
              refine ⟨10904062382354193492383837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7269374921569462328255891 10904062382354193492383837)
              ·
                refine ⟨4089023393382822559643939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10904062382354193492383837 4089023393382822559643939)
                ·
                  refine ⟨6133535090074233839465909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089023393382822559643939 6133535090074233839465909)
                  ·
                    refine ⟨575018914694459422449929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6133535090074233839465909 575018914694459422449929)
                    ·
                      rfl

theorem cell22_1679768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_1679768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679768 prefixEnd_1679768 := by exact prefixLift 1679768
  have htrace : WordTrace (prefixWord ++ tailWord_1679768) baseStart_1679768 baseEnd_1679768 := by
    simpa [prefixWord, tailWord_1679768, baseEnd_1679768] using wordTrace_append hprefix tailTrace_1679768
  have hstable : (prefixWord ++ tailWord_1679768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679768).length < 2 ^ (prefixWord ++ tailWord_1679768).sum := by decide
  have hdescent : baseEnd_1679768 < baseStart_1679768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679783 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1679783 : Nat := 118140960795 + 1679783 * 2 ^ 59
def prefixEnd_1679783 : Nat := 4983230072969 + 3 ^ 40 * 1679783 * 2
def baseEnd_1679783 : Nat := 575024049501004383324883

theorem tailTrace_1679783 : CollatzResearch.WordTrace tailWord_1679783 prefixEnd_1679783 575024049501004383324883 := by
  unfold tailWord_1679783
  simp only [CollatzResearch.WordTrace]
  refine ⟨61266719273440549941500003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40844479515627033294333335 61266719273440549941500003)
  ·
    refine ⟨91900078910160824912250005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61266719273440549941500003 91900078910160824912250005)
    ·
      refine ⟨4307816198913788667761719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91900078910160824912250005 4307816198913788667761719)
      ·
        refine ⟨6461724298370683001642579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4307816198913788667761719 6461724298370683001642579)
        ·
          refine ⟨9692586447556024502463869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6461724298370683001642579 9692586447556024502463869)
          ·
            refine ⟨3634719917833509188423951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9692586447556024502463869 3634719917833509188423951)
            ·
              refine ⟨5452079876750263782635927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634719917833509188423951 5452079876750263782635927)
              ·
                refine ⟨8178119815125395673953891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452079876750263782635927 8178119815125395673953891)
                ·
                  refine ⟨12267179722688093510930837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8178119815125395673953891 12267179722688093510930837)
                  ·
                    refine ⟨575024049501004383324883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12267179722688093510930837 575024049501004383324883)
                    ·
                      rfl

theorem cell22_1679783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1679783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679783 prefixEnd_1679783 := by exact prefixLift 1679783
  have htrace : WordTrace (prefixWord ++ tailWord_1679783) baseStart_1679783 baseEnd_1679783 := by
    simpa [prefixWord, tailWord_1679783, baseEnd_1679783] using wordTrace_append hprefix tailTrace_1679783
  have hstable : (prefixWord ++ tailWord_1679783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679783).length < 2 ^ (prefixWord ++ tailWord_1679783).sum := by decide
  have hdescent : baseEnd_1679783 < baseStart_1679783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679789 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_1679789 : Nat := 118140960795 + 1679789 * 2 ^ 59
def prefixEnd_1679789 : Nat := 4983230072969 + 3 ^ 40 * 1679789 * 2
def baseEnd_1679789 : Nat := 575026103423622367674865

theorem tailTrace_1679789 : CollatzResearch.WordTrace tailWord_1679789 prefixEnd_1679789 575026103423622367674865 := by
  unfold tailWord_1679789
  simp only [CollatzResearch.WordTrace]
  refine ⟨61266938111418812966218421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40844625407612541977478947 61266938111418812966218421)
  ·
    refine ⟨5743775447945513715582977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61266938111418812966218421 5743775447945513715582977)
    ·
      refine ⟨4307831585959135286687233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5743775447945513715582977 4307831585959135286687233)
      ·
        refine ⟨3230873689469351465015425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4307831585959135286687233 3230873689469351465015425)
        ·
          refine ⟨2423155267102013598761569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3230873689469351465015425 2423155267102013598761569)
          ·
            refine ⟨1817366450326510199071177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2423155267102013598761569 1817366450326510199071177)
            ·
              refine ⟨1363024837744882649303383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817366450326510199071177 1363024837744882649303383)
              ·
                refine ⟨2044537256617323973955075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363024837744882649303383 2044537256617323973955075)
                ·
                  refine ⟨3066805884925985960932613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044537256617323973955075 3066805884925985960932613)
                  ·
                    refine ⟨575026103423622367674865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3066805884925985960932613 575026103423622367674865)
                    ·
                      rfl

theorem cell22_1679789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_1679789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679789 prefixEnd_1679789 := by exact prefixLift 1679789
  have htrace : WordTrace (prefixWord ++ tailWord_1679789) baseStart_1679789 baseEnd_1679789 := by
    simpa [prefixWord, tailWord_1679789, baseEnd_1679789] using wordTrace_append hprefix tailTrace_1679789
  have hstable : (prefixWord ++ tailWord_1679789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679789).length < 2 ^ (prefixWord ++ tailWord_1679789).sum := by decide
  have hdescent : baseEnd_1679789 < baseStart_1679789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679905 : List Nat := [1, 2, 3, 2, 2, 1, 2, 5, 4]
def baseStart_1679905 : Nat := 118140960795 + 1679905 * 2 ^ 59
def prefixEnd_1679905 : Nat := 4983230072969 + 3 ^ 40 * 1679905 * 2
def baseEnd_1679905 : Nat := 191688604198078910591503

theorem tailTrace_1679905 : CollatzResearch.WordTrace tailWord_1679905 prefixEnd_1679905 191688604198078910591503 := by
  unfold tailWord_1679905
  simp only [CollatzResearch.WordTrace]
  refine ⟨61271168978998564777441169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40847445985999043184960779 61271168978998564777441169)
  ·
    refine ⟨45953376734248923583080877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61271168978998564777441169 45953376734248923583080877)
    ·
      refine ⟨17232516275343346343655329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45953376734248923583080877 17232516275343346343655329)
      ·
        refine ⟨12924387206507509757741497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17232516275343346343655329 12924387206507509757741497)
        ·
          refine ⟨9693290404880632318306123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12924387206507509757741497 9693290404880632318306123)
          ·
            refine ⟨14539935607320948477459185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9693290404880632318306123 14539935607320948477459185)
            ·
              refine ⟨10904951705490711358094389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14539935607320948477459185 10904951705490711358094389)
              ·
                refine ⟨1022339222389754189821349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10904951705490711358094389 1022339222389754189821349)
                ·
                  refine ⟨191688604198078910591503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022339222389754189821349 191688604198078910591503)
                  ·
                    rfl

theorem cell22_1679905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 4].length) (baseStart_1679905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679905 prefixEnd_1679905 := by exact prefixLift 1679905
  have htrace : WordTrace (prefixWord ++ tailWord_1679905) baseStart_1679905 baseEnd_1679905 := by
    simpa [prefixWord, tailWord_1679905, baseEnd_1679905] using wordTrace_append hprefix tailTrace_1679905
  have hstable : (prefixWord ++ tailWord_1679905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679905).length < 2 ^ (prefixWord ++ tailWord_1679905).sum := by decide
  have hdescent : baseEnd_1679905 < baseStart_1679905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679907 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 1, 4]
def baseStart_1679907 : Nat := 118140960795 + 1679907 * 2 ^ 59
def prefixEnd_1679907 : Nat := 4983230072969 + 3 ^ 40 * 1679907 * 2
def baseEnd_1679907 : Nat := 575066497235109393224503

theorem tailTrace_1679907 : CollatzResearch.WordTrace tailWord_1679907 prefixEnd_1679907 575066497235109393224503 := by
  unfold tailWord_1679907
  simp only [CollatzResearch.WordTrace]
  refine ⟨61271241924991319119013975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40847494616660879412675983 61271241924991319119013975)
  ·
    refine ⟨91906862887486978678520963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61271241924991319119013975 91906862887486978678520963)
    ·
      refine ⟨137860294331230468017781445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91906862887486978678520963 137860294331230468017781445)
      ·
        refine ⟨25848805187105712753334021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137860294331230468017781445 25848805187105712753334021)
        ·
          refine ⟨4846650972582321141250129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25848805187105712753334021 4846650972582321141250129)
          ·
            refine ⟨3634988229436740855937597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4846650972582321141250129 3634988229436740855937597)
            ·
              refine ⟨1363120586038777820976599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3634988229436740855937597 1363120586038777820976599)
              ·
                refine ⟨2044680879058166731464899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363120586038777820976599 2044680879058166731464899)
                ·
                  refine ⟨3067021318587250097197349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044680879058166731464899 3067021318587250097197349)
                  ·
                    refine ⟨575066497235109393224503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3067021318587250097197349 575066497235109393224503)
                    ·
                      rfl

theorem cell22_1679907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 4].length) (baseStart_1679907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679907 prefixEnd_1679907 := by exact prefixLift 1679907
  have htrace : WordTrace (prefixWord ++ tailWord_1679907) baseStart_1679907 baseEnd_1679907 := by
    simpa [prefixWord, tailWord_1679907, baseEnd_1679907] using wordTrace_append hprefix tailTrace_1679907
  have hstable : (prefixWord ++ tailWord_1679907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679907).length < 2 ^ (prefixWord ++ tailWord_1679907).sum := by decide
  have hdescent : baseEnd_1679907 < baseStart_1679907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679920 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 2, 3]
def baseStart_1679920 : Nat := 118140960795 + 1679920 * 2 ^ 59
def prefixEnd_1679920 : Nat := 4983230072969 + 3 ^ 40 * 1679920 * 2
def baseEnd_1679920 : Nat := 575070947400781692649463

theorem tailTrace_1679920 : CollatzResearch.WordTrace tailWord_1679920 prefixEnd_1679920 575070947400781692649463 := by
  unfold tailWord_1679920
  simp only [CollatzResearch.WordTrace]
  refine ⟨30635858036972111169618607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40847810715962814892824809 30635858036972111169618607)
  ·
    refine ⟨45953787055458166754427911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30635858036972111169618607 45953787055458166754427911)
    ·
      refine ⟨68930680583187250131641867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45953787055458166754427911 68930680583187250131641867)
      ·
        refine ⟨103396020874780875197462801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68930680583187250131641867 103396020874780875197462801)
        ·
          refine ⟨77547015656085656398097101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103396020874780875197462801 77547015656085656398097101)
          ·
            refine ⟨29080130871032121149286413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77547015656085656398097101 29080130871032121149286413)
            ·
              refine ⟨10905049076637045430982405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29080130871032121149286413 10905049076637045430982405)
              ·
                refine ⟨2044696701869446018309201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10905049076637045430982405 2044696701869446018309201)
                ·
                  refine ⟨1533522526402084513731901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2044696701869446018309201 1533522526402084513731901)
                  ·
                    refine ⟨575070947400781692649463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1533522526402084513731901 575070947400781692649463)
                    ·
                      rfl

theorem cell22_1679920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2, 3].length) (baseStart_1679920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679920 prefixEnd_1679920 := by exact prefixLift 1679920
  have htrace : WordTrace (prefixWord ++ tailWord_1679920) baseStart_1679920 baseEnd_1679920 := by
    simpa [prefixWord, tailWord_1679920, baseEnd_1679920] using wordTrace_append hprefix tailTrace_1679920
  have hstable : (prefixWord ++ tailWord_1679920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679920).length < 2 ^ (prefixWord ++ tailWord_1679920).sum := by decide
  have hdescent : baseEnd_1679920 < baseStart_1679920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679922 : List Nat := [3, 2, 1, 1, 2, 1, 6, 2, 4]
def baseStart_1679922 : Nat := 118140960795 + 1679922 * 2 ^ 59
def prefixEnd_1679922 : Nat := 4983230072969 + 3 ^ 40 * 1679922 * 2
def baseEnd_1679922 : Nat := 191690544013884784699819

theorem tailTrace_1679922 : CollatzResearch.WordTrace tailWord_1679922 prefixEnd_1679922 191690544013884784699819 := by
  unfold tailWord_1679922
  simp only [CollatzResearch.WordTrace]
  refine ⟨15317947254984244170202505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40847859346624651120540013 15317947254984244170202505)
  ·
    refine ⟨11488460441238183127651879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15317947254984244170202505 11488460441238183127651879)
    ·
      refine ⟨17232690661857274691477819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11488460441238183127651879 17232690661857274691477819)
      ·
        refine ⟨25849035992785912037216729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17232690661857274691477819 25849035992785912037216729)
        ·
          refine ⟨19386776994589434027912547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25849035992785912037216729 19386776994589434027912547)
          ·
            refine ⟨29080165491884151041868821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19386776994589434027912547 29080165491884151041868821)
            ·
              refine ⟨1363132757432069580087601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29080165491884151041868821 1363132757432069580087601)
              ·
                refine ⟨1022349568074052185065701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363132757432069580087601 1022349568074052185065701)
                ·
                  refine ⟨191690544013884784699819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022349568074052185065701 191690544013884784699819)
                  ·
                    rfl

theorem cell22_1679922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_1679922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679922 prefixEnd_1679922 := by exact prefixLift 1679922
  have htrace : WordTrace (prefixWord ++ tailWord_1679922) baseStart_1679922 baseEnd_1679922 := by
    simpa [prefixWord, tailWord_1679922, baseEnd_1679922] using wordTrace_append hprefix tailTrace_1679922
  have hstable : (prefixWord ++ tailWord_1679922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679922).length < 2 ^ (prefixWord ++ tailWord_1679922).sum := by decide
  have hdescent : baseEnd_1679922 < baseStart_1679922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679937 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1679937 : Nat := 118140960795 + 1679937 * 2 ^ 59
def prefixEnd_1679937 : Nat := 4983230072969 + 3 ^ 40 * 1679937 * 2
def baseEnd_1679937 : Nat := 575076766848199314974411

theorem tailTrace_1679937 : CollatzResearch.WordTrace tailWord_1679937 prefixEnd_1679937 575076766848199314974411 := by
  unfold tailWord_1679937
  simp only [CollatzResearch.WordTrace]
  refine ⟨61272336114882634242606065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40848224076588422828404043 61272336114882634242606065)
  ·
    refine ⟨45954252086161975681954549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61272336114882634242606065 45954252086161975681954549)
    ·
      refine ⟨4308211133077685220183239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45954252086161975681954549 4308211133077685220183239)
      ·
        refine ⟨6462316699616527830274859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308211133077685220183239 6462316699616527830274859)
        ·
          refine ⟨9693475049424791745412289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6462316699616527830274859 9693475049424791745412289)
          ·
            refine ⟨7270106287068593809059217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9693475049424791745412289 7270106287068593809059217)
            ·
              refine ⟨5452579715301445356794413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7270106287068593809059217 5452579715301445356794413)
              ·
                refine ⟨2044717393238042008797905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5452579715301445356794413 2044717393238042008797905)
                ·
                  refine ⟨1533538044928531506598429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2044717393238042008797905 1533538044928531506598429)
                  ·
                    refine ⟨575076766848199314974411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1533538044928531506598429 575076766848199314974411)
                    ·
                      rfl

theorem cell22_1679937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1679937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679937 prefixEnd_1679937 := by exact prefixLift 1679937
  have htrace : WordTrace (prefixWord ++ tailWord_1679937) baseStart_1679937 baseEnd_1679937 := by
    simpa [prefixWord, tailWord_1679937, baseEnd_1679937] using wordTrace_append hprefix tailTrace_1679937
  have hstable : (prefixWord ++ tailWord_1679937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679937).length < 2 ^ (prefixWord ++ tailWord_1679937).sum := by decide
  have hdescent : baseEnd_1679937 < baseStart_1679937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679982 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1679982 : Nat := 118140960795 + 1679982 * 2 ^ 59
def prefixEnd_1679982 : Nat := 4983230072969 + 3 ^ 40 * 1679982 * 2
def baseEnd_1679982 : Nat := 575092171267834197599273

theorem tailTrace_1679982 : CollatzResearch.WordTrace tailWord_1679982 prefixEnd_1679982 575092171267834197599273 := by
  unfold tailWord_1679982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659247174964950865999275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40849318266479737951996133 7659247174964950865999275)
  ·
    refine ⟨11488870762447426298998913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7659247174964950865999275 11488870762447426298998913)
    ·
      refine ⟨8616653071835569724249185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11488870762447426298998913 8616653071835569724249185)
      ·
        refine ⟨6462489803876677293186889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8616653071835569724249185 6462489803876677293186889)
        ·
          refine ⟨4846867352907507969890167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6462489803876677293186889 4846867352907507969890167)
          ·
            refine ⟨7270301029361261954835251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4846867352907507969890167 7270301029361261954835251)
            ·
              refine ⟨10905451544041892932252877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7270301029361261954835251 10905451544041892932252877)
              ·
                refine ⟨4089544329015709849594829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10905451544041892932252877 4089544329015709849594829)
                ·
                  refine ⟨1533579123380891193598061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4089544329015709849594829 1533579123380891193598061)
                  ·
                    refine ⟨575092171267834197599273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1533579123380891193598061 575092171267834197599273)
                    ·
                      rfl

theorem cell22_1679982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1679982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1679982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1679982 prefixEnd_1679982 := by exact prefixLift 1679982
  have htrace : WordTrace (prefixWord ++ tailWord_1679982) baseStart_1679982 baseEnd_1679982 := by
    simpa [prefixWord, tailWord_1679982, baseEnd_1679982] using wordTrace_append hprefix tailTrace_1679982
  have hstable : (prefixWord ++ tailWord_1679982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679982).length < 2 ^ (prefixWord ++ tailWord_1679982).sum := by decide
  have hdescent : baseEnd_1679982 < baseStart_1679982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680025 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 1, 4]
def baseStart_1680025 : Nat := 118140960795 + 1680025 * 2 ^ 59
def prefixEnd_1680025 : Nat := 4983230072969 + 3 ^ 40 * 1680025 * 2
def baseEnd_1680025 : Nat := 575106891046596418774141

theorem tailTrace_1680025 : CollatzResearch.WordTrace tailWord_1680025 prefixEnd_1680025 575106891046596418774141 := by
  unfold tailWord_1680025
  simp only [CollatzResearch.WordTrace]
  refine ⟨61275545738563825271809529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40850363825709216847873019 61275545738563825271809529)
  ·
    refine ⟨45956659303922868953857147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61275545738563825271809529 45956659303922868953857147)
    ·
      refine ⟨68934988955884303430785721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45956659303922868953857147 68934988955884303430785721)
      ·
        refine ⟨51701241716913227573089291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68934988955884303430785721 51701241716913227573089291)
        ·
          refine ⟨77551862575369841359633937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51701241716913227573089291 77551862575369841359633937)
          ·
            refine ⟨58163896931527381019725453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77551862575369841359633937 58163896931527381019725453)
            ·
              refine ⟨21811461349322767882397045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58163896931527381019725453 21811461349322767882397045)
              ·
                refine ⟨2044824501499009488974723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21811461349322767882397045 2044824501499009488974723)
                ·
                  refine ⟨3067236752248514233462085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044824501499009488974723 3067236752248514233462085)
                  ·
                    refine ⟨575106891046596418774141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3067236752248514233462085 575106891046596418774141)
                    ·
                      rfl

theorem cell22_1680025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_1680025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680025 prefixEnd_1680025 := by exact prefixLift 1680025
  have htrace : WordTrace (prefixWord ++ tailWord_1680025) baseStart_1680025 baseEnd_1680025 := by
    simpa [prefixWord, tailWord_1680025, baseEnd_1680025] using wordTrace_append hprefix tailTrace_1680025
  have hstable : (prefixWord ++ tailWord_1680025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680025).length < 2 ^ (prefixWord ++ tailWord_1680025).sum := by decide
  have hdescent : baseEnd_1680025 < baseStart_1680025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680046 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_1680046 : Nat := 118140960795 + 1680046 * 2 ^ 59
def prefixEnd_1680046 : Nat := 4983230072969 + 3 ^ 40 * 1680046 * 2
def baseEnd_1680046 : Nat := 191704693258586454666359

theorem tailTrace_1680046 : CollatzResearch.WordTrace tailWord_1680046 prefixEnd_1680046 191704693258586454666359 := by
  unfold tailWord_1680046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659538958935968232290499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40850874447658497238882661 7659538958935968232290499)
  ·
    refine ⟨11489308438403952348435749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7659538958935968232290499 11489308438403952348435749)
    ·
      refine ⟨2154245332200741065331703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11489308438403952348435749 2154245332200741065331703)
      ·
        refine ⟨3231367998301111597997555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154245332200741065331703 3231367998301111597997555)
        ·
          refine ⟨4847051997451667396996333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231367998301111597997555 4847051997451667396996333)
          ·
            refine ⟨1817644499044375273873625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4847051997451667396996333 1817644499044375273873625)
            ·
              refine ⟨1363233374283281455405219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817644499044375273873625 1363233374283281455405219)
              ·
                refine ⟨2044850061424922183107829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363233374283281455405219 2044850061424922183107829)
                ·
                  refine ⟨191704693258586454666359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2044850061424922183107829 191704693258586454666359)
                  ·
                    rfl

theorem cell22_1680046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_1680046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680046 prefixEnd_1680046 := by exact prefixLift 1680046
  have htrace : WordTrace (prefixWord ++ tailWord_1680046) baseStart_1680046 baseEnd_1680046 := by
    simpa [prefixWord, tailWord_1680046, baseEnd_1680046] using wordTrace_append hprefix tailTrace_1680046
  have hstable : (prefixWord ++ tailWord_1680046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680046).length < 2 ^ (prefixWord ++ tailWord_1680046).sum := by decide
  have hdescent : baseEnd_1680046 < baseStart_1680046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680085 : List Nat := [1, 3, 2, 5, 11]
def baseStart_1680085 : Nat := 118140960795 + 1680085 * 2 ^ 59
def prefixEnd_1680085 : Nat := 4983230072969 + 3 ^ 40 * 1680085 * 2
def baseEnd_1680085 : Nat := 2366779548447638939399

theorem tailTrace_1680085 : CollatzResearch.WordTrace tailWord_1680085 prefixEnd_1680085 2366779548447638939399 := by
  unfold tailWord_1680085
  simp only [CollatzResearch.WordTrace]
  refine ⟨61277734118346455518993709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40851822745564303679329139 61277734118346455518993709)
  ·
    refine ⟨22979150294379920819622641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61277734118346455518993709 22979150294379920819622641)
    ·
      refine ⟨17234362720784940614716981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22979150294379920819622641 17234362720784940614716981)
      ·
        refine ⟨1615721505073588182629717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17234362720784940614716981 1615721505073588182629717)
        ·
          refine ⟨2366779548447638939399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1615721505073588182629717 2366779548447638939399)
          ·
            rfl

theorem cell22_1680085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 11].length) (baseStart_1680085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680085 prefixEnd_1680085 := by exact prefixLift 1680085
  have htrace : WordTrace (prefixWord ++ tailWord_1680085) baseStart_1680085 baseEnd_1680085 := by
    simpa [prefixWord, tailWord_1680085, baseEnd_1680085] using wordTrace_append hprefix tailTrace_1680085
  have hstable : (prefixWord ++ tailWord_1680085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680085).length < 2 ^ (prefixWord ++ tailWord_1680085).sum := by decide
  have hdescent : baseEnd_1680085 < baseStart_1680085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680145 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_1680145 : Nat := 118140960795 + 1680145 * 2 ^ 59
def prefixEnd_1680145 : Nat := 4983230072969 + 3 ^ 40 * 1680145 * 2
def baseEnd_1680145 : Nat := 575147969498956105773773

theorem tailTrace_1680145 : CollatzResearch.WordTrace tailWord_1680145 prefixEnd_1680145 575147969498956105773773 := by
  unfold tailWord_1680145
  simp only [CollatzResearch.WordTrace]
  refine ⟨61279922498129085766177889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40853281665419390510785259 61279922498129085766177889)
  ·
    refine ⟨45959941873596814324633417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61279922498129085766177889 45959941873596814324633417)
    ·
      refine ⟨34469956405197610743475063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45959941873596814324633417 34469956405197610743475063)
      ·
        refine ⟨51704934607796416115212595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34469956405197610743475063 51704934607796416115212595)
        ·
          refine ⟨77557401911694624172818893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51704934607796416115212595 77557401911694624172818893)
          ·
            refine ⟨29084025716885484064807085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77557401911694624172818893 29084025716885484064807085)
            ·
              refine ⟨10906509643832056524302657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29084025716885484064807085 10906509643832056524302657)
              ·
                refine ⟨8179882232874042393226993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10906509643832056524302657 8179882232874042393226993)
                ·
                  refine ⟨6134911674655531794920245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8179882232874042393226993 6134911674655531794920245)
                  ·
                    refine ⟨575147969498956105773773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6134911674655531794920245 575147969498956105773773)
                    ·
                      rfl

theorem cell22_1680145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_1680145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680145 prefixEnd_1680145 := by exact prefixLift 1680145
  have htrace : WordTrace (prefixWord ++ tailWord_1680145) baseStart_1680145 baseEnd_1680145 := by
    simpa [prefixWord, tailWord_1680145, baseEnd_1680145] using wordTrace_append hprefix tailTrace_1680145
  have hstable : (prefixWord ++ tailWord_1680145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680145).length < 2 ^ (prefixWord ++ tailWord_1680145).sum := by decide
  have hdescent : baseEnd_1680145 < baseStart_1680145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680162 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1680162 : Nat := 118140960795 + 1680162 * 2 ^ 59
def prefixEnd_1680162 : Nat := 4983230072969 + 3 ^ 40 * 1680162 * 2
def baseEnd_1680162 : Nat := 575153788946373728098721

theorem tailTrace_1680162 : CollatzResearch.WordTrace tailWord_1680162 prefixEnd_1680162 575153788946373728098721 := by
  unfold tailWord_1680162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15320135634766874417386685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40853695026044998446364493 15320135634766874417386685)
  ·
    refine ⟨5745050863037577906520007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15320135634766874417386685 5745050863037577906520007)
    ·
      refine ⟨8617576294556366859780011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5745050863037577906520007 8617576294556366859780011)
      ·
        refine ⟨12926364441834550289670017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8617576294556366859780011 12926364441834550289670017)
        ·
          refine ⟨9694773331375912717252513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12926364441834550289670017 9694773331375912717252513)
          ·
            refine ⟨7271079998531934537939385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9694773331375912717252513 7271079998531934537939385)
            ·
              refine ⟨5453309998898950903454539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7271079998531934537939385 5453309998898950903454539)
              ·
                refine ⟨8179964998348426355181809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453309998898950903454539 8179964998348426355181809)
                ·
                  refine ⟨6134973748761319766386357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8179964998348426355181809 6134973748761319766386357)
                  ·
                    refine ⟨575153788946373728098721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6134973748761319766386357 575153788946373728098721)
                    ·
                      rfl

theorem cell22_1680162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1680162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680162 prefixEnd_1680162 := by exact prefixLift 1680162
  have htrace : WordTrace (prefixWord ++ tailWord_1680162) baseStart_1680162 baseEnd_1680162 := by
    simpa [prefixWord, tailWord_1680162, baseEnd_1680162] using wordTrace_append hprefix tailTrace_1680162
  have hstable : (prefixWord ++ tailWord_1680162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680162).length < 2 ^ (prefixWord ++ tailWord_1680162).sum := by decide
  have hdescent : baseEnd_1680162 < baseStart_1680162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680209 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 6]
def baseStart_1680209 : Nat := 118140960795 + 1680209 * 2 ^ 59
def prefixEnd_1680209 : Nat := 4983230072969 + 3 ^ 40 * 1680209 * 2
def baseEnd_1680209 : Nat := 191723292668960424057859

theorem tailTrace_1680209 : CollatzResearch.WordTrace tailWord_1680209 prefixEnd_1680209 191723292668960424057859 := by
  unfold tailWord_1680209
  simp only [CollatzResearch.WordTrace]
  refine ⟨61282256769897224696507681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40854837846598149797671787 61282256769897224696507681)
  ·
    refine ⟨45961692577422918522380761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61282256769897224696507681 45961692577422918522380761)
    ·
      refine ⟨34471269433067188891785571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45961692577422918522380761 34471269433067188891785571)
      ·
        refine ⟨51706904149600783337678357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34471269433067188891785571 51706904149600783337678357)
        ·
          refine ⟨2423761132012536718953673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51706904149600783337678357 2423761132012536718953673)
          ·
            refine ⟨1817820849009402539215255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2423761132012536718953673 1817820849009402539215255)
            ·
              refine ⟨2726731273514103808822883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817820849009402539215255 2726731273514103808822883)
              ·
                refine ⟨4090096910271155713234325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726731273514103808822883 4090096910271155713234325)
                ·
                  refine ⟨191723292668960424057859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4090096910271155713234325 191723292668960424057859)
                  ·
                    rfl

theorem cell22_1680209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 6].length) (baseStart_1680209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680209 prefixEnd_1680209 := by exact prefixLift 1680209
  have htrace : WordTrace (prefixWord ++ tailWord_1680209) baseStart_1680209 baseEnd_1680209 := by
    simpa [prefixWord, tailWord_1680209, baseEnd_1680209] using wordTrace_append hprefix tailTrace_1680209
  have hstable : (prefixWord ++ tailWord_1680209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680209).length < 2 ^ (prefixWord ++ tailWord_1680209).sum := by decide
  have hdescent : baseEnd_1680209 < baseStart_1680209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680224 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 2, 3]
def baseStart_1680224 : Nat := 118140960795 + 1680224 * 2 ^ 59
def prefixEnd_1680224 : Nat := 4983230072969 + 3 ^ 40 * 1680224 * 2
def baseEnd_1680224 : Nat := 575175012813426233048531

theorem tailTrace_1680224 : CollatzResearch.WordTrace tailWord_1680224 prefixEnd_1680224 575175012813426233048531 := by
  unfold tailWord_1680224
  simp only [CollatzResearch.WordTrace]
  refine ⟨30641401932421441129151863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40855202576561921505535817 30641401932421441129151863)
  ·
    refine ⟨45962102898632161693727795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30641401932421441129151863 45962102898632161693727795)
    ·
      refine ⟨68943154347948242540591693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45962102898632161693727795 68943154347948242540591693)
      ·
        refine ⟨25853682880480590952721885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68943154347948242540591693 25853682880480590952721885)
        ·
          refine ⟨9695131080180221607270707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25853682880480590952721885 9695131080180221607270707)
          ·
            refine ⟨14542696620270332410906061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9695131080180221607270707 14542696620270332410906061)
            ·
              refine ⟨5453511232601374654089773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14542696620270332410906061 5453511232601374654089773)
              ·
                refine ⟨2045066712225515495283665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5453511232601374654089773 2045066712225515495283665)
                ·
                  refine ⟨1533800034169136621462749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2045066712225515495283665 1533800034169136621462749)
                  ·
                    refine ⟨575175012813426233048531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1533800034169136621462749 575175012813426233048531)
                    ·
                      rfl

theorem cell22_1680224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2, 3].length) (baseStart_1680224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680224 prefixEnd_1680224 := by exact prefixLift 1680224
  have htrace : WordTrace (prefixWord ++ tailWord_1680224) baseStart_1680224 baseEnd_1680224 := by
    simpa [prefixWord, tailWord_1680224, baseEnd_1680224] using wordTrace_append hprefix tailTrace_1680224
  have hstable : (prefixWord ++ tailWord_1680224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680224).length < 2 ^ (prefixWord ++ tailWord_1680224).sum := by decide
  have hdescent : baseEnd_1680224 < baseStart_1680224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680235 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 2, 7]
def baseStart_1680235 : Nat := 118140960795 + 1680235 * 2 ^ 59
def prefixEnd_1680235 : Nat := 4983230072969 + 3 ^ 40 * 1680235 * 2
def baseEnd_1680235 : Nat := 575178778338225871023497

theorem tailTrace_1680235 : CollatzResearch.WordTrace tailWord_1680235 prefixEnd_1680235 575178778338225871023497 := by
  unfold tailWord_1680235
  simp only [CollatzResearch.WordTrace]
  refine ⟨61283205067803031136954159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40855470045202020757969439 61283205067803031136954159)
  ·
    refine ⟨91924807601704546705431239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61283205067803031136954159 91924807601704546705431239)
    ·
      refine ⟨137887211402556820058146859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91924807601704546705431239 137887211402556820058146859)
      ·
        refine ⟨206830817103835230087220289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137887211402556820058146859 206830817103835230087220289)
        ·
          refine ⟨155123112827876422565415217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206830817103835230087220289 155123112827876422565415217)
          ·
            refine ⟨116342334620907316924061413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155123112827876422565415217 116342334620907316924061413)
            ·
              refine ⟨21814187741420121923261515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116342334620907316924061413 21814187741420121923261515)
              ·
                refine ⟨32721281612130182884892273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21814187741420121923261515 32721281612130182884892273)
                ·
                  refine ⟨24540961209097637163669205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32721281612130182884892273 24540961209097637163669205)
                  ·
                    refine ⟨575178778338225871023497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24540961209097637163669205 575178778338225871023497)
                    ·
                      rfl

theorem cell22_1680235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_1680235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680235 prefixEnd_1680235 := by exact prefixLift 1680235
  have htrace : WordTrace (prefixWord ++ tailWord_1680235) baseStart_1680235 baseEnd_1680235 := by
    simpa [prefixWord, tailWord_1680235, baseEnd_1680235] using wordTrace_append hprefix tailTrace_1680235
  have hstable : (prefixWord ++ tailWord_1680235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680235).length < 2 ^ (prefixWord ++ tailWord_1680235).sum := by decide
  have hdescent : baseEnd_1680235 < baseStart_1680235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680254 : List Nat := [4, 2, 3, 1, 2, 10]
def baseStart_1680254 : Nat := 118140960795 + 1680254 * 2 ^ 59
def prefixEnd_1680254 : Nat := 4983230072969 + 3 ^ 40 * 1680254 * 2
def baseEnd_1680254 : Nat := 7101052869463162404919

theorem tailTrace_1680254 : CollatzResearch.WordTrace tailWord_1680254 prefixEnd_1680254 7101052869463162404919 := by
  unfold tailWord_1680254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7660487256841774672736977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40855932036489464921263877 7660487256841774672736977)
  ·
    refine ⟨5745365442631331004552733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7660487256841774672736977 5745365442631331004552733)
    ·
      refine ⟨2154512040986749126707275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5745365442631331004552733 2154512040986749126707275)
      ·
        refine ⟨3231768061480123690060913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154512040986749126707275 3231768061480123690060913)
        ·
          refine ⟨2423826046110092767545685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3231768061480123690060913 2423826046110092767545685)
          ·
            refine ⟨7101052869463162404919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2423826046110092767545685 7101052869463162404919)
            ·
              rfl

theorem cell22_1680254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 10].length) (baseStart_1680254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680254 prefixEnd_1680254 := by exact prefixLift 1680254
  have htrace : WordTrace (prefixWord ++ tailWord_1680254) baseStart_1680254 baseEnd_1680254 := by
    simpa [prefixWord, tailWord_1680254, baseEnd_1680254] using wordTrace_append hprefix tailTrace_1680254
  have hstable : (prefixWord ++ tailWord_1680254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680254).length < 2 ^ (prefixWord ++ tailWord_1680254).sum := by decide
  have hdescent : baseEnd_1680254 < baseStart_1680254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680327 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 6]
def baseStart_1680327 : Nat := 118140960795 + 1680327 * 2 ^ 59
def prefixEnd_1680327 : Nat := 4983230072969 + 3 ^ 40 * 1680327 * 2
def baseEnd_1680327 : Nat := 191736757272789432574405

theorem tailTrace_1680327 : CollatzResearch.WordTrace tailWord_1680327 prefixEnd_1680327 191736757272789432574405 := by
  unfold tailWord_1680327
  simp only [CollatzResearch.WordTrace]
  refine ⟨61286560583469730849303235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40857707055646487232868823 61286560583469730849303235)
  ·
    refine ⟨91929840875204596273954853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61286560583469730849303235 91929840875204596273954853)
    ·
      refine ⟨17236845164100861801366535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91929840875204596273954853 17236845164100861801366535)
      ·
        refine ⟨25855267746151292702049803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17236845164100861801366535 25855267746151292702049803)
        ·
          refine ⟨38782901619226939053074705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25855267746151292702049803 38782901619226939053074705)
          ·
            refine ⟨29087176214420204289806029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38782901619226939053074705 29087176214420204289806029)
            ·
              refine ⟨10907691080407576608677261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29087176214420204289806029 10907691080407576608677261)
              ·
                refine ⟨4090384155152841228253973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10907691080407576608677261 4090384155152841228253973)
                ·
                  refine ⟨191736757272789432574405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4090384155152841228253973 191736757272789432574405)
                  ·
                    rfl

theorem cell22_1680327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 6].length) (baseStart_1680327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680327 prefixEnd_1680327 := by exact prefixLift 1680327
  have htrace : WordTrace (prefixWord ++ tailWord_1680327) baseStart_1680327 baseEnd_1680327 := by
    simpa [prefixWord, tailWord_1680327, baseEnd_1680327] using wordTrace_append hprefix tailTrace_1680327
  have hstable : (prefixWord ++ tailWord_1680327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680327).length < 2 ^ (prefixWord ++ tailWord_1680327).sum := by decide
  have hdescent : baseEnd_1680327 < baseStart_1680327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680346 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_1680346 : Nat := 118140960795 + 1680346 * 2 ^ 59
def prefixEnd_1680346 : Nat := 4983230072969 + 3 ^ 40 * 1680346 * 2
def baseEnd_1680346 : Nat := 575216775906658581498157

theorem tailTrace_1680346 : CollatzResearch.WordTrace tailWord_1680346 prefixEnd_1680346 575216775906658581498157 := by
  unfold tailWord_1680346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15321813392600224273561223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40858169046933931396163261 15321813392600224273561223)
  ·
    refine ⟨22982720088900336410341835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15321813392600224273561223 22982720088900336410341835)
    ·
      refine ⟨34474080133350504615512753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22982720088900336410341835 34474080133350504615512753)
      ·
        refine ⟨25855560100012878461634565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34474080133350504615512753 25855560100012878461634565)
        ·
          refine ⟨4847917518752414711556481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25855560100012878461634565 4847917518752414711556481)
          ·
            refine ⟨3635938139064311033667361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4847917518752414711556481 3635938139064311033667361)
            ·
              refine ⟨2726953604298233275250521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3635938139064311033667361 2726953604298233275250521)
              ·
                refine ⟨2045215203223674956437891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726953604298233275250521 2045215203223674956437891)
                ·
                  refine ⟨3067822804835512434656837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045215203223674956437891 3067822804835512434656837)
                  ·
                    refine ⟨575216775906658581498157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3067822804835512434656837 575216775906658581498157)
                    ·
                      rfl

theorem cell22_1680346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_1680346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680346 prefixEnd_1680346 := by exact prefixLift 1680346
  have htrace : WordTrace (prefixWord ++ tailWord_1680346) baseStart_1680346 baseEnd_1680346 := by
    simpa [prefixWord, tailWord_1680346, baseEnd_1680346] using wordTrace_append hprefix tailTrace_1680346
  have hstable : (prefixWord ++ tailWord_1680346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680346).length < 2 ^ (prefixWord ++ tailWord_1680346).sum := by decide
  have hdescent : baseEnd_1680346 < baseStart_1680346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680436 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1680436 : Nat := 118140960795 + 1680436 * 2 ^ 59
def prefixEnd_1680436 : Nat := 4983230072969 + 3 ^ 40 * 1680436 * 2
def baseEnd_1680436 : Nat := 575247584745928346747881

theorem tailTrace_1680436 : CollatzResearch.WordTrace tailWord_1680436 prefixEnd_1680436 575247584745928346747881 := by
  unfold tailWord_1680436
  simp only [CollatzResearch.WordTrace]
  refine ⟨30645268070037421232510581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40860357426716561643347441 30645268070037421232510581)
  ·
    refine ⟨2872993881566008240547867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30645268070037421232510581 2872993881566008240547867)
    ·
      refine ⟨4309490822349012360821801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872993881566008240547867 4309490822349012360821801)
      ·
        refine ⟨3232118116761759270616351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4309490822349012360821801 3232118116761759270616351)
        ·
          refine ⟨4848177175142638905924527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232118116761759270616351 4848177175142638905924527)
          ·
            refine ⟨7272265762713958358886791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848177175142638905924527 7272265762713958358886791)
            ·
              refine ⟨10908398644070937538330187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7272265762713958358886791 10908398644070937538330187)
              ·
                refine ⟨16362597966106406307495281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10908398644070937538330187 16362597966106406307495281)
                ·
                  refine ⟨12271948474579804730621461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16362597966106406307495281 12271948474579804730621461)
                  ·
                    refine ⟨575247584745928346747881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12271948474579804730621461 575247584745928346747881)
                    ·
                      rfl

theorem cell22_1680436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1680436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680436 prefixEnd_1680436 := by exact prefixLift 1680436
  have htrace : WordTrace (prefixWord ++ tailWord_1680436) baseStart_1680436 baseEnd_1680436 := by
    simpa [prefixWord, tailWord_1680436, baseEnd_1680436] using wordTrace_append hprefix tailTrace_1680436
  have hstable : (prefixWord ++ tailWord_1680436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680436).length < 2 ^ (prefixWord ++ tailWord_1680436).sum := by decide
  have hdescent : baseEnd_1680436 < baseStart_1680436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680496 : List Nat := [2, 1, 1, 1, 5, 1, 1, 6, 4]
def baseStart_1680496 : Nat := 118140960795 + 1680496 * 2 ^ 59
def prefixEnd_1680496 : Nat := 4983230072969 + 3 ^ 40 * 1680496 * 2
def baseEnd_1680496 : Nat := 191756041324036063415899

theorem tailTrace_1680496 : CollatzResearch.WordTrace tailWord_1680496 prefixEnd_1680496 191756041324036063415899 := by
  unfold tailWord_1680496
  simp only [CollatzResearch.WordTrace]
  refine ⟨30646362259928736356102671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40861816346571648474803561 30646362259928736356102671)
  ·
    refine ⟨45969543389893104534154007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30646362259928736356102671 45969543389893104534154007)
    ·
      refine ⟨68954315084839656801231011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45969543389893104534154007 68954315084839656801231011)
      ·
        refine ⟨103431472627259485201846517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68954315084839656801231011 103431472627259485201846517)
        ·
          refine ⟨9696700558805576737673111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103431472627259485201846517 9696700558805576737673111)
          ·
            refine ⟨14545050838208365106509667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9696700558805576737673111 14545050838208365106509667)
            ·
              refine ⟨21817576257312547659764501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14545050838208365106509667 21817576257312547659764501)
              ·
                refine ⟨1022698887061525671551461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21817576257312547659764501 1022698887061525671551461)
                ·
                  refine ⟨191756041324036063415899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022698887061525671551461 191756041324036063415899)
                  ·
                    rfl

theorem cell22_1680496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 4].length) (baseStart_1680496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680496 prefixEnd_1680496 := by exact prefixLift 1680496
  have htrace : WordTrace (prefixWord ++ tailWord_1680496) baseStart_1680496 baseEnd_1680496 := by
    simpa [prefixWord, tailWord_1680496, baseEnd_1680496] using wordTrace_append hprefix tailTrace_1680496
  have hstable : (prefixWord ++ tailWord_1680496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680496).length < 2 ^ (prefixWord ++ tailWord_1680496).sum := by decide
  have hdescent : baseEnd_1680496 < baseStart_1680496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680509 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_1680509 : Nat := 118140960795 + 1680509 * 2 ^ 59
def prefixEnd_1680509 : Nat := 4983230072969 + 3 ^ 40 * 1680509 * 2
def baseEnd_1680509 : Nat := 575272574137780489672657

theorem tailTrace_1680509 : CollatzResearch.WordTrace tailWord_1680509 prefixEnd_1680509 575272574137780489672657 := by
  unfold tailWord_1680509
  simp only [CollatzResearch.WordTrace]
  refine ⟨61293198668810375932428581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40862132445873583954952387 61293198668810375932428581)
  ·
    refine ⟨11492474750401945487330359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61293198668810375932428581 11492474750401945487330359)
    ·
      refine ⟨17238712125602918230995539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11492474750401945487330359 17238712125602918230995539)
      ·
        refine ⟨25858068188404377346493309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17238712125602918230995539 25858068188404377346493309)
        ·
          refine ⟨9696775570651641504934991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25858068188404377346493309 9696775570651641504934991)
          ·
            refine ⟨14545163355977462257402487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9696775570651641504934991 14545163355977462257402487)
            ·
              refine ⟨21817745033966193386103731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14545163355977462257402487 21817745033966193386103731)
              ·
                refine ⟨32726617550949290079155597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21817745033966193386103731 32726617550949290079155597)
                ·
                  refine ⟨12272481581605983779683349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32726617550949290079155597 12272481581605983779683349)
                  ·
                    refine ⟨575272574137780489672657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12272481581605983779683349 575272574137780489672657)
                    ·
                      rfl

theorem cell22_1680509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_1680509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680509 prefixEnd_1680509 := by exact prefixLift 1680509
  have htrace : WordTrace (prefixWord ++ tailWord_1680509) baseStart_1680509 baseEnd_1680509 := by
    simpa [prefixWord, tailWord_1680509, baseEnd_1680509] using wordTrace_append hprefix tailTrace_1680509
  have hstable : (prefixWord ++ tailWord_1680509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680509).length < 2 ^ (prefixWord ++ tailWord_1680509).sum := by decide
  have hdescent : baseEnd_1680509 < baseStart_1680509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680526 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1680526 : Nat := 118140960795 + 1680526 * 2 ^ 59
def prefixEnd_1680526 : Nat := 4983230072969 + 3 ^ 40 * 1680526 * 2
def baseEnd_1680526 : Nat := 575278393585198111997605

theorem tailTrace_1680526 : CollatzResearch.WordTrace tailWord_1680526 prefixEnd_1680526 575278393585198111997605 := by
  unfold tailWord_1680526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7661727338718598479474679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40862545806499191890531621 7661727338718598479474679)
  ·
    refine ⟨11492591008077897719212019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7661727338718598479474679 11492591008077897719212019)
    ·
      refine ⟨17238886512116846578818029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11492591008077897719212019 17238886512116846578818029)
      ·
        refine ⟨6464582442043817467056761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17238886512116846578818029 6464582442043817467056761)
        ·
          refine ⟨4848436831532863100292571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6464582442043817467056761 4848436831532863100292571)
          ·
            refine ⟨7272655247299294650438857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848436831532863100292571 7272655247299294650438857)
            ·
              refine ⟨5454491435474470987829143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7272655247299294650438857 5454491435474470987829143)
              ·
                refine ⟨8181737153211706481743715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5454491435474470987829143 8181737153211706481743715)
                ·
                  refine ⟨12272605729817559722615573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8181737153211706481743715 12272605729817559722615573)
                  ·
                    refine ⟨575278393585198111997605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12272605729817559722615573 575278393585198111997605)
                    ·
                      rfl

theorem cell22_1680526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1680526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680526 prefixEnd_1680526 := by exact prefixLift 1680526
  have htrace : WordTrace (prefixWord ++ tailWord_1680526) baseStart_1680526 baseEnd_1680526 := by
    simpa [prefixWord, tailWord_1680526, baseEnd_1680526] using wordTrace_append hprefix tailTrace_1680526
  have hstable : (prefixWord ++ tailWord_1680526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680526).length < 2 ^ (prefixWord ++ tailWord_1680526).sum := by decide
  have hdescent : baseEnd_1680526 < baseStart_1680526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680530 : List Nat := [3, 2, 3, 1, 1, 4, 1, 3, 4]
def baseStart_1680530 : Nat := 118140960795 + 1680530 * 2 ^ 59
def prefixEnd_1680530 : Nat := 4983230072969 + 3 ^ 40 * 1680530 * 2
def baseEnd_1680530 : Nat := 191759920955647811632531

theorem tailTrace_1680530 : CollatzResearch.WordTrace tailWord_1680530 prefixEnd_1680530 191759920955647811632531 := by
  unfold tailWord_1680530
  simp only [CollatzResearch.WordTrace]
  refine ⟨15323491150433574129735761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40862643067822864345962029 15323491150433574129735761)
  ·
    refine ⟨11492618362825180597301821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15323491150433574129735761 11492618362825180597301821)
    ·
      refine ⟨4309731886059442723988183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11492618362825180597301821 4309731886059442723988183)
      ·
        refine ⟨6464597829089164085982275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4309731886059442723988183 6464597829089164085982275)
        ·
          refine ⟨9696896743633746128973413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6464597829089164085982275 9696896743633746128973413)
          ·
            refine ⟨1818168139431327399182515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9696896743633746128973413 1818168139431327399182515)
            ·
              refine ⟨2727252209146991098773773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1818168139431327399182515 2727252209146991098773773)
              ·
                refine ⟨1022719578430121662040165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2727252209146991098773773 1022719578430121662040165)
                ·
                  refine ⟨191759920955647811632531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022719578430121662040165 191759920955647811632531)
                  ·
                    rfl

theorem cell22_1680530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_1680530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680530 prefixEnd_1680530 := by exact prefixLift 1680530
  have htrace : WordTrace (prefixWord ++ tailWord_1680530) baseStart_1680530 baseEnd_1680530 := by
    simpa [prefixWord, tailWord_1680530, baseEnd_1680530] using wordTrace_append hprefix tailTrace_1680530
  have hstable : (prefixWord ++ tailWord_1680530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680530).length < 2 ^ (prefixWord ++ tailWord_1680530).sum := by decide
  have hdescent : baseEnd_1680530 < baseStart_1680530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680543 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 2, 4]
def baseStart_1680543 : Nat := 118140960795 + 1680543 * 2 ^ 59
def prefixEnd_1680543 : Nat := 4983230072969 + 3 ^ 40 * 1680543 * 2
def baseEnd_1680543 : Nat := 575284213032615734322553

theorem tailTrace_1680543 : CollatzResearch.WordTrace tailWord_1680543 prefixEnd_1680543 575284213032615734322553 := by
  unfold tailWord_1680543
  simp only [CollatzResearch.WordTrace]
  refine ⟨61294438750687199739166283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40862959167124799826110855 61294438750687199739166283)
  ·
    refine ⟨91941658126030799608749425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61294438750687199739166283 91941658126030799608749425)
    ·
      refine ⟨68956243594523099706562069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91941658126030799608749425 68956243594523099706562069)
      ·
        refine ⟨3232323918493270298745097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68956243594523099706562069 3232323918493270298745097)
        ·
          refine ⟨2424242938869952724058823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3232323918493270298745097 2424242938869952724058823)
          ·
            refine ⟨3636364408304929086088235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424242938869952724058823 3636364408304929086088235)
            ·
              refine ⟨5454546612457393629132353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3636364408304929086088235 5454546612457393629132353)
              ·
                refine ⟨4090909959343045221849265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5454546612457393629132353 4090909959343045221849265)
                ·
                  refine ⟨3068182469507283916386949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4090909959343045221849265 3068182469507283916386949)
                  ·
                    refine ⟨575284213032615734322553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3068182469507283916386949 575284213032615734322553)
                    ·
                      rfl

theorem cell22_1680543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_1680543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680543 prefixEnd_1680543 := by exact prefixLift 1680543
  have htrace : WordTrace (prefixWord ++ tailWord_1680543) baseStart_1680543 baseEnd_1680543 := by
    simpa [prefixWord, tailWord_1680543, baseEnd_1680543] using wordTrace_append hprefix tailTrace_1680543
  have hstable : (prefixWord ++ tailWord_1680543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680543).length < 2 ^ (prefixWord ++ tailWord_1680543).sum := by decide
  have hdescent : baseEnd_1680543 < baseStart_1680543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680556 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 3, 3]
def baseStart_1680556 : Nat := 118140960795 + 1680556 * 2 ^ 59
def prefixEnd_1680556 : Nat := 4983230072969 + 3 ^ 40 * 1680556 * 2
def baseEnd_1680556 : Nat := 575288663198288033747513

theorem tailTrace_1680556 : CollatzResearch.WordTrace tailWord_1680556 prefixEnd_1680556 575288663198288033747513 := by
  unfold tailWord_1680556
  simp only [CollatzResearch.WordTrace]
  refine ⟨30647456449820051479694761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40863275266426735306259681 30647456449820051479694761)
  ·
    refine ⟨22985592337365038609771071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30647456449820051479694761 22985592337365038609771071)
    ·
      refine ⟨34478388506047557914656607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22985592337365038609771071 34478388506047557914656607)
      ·
        refine ⟨51717582759071336871984911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34478388506047557914656607 51717582759071336871984911)
        ·
          refine ⟨77576374138607005307977367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51717582759071336871984911 77576374138607005307977367)
          ·
            refine ⟨116364561207910507961966051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77576374138607005307977367 116364561207910507961966051)
            ·
              refine ⟨174546841811865761942949077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116364561207910507961966051 174546841811865761942949077)
              ·
                refine ⟨4090941604965603795537869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 174546841811865761942949077 4090941604965603795537869)
                ·
                  refine ⟨1534103101862101423326701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4090941604965603795537869 1534103101862101423326701)
                  ·
                    refine ⟨575288663198288033747513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1534103101862101423326701 575288663198288033747513)
                    ·
                      rfl

theorem cell22_1680556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_1680556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680556 prefixEnd_1680556 := by exact prefixLift 1680556
  have htrace : WordTrace (prefixWord ++ tailWord_1680556) baseStart_1680556 baseEnd_1680556 := by
    simpa [prefixWord, tailWord_1680556, baseEnd_1680556] using wordTrace_append hprefix tailTrace_1680556
  have hstable : (prefixWord ++ tailWord_1680556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680556).length < 2 ^ (prefixWord ++ tailWord_1680556).sum := by decide
  have hdescent : baseEnd_1680556 < baseStart_1680556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680616 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1680616 : Nat := 118140960795 + 1680616 * 2 ^ 59
def prefixEnd_1680616 : Nat := 4983230072969 + 3 ^ 40 * 1680616 * 2
def baseEnd_1680616 : Nat := 575309202424467877247329

theorem tailTrace_1680616 : CollatzResearch.WordTrace tailWord_1680616 prefixEnd_1680616 575309202424467877247329 := by
  unfold tailWord_1680616
  simp only [CollatzResearch.WordTrace]
  refine ⟨30648550639711366603286851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40864734186281822137715801 30648550639711366603286851)
  ·
    refine ⟨45972825959567049904930277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30648550639711366603286851 45972825959567049904930277)
    ·
      refine ⟨8619904867418821857174427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45972825959567049904930277 8619904867418821857174427)
      ·
        refine ⟨12929857301128232785761641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8619904867418821857174427 12929857301128232785761641)
        ·
          refine ⟨9697392975846174589321231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12929857301128232785761641 9697392975846174589321231)
          ·
            refine ⟨14546089463769261883981847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9697392975846174589321231 14546089463769261883981847)
            ·
              refine ⟨21819134195653892825972771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14546089463769261883981847 21819134195653892825972771)
              ·
                refine ⟨32728701293480839238959157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21819134195653892825972771 32728701293480839238959157)
                ·
                  refine ⟨3068315746263828678652421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32728701293480839238959157 3068315746263828678652421)
                  ·
                    refine ⟨575309202424467877247329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3068315746263828678652421 575309202424467877247329)
                    ·
                      rfl

theorem cell22_1680616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1680616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680616 prefixEnd_1680616 := by exact prefixLift 1680616
  have htrace : WordTrace (prefixWord ++ tailWord_1680616) baseStart_1680616 baseEnd_1680616 := by
    simpa [prefixWord, tailWord_1680616, baseEnd_1680616] using wordTrace_append hprefix tailTrace_1680616
  have hstable : (prefixWord ++ tailWord_1680616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680616).length < 2 ^ (prefixWord ++ tailWord_1680616).sum := by decide
  have hdescent : baseEnd_1680616 < baseStart_1680616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680661 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1680661 : Nat := 118140960795 + 1680661 * 2 ^ 59
def prefixEnd_1680661 : Nat := 4983230072969 + 3 ^ 40 * 1680661 * 2
def baseEnd_1680661 : Nat := 575324606844102759872191

theorem tailTrace_1680661 : CollatzResearch.WordTrace tailWord_1680661 prefixEnd_1680661 575324606844102759872191 := by
  unfold tailWord_1680661
  simp only [CollatzResearch.WordTrace]
  refine ⟨61298742564259705891961837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40865828376173137261307891 61298742564259705891961837)
  ·
    refine ⟨22987028461597389709485689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61298742564259705891961837 22987028461597389709485689)
    ·
      refine ⟨17240271346198042282114267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22987028461597389709485689 17240271346198042282114267)
      ·
        refine ⟨25860407019297063423171401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17240271346198042282114267 25860407019297063423171401)
        ·
          refine ⟨19395305264472797567378551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25860407019297063423171401 19395305264472797567378551)
          ·
            refine ⟨29092957896709196351067827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19395305264472797567378551 29092957896709196351067827)
            ·
              refine ⟨43639436845063794526601741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29092957896709196351067827 43639436845063794526601741)
              ·
                refine ⟨16364788816898922947475653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43639436845063794526601741 16364788816898922947475653)
                ·
                  refine ⟨3068397903168548052651685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16364788816898922947475653 3068397903168548052651685)
                  ·
                    refine ⟨575324606844102759872191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3068397903168548052651685 575324606844102759872191)
                    ·
                      rfl

theorem cell22_1680661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1680661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680661 prefixEnd_1680661 := by exact prefixLift 1680661
  have htrace : WordTrace (prefixWord ++ tailWord_1680661) baseStart_1680661 baseEnd_1680661 := by
    simpa [prefixWord, tailWord_1680661, baseEnd_1680661] using wordTrace_append hprefix tailTrace_1680661
  have hstable : (prefixWord ++ tailWord_1680661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680661).length < 2 ^ (prefixWord ++ tailWord_1680661).sum := by decide
  have hdescent : baseEnd_1680661 < baseStart_1680661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680663 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 4, 3]
def baseStart_1680663 : Nat := 118140960795 + 1680663 * 2 ^ 59
def prefixEnd_1680663 : Nat := 4983230072969 + 3 ^ 40 * 1680663 * 2
def baseEnd_1680663 : Nat := 575325291484975421322185

theorem tailTrace_1680663 : CollatzResearch.WordTrace tailWord_1680663 prefixEnd_1680663 575325291484975421322185 := by
  unfold tailWord_1680663
  simp only [CollatzResearch.WordTrace]
  refine ⟨61298815510252460233534643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40865877006834973489023095 61298815510252460233534643)
  ·
    refine ⟨91948223265378690350301965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61298815510252460233534643 91948223265378690350301965)
    ·
      refine ⟨34480583724517008881363237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91948223265378690350301965 34480583724517008881363237)
      ·
        refine ⟨6465109448346939165255607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34480583724517008881363237 6465109448346939165255607)
        ·
          refine ⟨9697664172520408747883411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465109448346939165255607 9697664172520408747883411)
          ·
            refine ⟨14546496258780613121825117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9697664172520408747883411 14546496258780613121825117)
            ·
              refine ⟨5454936097042729920684419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14546496258780613121825117 5454936097042729920684419)
              ·
                refine ⟨8182404145564094881026629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5454936097042729920684419 8182404145564094881026629)
                ·
                  refine ⟨1534200777293267790192493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8182404145564094881026629 1534200777293267790192493)
                  ·
                    refine ⟨575325291484975421322185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1534200777293267790192493 575325291484975421322185)
                    ·
                      rfl

theorem cell22_1680663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_1680663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680663 prefixEnd_1680663 := by exact prefixLift 1680663
  have htrace : WordTrace (prefixWord ++ tailWord_1680663) baseStart_1680663 baseEnd_1680663 := by
    simpa [prefixWord, tailWord_1680663, baseEnd_1680663] using wordTrace_append hprefix tailTrace_1680663
  have hstable : (prefixWord ++ tailWord_1680663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680663).length < 2 ^ (prefixWord ++ tailWord_1680663).sum := by decide
  have hdescent : baseEnd_1680663 < baseStart_1680663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680676 : List Nat := [2, 3, 1, 3, 1, 1, 2, 9]
def baseStart_1680676 : Nat := 118140960795 + 1680676 * 2 ^ 59
def prefixEnd_1680676 : Nat := 4983230072969 + 3 ^ 40 * 1680676 * 2
def baseEnd_1680676 : Nat := 63925526850071968971905

theorem tailTrace_1680676 : CollatzResearch.WordTrace tailWord_1680676 prefixEnd_1680676 63925526850071968971905 := by
  unfold tailWord_1680676
  simp only [CollatzResearch.WordTrace]
  refine ⟨30649644829602681726878941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40866193106136908969171921 30649644829602681726878941)
  ·
    refine ⟨11493616811101005647579603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30649644829602681726878941 11493616811101005647579603)
    ·
      refine ⟨17240425216651508471369405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11493616811101005647579603 17240425216651508471369405)
      ·
        refine ⟨6465159456244315676763527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17240425216651508471369405 6465159456244315676763527)
        ·
          refine ⟨9697739184366473515145291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465159456244315676763527 9697739184366473515145291)
          ·
            refine ⟨14546608776549710272717937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9697739184366473515145291 14546608776549710272717937)
            ·
              refine ⟨10909956582412282704538453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14546608776549710272717937 10909956582412282704538453)
              ·
                refine ⟨63925526850071968971905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10909956582412282704538453 63925526850071968971905)
                ·
                  rfl

theorem cell22_1680676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 9].length) (baseStart_1680676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680676 prefixEnd_1680676 := by exact prefixLift 1680676
  have htrace : WordTrace (prefixWord ++ tailWord_1680676) baseStart_1680676 baseEnd_1680676 := by
    simpa [prefixWord, tailWord_1680676, baseEnd_1680676] using wordTrace_append hprefix tailTrace_1680676
  have hstable : (prefixWord ++ tailWord_1680676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680676).length < 2 ^ (prefixWord ++ tailWord_1680676).sum := by decide
  have hdescent : baseEnd_1680676 < baseStart_1680676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680680 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1680680 : Nat := 118140960795 + 1680680 * 2 ^ 59
def prefixEnd_1680680 : Nat := 4983230072969 + 3 ^ 40 * 1680680 * 2
def baseEnd_1680680 : Nat := 575331110932393043647133

theorem tailTrace_1680680 : CollatzResearch.WordTrace tailWord_1680680 prefixEnd_1680680 575331110932393043647133 := by
  unfold tailWord_1680680
  simp only [CollatzResearch.WordTrace]
  refine ⟨30649717775595436068451747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40866290367460581424602329 30649717775595436068451747)
  ·
    refine ⟨45974576663393154102677621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30649717775595436068451747 45974576663393154102677621)
    ·
      refine ⟨4310116562193108197126027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45974576663393154102677621 4310116562193108197126027)
      ·
        refine ⟨6465174843289662295689041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310116562193108197126027 6465174843289662295689041)
        ·
          refine ⟨4848881132467246721766781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6465174843289662295689041 4848881132467246721766781)
          ·
            refine ⟨1818330424675217520662543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4848881132467246721766781 1818330424675217520662543)
            ·
              refine ⟨2727495637012826280993815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1818330424675217520662543 2727495637012826280993815)
              ·
                refine ⟨4091243455519239421490723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2727495637012826280993815 4091243455519239421490723)
                ·
                  refine ⟨6136865183278859132236085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091243455519239421490723 6136865183278859132236085)
                  ·
                    refine ⟨575331110932393043647133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6136865183278859132236085 575331110932393043647133)
                    ·
                      rfl

theorem cell22_1680680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1680680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680680 prefixEnd_1680680 := by exact prefixLift 1680680
  have htrace : WordTrace (prefixWord ++ tailWord_1680680) baseStart_1680680 baseEnd_1680680 := by
    simpa [prefixWord, tailWord_1680680, baseEnd_1680680] using wordTrace_append hprefix tailTrace_1680680
  have hstable : (prefixWord ++ tailWord_1680680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680680).length < 2 ^ (prefixWord ++ tailWord_1680680).sum := by decide
  have hdescent : baseEnd_1680680 < baseStart_1680680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680693 : List Nat := [1, 3, 3, 1, 2, 2, 4, 6]
def baseStart_1680693 : Nat := 118140960795 + 1680693 * 2 ^ 59
def prefixEnd_1680693 : Nat := 4983230072969 + 3 ^ 40 * 1680693 * 2
def baseEnd_1680693 : Nat := 63926173455340593674677

theorem tailTrace_1680693 : CollatzResearch.WordTrace tailWord_1680693 prefixEnd_1680693 63926173455340593674677 := by
  unfold tailWord_1680693
  simp only [CollatzResearch.WordTrace]
  refine ⟨61299909700143775357126733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40866606466762516904751155 61299909700143775357126733)
  ·
    refine ⟨22987466137553915758922525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61299909700143775357126733 22987466137553915758922525)
    ·
      refine ⟨8620299801582718409595947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22987466137553915758922525 8620299801582718409595947)
      ·
        refine ⟨12930449702374077614393921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8620299801582718409595947 12930449702374077614393921)
        ·
          refine ⟨9697837276780558210795441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12930449702374077614393921 9697837276780558210795441)
          ·
            refine ⟨7273377957585418658096581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9697837276780558210795441 7273377957585418658096581)
            ·
              refine ⟨1363758367047265998393109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7273377957585418658096581 1363758367047265998393109)
              ·
                refine ⟨63926173455340593674677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1363758367047265998393109 63926173455340593674677)
                ·
                  rfl

theorem cell22_1680693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 6].length) (baseStart_1680693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680693 prefixEnd_1680693 := by exact prefixLift 1680693
  have htrace : WordTrace (prefixWord ++ tailWord_1680693) baseStart_1680693 baseEnd_1680693 := by
    simpa [prefixWord, tailWord_1680693, baseEnd_1680693] using wordTrace_append hprefix tailTrace_1680693
  have hstable : (prefixWord ++ tailWord_1680693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680693).length < 2 ^ (prefixWord ++ tailWord_1680693).sum := by decide
  have hdescent : baseEnd_1680693 < baseStart_1680693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680721 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 7]
def baseStart_1680721 : Nat := 118140960795 + 1680721 * 2 ^ 59
def prefixEnd_1680721 : Nat := 4983230072969 + 3 ^ 40 * 1680721 * 2
def baseEnd_1680721 : Nat := 191781715356760867790669

theorem tailTrace_1680721 : CollatzResearch.WordTrace tailWord_1680721 prefixEnd_1680721 191781715356760867790669 := by
  unfold tailWord_1680721
  simp only [CollatzResearch.WordTrace]
  refine ⟨61300930944042336139146017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40867287296028224092764011 61300930944042336139146017)
  ·
    refine ⟨45975698208031752104359513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61300930944042336139146017 45975698208031752104359513)
    ·
      refine ⟨34481773656023814078269635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45975698208031752104359513 34481773656023814078269635)
      ·
        refine ⟨51722660484035721117404453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34481773656023814078269635 51722660484035721117404453)
        ·
          refine ⟨9697998840756697709513335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51722660484035721117404453 9697998840756697709513335)
          ·
            refine ⟨14546998261135046564270003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9697998840756697709513335 14546998261135046564270003)
            ·
              refine ⟨21820497391702569846405005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14546998261135046564270003 21820497391702569846405005)
              ·
                refine ⟨8182686521888463692401877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21820497391702569846405005 8182686521888463692401877)
                ·
                  refine ⟨191781715356760867790669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8182686521888463692401877 191781715356760867790669)
                  ·
                    rfl

theorem cell22_1680721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_1680721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680721 prefixEnd_1680721 := by exact prefixLift 1680721
  have htrace : WordTrace (prefixWord ++ tailWord_1680721) baseStart_1680721 baseEnd_1680721 := by
    simpa [prefixWord, tailWord_1680721, baseEnd_1680721] using wordTrace_append hprefix tailTrace_1680721
  have hstable : (prefixWord ++ tailWord_1680721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680721).length < 2 ^ (prefixWord ++ tailWord_1680721).sum := by decide
  have hdescent : baseEnd_1680721 < baseStart_1680721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680725 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 3, 3]
def baseStart_1680725 : Nat := 118140960795 + 1680725 * 2 ^ 59
def prefixEnd_1680725 : Nat := 4983230072969 + 3 ^ 40 * 1680725 * 2
def baseEnd_1680725 : Nat := 575346515352027926271995

theorem tailTrace_1680725 : CollatzResearch.WordTrace tailWord_1680725 prefixEnd_1680725 575346515352027926271995 := by
  unfold tailWord_1680725
  simp only [CollatzResearch.WordTrace]
  refine ⟨61301076836027844822291629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40867384557351896548194419 61301076836027844822291629)
  ·
    refine ⟨22987903813510441808359361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61301076836027844822291629 22987903813510441808359361)
    ·
      refine ⟨17240927860132831356269521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22987903813510441808359361 17240927860132831356269521)
      ·
        refine ⟨12930695895099623517202141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17240927860132831356269521 12930695895099623517202141)
        ·
          refine ⟨4849010960662358818950803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12930695895099623517202141 4849010960662358818950803)
          ·
            refine ⟨7273516440993538228426205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4849010960662358818950803 7273516440993538228426205)
            ·
              refine ⟨2727568665372576835659827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7273516440993538228426205 2727568665372576835659827)
              ·
                refine ⟨4091352998058865253489741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2727568665372576835659827 4091352998058865253489741)
                ·
                  refine ⟨1534257374272074470058653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4091352998058865253489741 1534257374272074470058653)
                  ·
                    refine ⟨575346515352027926271995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1534257374272074470058653 575346515352027926271995)
                    ·
                      rfl

theorem cell22_1680725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_1680725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680725 prefixEnd_1680725 := by exact prefixLift 1680725
  have htrace : WordTrace (prefixWord ++ tailWord_1680725) baseStart_1680725 baseEnd_1680725 := by
    simpa [prefixWord, tailWord_1680725, baseEnd_1680725] using wordTrace_append hprefix tailTrace_1680725
  have hstable : (prefixWord ++ tailWord_1680725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680725).length < 2 ^ (prefixWord ++ tailWord_1680725).sum := by decide
  have hdescent : baseEnd_1680725 < baseStart_1680725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680768 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 1, 4]
def baseStart_1680768 : Nat := 118140960795 + 1680768 * 2 ^ 59
def prefixEnd_1680768 : Nat := 4983230072969 + 3 ^ 40 * 1680768 * 2
def baseEnd_1680768 : Nat := 575361235130790147446863

theorem tailTrace_1680768 : CollatzResearch.WordTrace tailWord_1680768 prefixEnd_1680768 575361235130790147446863 := by
  unfold tailWord_1680768
  simp only [CollatzResearch.WordTrace]
  refine ⟨30651322587436031583053479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40868430116581375444071305 30651322587436031583053479)
  ·
    refine ⟨45976983881154047374580219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30651322587436031583053479 45976983881154047374580219)
    ·
      refine ⟨68965475821731071061870329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45976983881154047374580219 68965475821731071061870329)
      ·
        refine ⟨51724106866298303296402747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68965475821731071061870329 51724106866298303296402747)
        ·
          refine ⟨77586160299447454944604121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51724106866298303296402747 77586160299447454944604121)
          ·
            refine ⟨58189620224585591208453091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77586160299447454944604121 58189620224585591208453091)
            ·
              refine ⟨87284430336878386812679637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58189620224585591208453091 87284430336878386812679637)
              ·
                refine ⟨2045728836020587190922179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 87284430336878386812679637 2045728836020587190922179)
                ·
                  refine ⟨3068593254030880786383269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045728836020587190922179 3068593254030880786383269)
                  ·
                    refine ⟨575361235130790147446863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3068593254030880786383269 575361235130790147446863)
                    ·
                      rfl

theorem cell22_1680768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_1680768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680768 prefixEnd_1680768 := by exact prefixLift 1680768
  have htrace : WordTrace (prefixWord ++ tailWord_1680768) baseStart_1680768 baseEnd_1680768 := by
    simpa [prefixWord, tailWord_1680768, baseEnd_1680768] using wordTrace_append hprefix tailTrace_1680768
  have hstable : (prefixWord ++ tailWord_1680768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680768).length < 2 ^ (prefixWord ++ tailWord_1680768).sum := by decide
  have hdescent : baseEnd_1680768 < baseStart_1680768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680952 : List Nat := [2, 1, 2, 1, 4, 3, 1, 4, 4]
def baseStart_1680952 : Nat := 118140960795 + 1680952 * 2 ^ 59
def prefixEnd_1680952 : Nat := 4983230072969 + 3 ^ 40 * 1680952 * 2
def baseEnd_1680952 : Nat := 191808074030358333615433

theorem tailTrace_1680952 : CollatzResearch.WordTrace tailWord_1680952 prefixEnd_1680952 191808074030358333615433 := by
  unfold tailWord_1680952
  simp only [CollatzResearch.WordTrace]
  refine ⟨30654678103102731295402555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40872904137470308393870073 30654678103102731295402555)
  ·
    refine ⟨45982017154654096943103833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30654678103102731295402555 45982017154654096943103833)
    ·
      refine ⟨34486512865990572707327875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45982017154654096943103833 34486512865990572707327875)
      ·
        refine ⟨51729769298985859060991813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34486512865990572707327875 51729769298985859060991813)
        ·
          refine ⟨9699331743559848573935965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51729769298985859060991813 9699331743559848573935965)
          ·
            refine ⟨3637249403834943215225987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9699331743559848573935965 3637249403834943215225987)
            ·
              refine ⟨5455874105752414822838981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3637249403834943215225987 5455874105752414822838981)
              ·
                refine ⟨1022976394828577779282309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5455874105752414822838981 1022976394828577779282309)
                ·
                  refine ⟨191808074030358333615433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022976394828577779282309 191808074030358333615433)
                  ·
                    rfl

theorem cell22_1680952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 4].length) (baseStart_1680952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680952 prefixEnd_1680952 := by exact prefixLift 1680952
  have htrace : WordTrace (prefixWord ++ tailWord_1680952) baseStart_1680952 baseEnd_1680952 := by
    simpa [prefixWord, tailWord_1680952, baseEnd_1680952] using wordTrace_append hprefix tailTrace_1680952
  have hstable : (prefixWord ++ tailWord_1680952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680952).length < 2 ^ (prefixWord ++ tailWord_1680952).sum := by decide
  have hdescent : baseEnd_1680952 < baseStart_1680952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680967 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 1, 5]
def baseStart_1680967 : Nat := 118140960795 + 1680967 * 2 ^ 59
def prefixEnd_1680967 : Nat := 4983230072969 + 3 ^ 40 * 1680967 * 2
def baseEnd_1680967 : Nat := 575429356897619961721253

theorem tailTrace_1680967 : CollatzResearch.WordTrace tailWord_1680967 prefixEnd_1680967 575429356897619961721253 := by
  unfold tailWord_1680967
  simp only [CollatzResearch.WordTrace]
  refine ⟨61309903301151120152601155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40873268867434080101734103 61309903301151120152601155)
  ·
    refine ⟨91964854951726680228901733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61309903301151120152601155 91964854951726680228901733)
    ·
      refine ⟨17243410303448752542919075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91964854951726680228901733 17243410303448752542919075)
      ·
        refine ⟨25865115455173128814378613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17243410303448752542919075 25865115455173128814378613)
        ·
          refine ⟨2424854573922480826347995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25865115455173128814378613 2424854573922480826347995)
          ·
            refine ⟨3637281860883721239521993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424854573922480826347995 3637281860883721239521993)
            ·
              refine ⟨2727961395662790929641495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3637281860883721239521993 2727961395662790929641495)
              ·
                refine ⟨4091942093494186394462243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2727961395662790929641495 4091942093494186394462243)
                ·
                  refine ⟨6137913140241279591693365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091942093494186394462243 6137913140241279591693365)
                  ·
                    refine ⟨575429356897619961721253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6137913140241279591693365 575429356897619961721253)
                    ·
                      rfl

theorem cell22_1680967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_1680967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1680967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1680967 prefixEnd_1680967 := by exact prefixLift 1680967
  have htrace : WordTrace (prefixWord ++ tailWord_1680967) baseStart_1680967 baseEnd_1680967 := by
    simpa [prefixWord, tailWord_1680967, baseEnd_1680967] using wordTrace_append hprefix tailTrace_1680967
  have hstable : (prefixWord ++ tailWord_1680967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680967).length < 2 ^ (prefixWord ++ tailWord_1680967).sum := by decide
  have hdescent : baseEnd_1680967 < baseStart_1680967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681102 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1681102 : Nat := 118140960795 + 1681102 * 2 ^ 59
def prefixEnd_1681102 : Nat := 4983230072969 + 3 ^ 40 * 1681102 * 2
def baseEnd_1681102 : Nat := 575475570156524609595839

theorem tailTrace_1681102 : CollatzResearch.WordTrace tailWord_1681102 prefixEnd_1681102 575475570156524609595839 := by
  unfold tailWord_1681102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7664353394457754776095695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40876551437108025472510373 7664353394457754776095695)
  ·
    refine ⟨11496530091686632164143543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7664353394457754776095695 11496530091686632164143543)
    ·
      refine ⟨17244795137529948246215315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11496530091686632164143543 17244795137529948246215315)
      ·
        refine ⟨25867192706294922369322973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17244795137529948246215315 25867192706294922369322973)
        ·
          refine ⟨9700197264860595888496115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25867192706294922369322973 9700197264860595888496115)
          ·
            refine ⟨14550295897290893832744173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9700197264860595888496115 14550295897290893832744173)
            ·
              refine ⟨5456360961484085187279065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14550295897290893832744173 5456360961484085187279065)
              ·
                refine ⟨4092270721113063890459299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5456360961484085187279065 4092270721113063890459299)
                ·
                  refine ⟨6138406081669595835688949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092270721113063890459299 6138406081669595835688949)
                  ·
                    refine ⟨575475570156524609595839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6138406081669595835688949 575475570156524609595839)
                    ·
                      rfl

theorem cell22_1681102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1681102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681102 prefixEnd_1681102 := by exact prefixLift 1681102
  have htrace : WordTrace (prefixWord ++ tailWord_1681102) baseStart_1681102 baseEnd_1681102 := by
    simpa [prefixWord, tailWord_1681102, baseEnd_1681102] using wordTrace_append hprefix tailTrace_1681102
  have hstable : (prefixWord ++ tailWord_1681102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681102).length < 2 ^ (prefixWord ++ tailWord_1681102).sum := by decide
  have hdescent : baseEnd_1681102 < baseStart_1681102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681106 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_1681106 : Nat := 118140960795 + 1681106 * 2 ^ 59
def prefixEnd_1681106 : Nat := 4983230072969 + 3 ^ 40 * 1681106 * 2
def baseEnd_1681106 : Nat := 575476939438269932495827

theorem tailTrace_1681106 : CollatzResearch.WordTrace tailWord_1681106 prefixEnd_1681106 575476939438269932495827 := by
  unfold tailWord_1681106
  simp only [CollatzResearch.WordTrace]
  refine ⟨15328743261911886722977793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40876648698431697927940781 15328743261911886722977793)
  ·
    refine ⟨11496557446433915042233345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15328743261911886722977793 11496557446433915042233345)
    ·
      refine ⟨8622418084825436281675009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11496557446433915042233345 8622418084825436281675009)
      ·
        refine ⟨6466813563619077211256257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8622418084825436281675009 6466813563619077211256257)
        ·
          refine ⟨4850110172714307908442193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6466813563619077211256257 4850110172714307908442193)
          ·
            refine ⟨3637582629535730931331645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4850110172714307908442193 3637582629535730931331645)
            ·
              refine ⟨1364093486075899099249367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3637582629535730931331645 1364093486075899099249367)
              ·
                refine ⟨2046140229113848648874051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364093486075899099249367 2046140229113848648874051)
                ·
                  refine ⟨3069210343670772973311077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046140229113848648874051 3069210343670772973311077)
                  ·
                    refine ⟨575476939438269932495827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3069210343670772973311077 575476939438269932495827)
                    ·
                      rfl

theorem cell22_1681106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_1681106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681106 prefixEnd_1681106 := by exact prefixLift 1681106
  have htrace : WordTrace (prefixWord ++ tailWord_1681106) baseStart_1681106 baseEnd_1681106 := by
    simpa [prefixWord, tailWord_1681106, baseEnd_1681106] using wordTrace_append hprefix tailTrace_1681106
  have hstable : (prefixWord ++ tailWord_1681106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681106).length < 2 ^ (prefixWord ++ tailWord_1681106).sum := by decide
  have hdescent : baseEnd_1681106 < baseStart_1681106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681119 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 2, 3]
def baseStart_1681119 : Nat := 118140960795 + 1681119 * 2 ^ 59
def prefixEnd_1681119 : Nat := 4983230072969 + 3 ^ 40 * 1681119 * 2
def baseEnd_1681119 : Nat := 575481389603942231920787

theorem tailTrace_1681119 : CollatzResearch.WordTrace tailWord_1681119 prefixEnd_1681119 575481389603942231920787 := by
  unfold tailWord_1681119
  simp only [CollatzResearch.WordTrace]
  refine ⟨61315447196600450112134411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40876964797733633408089607 61315447196600450112134411)
  ·
    refine ⟨91973170794900675168201617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61315447196600450112134411 91973170794900675168201617)
    ·
      refine ⟨68979878096175506376151213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91973170794900675168201617 68979878096175506376151213)
      ·
        refine ⟨25867454286065814891056705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68979878096175506376151213 25867454286065814891056705)
        ·
          refine ⟨19400590714549361168292529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25867454286065814891056705 19400590714549361168292529)
          ·
            refine ⟨14550443035912020876219397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19400590714549361168292529 14550443035912020876219397)
            ·
              refine ⟨2728208069233503914291137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14550443035912020876219397 2728208069233503914291137)
              ·
                refine ⟨2046156051925127935718353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728208069233503914291137 2046156051925127935718353)
                ·
                  refine ⟨1534617038943845951788765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2046156051925127935718353 1534617038943845951788765)
                  ·
                    refine ⟨575481389603942231920787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1534617038943845951788765 575481389603942231920787)
                    ·
                      rfl

theorem cell22_1681119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 3].length) (baseStart_1681119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681119 prefixEnd_1681119 := by exact prefixLift 1681119
  have htrace : WordTrace (prefixWord ++ tailWord_1681119) baseStart_1681119 baseEnd_1681119 := by
    simpa [prefixWord, tailWord_1681119, baseEnd_1681119] using wordTrace_append hprefix tailTrace_1681119
  have hstable : (prefixWord ++ tailWord_1681119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681119).length < 2 ^ (prefixWord ++ tailWord_1681119).sum := by decide
  have hdescent : baseEnd_1681119 < baseStart_1681119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681215 : List Nat := [1, 1, 2, 2, 7, 1, 1, 3, 1, 3]
def baseStart_1681215 : Nat := 118140960795 + 1681215 * 2 ^ 59
def prefixEnd_1681215 : Nat := 4983230072969 + 3 ^ 40 * 1681215 * 2
def baseEnd_1681215 : Nat := 575514252365829981520493

theorem tailTrace_1681215 : CollatzResearch.WordTrace tailWord_1681215 prefixEnd_1681215 575514252365829981520493 := by
  unfold tailWord_1681215
  simp only [CollatzResearch.WordTrace]
  refine ⟨61318948604252658507629099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40879299069501772338419399 61318948604252658507629099)
  ·
    refine ⟨91978422906378987761443649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61318948604252658507629099 91978422906378987761443649)
    ·
      refine ⟨68983817179784240821082737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91978422906378987761443649 68983817179784240821082737)
      ·
        refine ⟨51737862884838180615812053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68983817179784240821082737 51737862884838180615812053)
        ·
          refine ⟨1212606161363394858183095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 51737862884838180615812053 1212606161363394858183095)
          ·
            refine ⟨1818909242045092287274643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212606161363394858183095 1818909242045092287274643)
            ·
              refine ⟨2728363863067638430911965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1818909242045092287274643 2728363863067638430911965)
              ·
                refine ⟨1023136448650364411591987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2728363863067638430911965 1023136448650364411591987)
                ·
                  refine ⟨1534704672975546617387981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023136448650364411591987 1534704672975546617387981)
                  ·
                    refine ⟨575514252365829981520493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1534704672975546617387981 575514252365829981520493)
                    ·
                      rfl

theorem cell22_1681215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 1, 3].length) (baseStart_1681215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681215 prefixEnd_1681215 := by exact prefixLift 1681215
  have htrace : WordTrace (prefixWord ++ tailWord_1681215) baseStart_1681215 baseEnd_1681215 := by
    simpa [prefixWord, tailWord_1681215, baseEnd_1681215] using wordTrace_append hprefix tailTrace_1681215
  have hstable : (prefixWord ++ tailWord_1681215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681215).length < 2 ^ (prefixWord ++ tailWord_1681215).sum := by decide
  have hdescent : baseEnd_1681215 < baseStart_1681215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681224 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 1, 4]
def baseStart_1681224 : Nat := 118140960795 + 1681224 * 2 ^ 59
def prefixEnd_1681224 : Nat := 4983230072969 + 3 ^ 40 * 1681224 * 2
def baseEnd_1681224 : Nat := 575517333249756958045465

theorem tailTrace_1681224 : CollatzResearch.WordTrace tailWord_1681224 prefixEnd_1681224 575517333249756958045465 := by
  unfold tailWord_1681224
  simp only [CollatzResearch.WordTrace]
  refine ⟨30659638430610026522353363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40879517907480035363137817 30659638430610026522353363)
  ·
    refine ⟨45989457645915039783530045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30659638430610026522353363 45989457645915039783530045)
    ·
      refine ⟨17246046617218139918823767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45989457645915039783530045 17246046617218139918823767)
      ·
        refine ⟨25869069925827209878235651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17246046617218139918823767 25869069925827209878235651)
        ·
          refine ⟨38803604888740814817353477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25869069925827209878235651 38803604888740814817353477)
          ·
            refine ⟨7275675916638902778253777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38803604888740814817353477 7275675916638902778253777)
            ·
              refine ⟨5456756937479177083690333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7275675916638902778253777 5456756937479177083690333)
              ·
                refine ⟨2046283851554691406383875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5456756937479177083690333 2046283851554691406383875)
                ·
                  refine ⟨3069425777332037109575813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046283851554691406383875 3069425777332037109575813)
                  ·
                    refine ⟨575517333249756958045465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3069425777332037109575813 575517333249756958045465)
                    ·
                      rfl

theorem cell22_1681224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_1681224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681224 prefixEnd_1681224 := by exact prefixLift 1681224
  have htrace : WordTrace (prefixWord ++ tailWord_1681224) baseStart_1681224 baseEnd_1681224 := by
    simpa [prefixWord, tailWord_1681224, baseEnd_1681224] using wordTrace_append hprefix tailTrace_1681224
  have hstable : (prefixWord ++ tailWord_1681224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681224).length < 2 ^ (prefixWord ++ tailWord_1681224).sum := by decide
  have hdescent : baseEnd_1681224 < baseStart_1681224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681288 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 2, 3]
def baseStart_1681288 : Nat := 118140960795 + 1681288 * 2 ^ 59
def prefixEnd_1681288 : Nat := 4983230072969 + 3 ^ 40 * 1681288 * 2
def baseEnd_1681288 : Nat := 575539241757682124445269

theorem tailTrace_1681288 : CollatzResearch.WordTrace tailWord_1681288 prefixEnd_1681288 575539241757682124445269 := by
  unfold tailWord_1681288
  simp only [CollatzResearch.WordTrace]
  refine ⟨30660805566494095987518259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40881074088658794650024345 30660805566494095987518259)
  ·
    refine ⟨45991208349741143981277389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30660805566494095987518259 45991208349741143981277389)
    ·
      refine ⟨17246703131152928992979021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45991208349741143981277389 17246703131152928992979021)
      ·
        refine ⟨6467513674182348372367133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17246703131152928992979021 6467513674182348372367133)
        ·
          refine ⟨2425317627818380639637675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6467513674182348372367133 2425317627818380639637675)
          ·
            refine ⟨3637976441727570959456513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425317627818380639637675 3637976441727570959456513)
            ·
              refine ⟨2728482331295678219592385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3637976441727570959456513 2728482331295678219592385)
              ·
                refine ⟨2046361748471758664694289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728482331295678219592385 2046361748471758664694289)
                ·
                  refine ⟨1534771311353818998520717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2046361748471758664694289 1534771311353818998520717)
                  ·
                    refine ⟨575539241757682124445269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1534771311353818998520717 575539241757682124445269)
                    ·
                      rfl

theorem cell22_1681288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_1681288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681288 prefixEnd_1681288 := by exact prefixLift 1681288
  have htrace : WordTrace (prefixWord ++ tailWord_1681288) baseStart_1681288 baseEnd_1681288 := by
    simpa [prefixWord, tailWord_1681288, baseEnd_1681288] using wordTrace_append hprefix tailTrace_1681288
  have hstable : (prefixWord ++ tailWord_1681288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681288).length < 2 ^ (prefixWord ++ tailWord_1681288).sum := by decide
  have hdescent : baseEnd_1681288 < baseStart_1681288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681290 : List Nat := [3, 1, 2, 4, 2, 2, 2, 2, 4]
def baseStart_1681290 : Nat := 118140960795 + 1681290 * 2 ^ 59
def prefixEnd_1681290 : Nat := 4983230072969 + 3 ^ 40 * 1681290 * 2
def baseEnd_1681290 : Nat := 191846642132851595298421

theorem tailTrace_1681290 : CollatzResearch.WordTrace tailWord_1681290 prefixEnd_1681290 191846642132851595298421 := by
  unfold tailWord_1681290
  simp only [CollatzResearch.WordTrace]
  refine ⟨15330421019745236579152331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40881122719320630877739549 15330421019745236579152331)
  ·
    refine ⟨22995631529617854868728497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15330421019745236579152331 22995631529617854868728497)
    ·
      refine ⟨17246723647213391151546373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22995631529617854868728497 17246723647213391151546373)
      ·
        refine ⟨3233760683852510840914945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17246723647213391151546373 3233760683852510840914945)
        ·
          refine ⟨2425320512889383130686209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3233760683852510840914945 2425320512889383130686209)
          ·
            refine ⟨1818990384667037348014657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425320512889383130686209 1818990384667037348014657)
            ·
              refine ⟨1364242788500278011010993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818990384667037348014657 1364242788500278011010993)
              ·
                refine ⟨1023182091375208508258245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364242788500278011010993 1023182091375208508258245)
                ·
                  refine ⟨191846642132851595298421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1023182091375208508258245 191846642132851595298421)
                  ·
                    rfl

theorem cell22_1681290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_1681290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681290 prefixEnd_1681290 := by exact prefixLift 1681290
  have htrace : WordTrace (prefixWord ++ tailWord_1681290) baseStart_1681290 baseEnd_1681290 := by
    simpa [prefixWord, tailWord_1681290, baseEnd_1681290] using wordTrace_append hprefix tailTrace_1681290
  have hstable : (prefixWord ++ tailWord_1681290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681290).length < 2 ^ (prefixWord ++ tailWord_1681290).sum := by decide
  have hdescent : baseEnd_1681290 < baseStart_1681290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681297 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_1681297 : Nat := 118140960795 + 1681297 * 2 ^ 59
def prefixEnd_1681297 : Nat := 4983230072969 + 3 ^ 40 * 1681297 * 2
def baseEnd_1681297 : Nat := 575542322641609100970241

theorem tailTrace_1681297 : CollatzResearch.WordTrace tailWord_1681297 prefixEnd_1681297 575542322641609100970241 := by
  unfold tailWord_1681297
  simp only [CollatzResearch.WordTrace]
  refine ⟨61321939389955586512114145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40881292926637057674742763 61321939389955586512114145)
  ·
    refine ⟨45991454542466689884085609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61321939389955586512114145 45991454542466689884085609)
    ·
      refine ⟨34493590906850017413064207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45991454542466689884085609 34493590906850017413064207)
      ·
        refine ⟨51740386360275026119596311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34493590906850017413064207 51740386360275026119596311)
        ·
          refine ⟨77610579540412539179394467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51740386360275026119596311 77610579540412539179394467)
          ·
            refine ⟨116415869310618808769091701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77610579540412539179394467 116415869310618808769091701)
            ·
              refine ⟨10913987747870513322102347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116415869310618808769091701 10913987747870513322102347)
              ·
                refine ⟨16370981621805769983153521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10913987747870513322102347 16370981621805769983153521)
                ·
                  refine ⟨12278236216354327487365141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16370981621805769983153521 12278236216354327487365141)
                  ·
                    refine ⟨575542322641609100970241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12278236216354327487365141 575542322641609100970241)
                    ·
                      rfl

theorem cell22_1681297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_1681297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681297 prefixEnd_1681297 := by exact prefixLift 1681297
  have htrace : WordTrace (prefixWord ++ tailWord_1681297) baseStart_1681297 baseEnd_1681297 := by
    simpa [prefixWord, tailWord_1681297, baseEnd_1681297] using wordTrace_append hprefix tailTrace_1681297
  have hstable : (prefixWord ++ tailWord_1681297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681297).length < 2 ^ (prefixWord ++ tailWord_1681297).sum := by decide
  have hdescent : baseEnd_1681297 < baseStart_1681297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681312 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 9]
def baseStart_1681312 : Nat := 118140960795 + 1681312 * 2 ^ 59
def prefixEnd_1681312 : Nat := 4983230072969 + 3 ^ 40 * 1681312 * 2
def baseEnd_1681312 : Nat := 191849152482718020615065

theorem tailTrace_1681312 : CollatzResearch.WordTrace tailWord_1681312 prefixEnd_1681312 191849152482718020615065 := by
  unfold tailWord_1681312
  simp only [CollatzResearch.WordTrace]
  refine ⟨30661243242450622036955095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40881657656600829382606793 30661243242450622036955095)
  ·
    refine ⟨45991864863675933055432643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30661243242450622036955095 45991864863675933055432643)
    ·
      refine ⟨68987797295513899583148965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45991864863675933055432643 68987797295513899583148965)
      ·
        refine ⟨12935211992908856171840431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68987797295513899583148965 12935211992908856171840431)
        ·
          refine ⟨19402817989363284257760647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12935211992908856171840431 19402817989363284257760647)
          ·
            refine ⟨29104226984044926386640971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19402817989363284257760647 29104226984044926386640971)
            ·
              refine ⟨43656340476067389579961457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29104226984044926386640971 43656340476067389579961457)
              ·
                refine ⟨32742255357050542184971093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43656340476067389579961457 32742255357050542184971093)
                ·
                  refine ⟨191849152482718020615065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32742255357050542184971093 191849152482718020615065)
                  ·
                    rfl

theorem cell22_1681312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_1681312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681312 prefixEnd_1681312 := by exact prefixLift 1681312
  have htrace : WordTrace (prefixWord ++ tailWord_1681312) baseStart_1681312 baseEnd_1681312 := by
    simpa [prefixWord, tailWord_1681312, baseEnd_1681312] using wordTrace_append hprefix tailTrace_1681312
  have hstable : (prefixWord ++ tailWord_1681312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681312).length < 2 ^ (prefixWord ++ tailWord_1681312).sum := by decide
  have hdescent : baseEnd_1681312 < baseStart_1681312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681316 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_1681316 : Nat := 118140960795 + 1681316 * 2 ^ 59
def prefixEnd_1681316 : Nat := 4983230072969 + 3 ^ 40 * 1681316 * 2
def baseEnd_1681316 : Nat := 575548826729899384745183

theorem tailTrace_1681316 : CollatzResearch.WordTrace tailWord_1681316 prefixEnd_1681316 575548826729899384745183 := by
  unfold tailWord_1681316
  simp only [CollatzResearch.WordTrace]
  refine ⟨30661316188443376378527901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40881754917924501838037201 30661316188443376378527901)
  ·
    refine ⟨11497993570666266141947963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30661316188443376378527901 11497993570666266141947963)
    ·
      refine ⟨17246990355999399212921945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11497993570666266141947963 17246990355999399212921945)
      ·
        refine ⟨12935242766999549409691459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17246990355999399212921945 12935242766999549409691459)
        ·
          refine ⟨19402864150499324114537189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12935242766999549409691459 19402864150499324114537189)
          ·
            refine ⟨3638037028218623271475723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19402864150499324114537189 3638037028218623271475723)
            ·
              refine ⟨5457055542327934907213585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638037028218623271475723 5457055542327934907213585)
              ·
                refine ⟨4092791656745951180410189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5457055542327934907213585 4092791656745951180410189)
                ·
                  refine ⟨1534796871279731692653821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4092791656745951180410189 1534796871279731692653821)
                  ·
                    refine ⟨575548826729899384745183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1534796871279731692653821 575548826729899384745183)
                    ·
                      rfl

theorem cell22_1681316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_1681316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681316 prefixEnd_1681316 := by exact prefixLift 1681316
  have htrace : WordTrace (prefixWord ++ tailWord_1681316) baseStart_1681316 baseEnd_1681316 := by
    simpa [prefixWord, tailWord_1681316, baseEnd_1681316] using wordTrace_append hprefix tailTrace_1681316
  have hstable : (prefixWord ++ tailWord_1681316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681316).length < 2 ^ (prefixWord ++ tailWord_1681316).sum := by decide
  have hdescent : baseEnd_1681316 < baseStart_1681316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681320 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1681320 : Nat := 118140960795 + 1681320 * 2 ^ 59
def prefixEnd_1681320 : Nat := 4983230072969 + 3 ^ 40 * 1681320 * 2
def baseEnd_1681320 : Nat := 575550196011644707645171

theorem tailTrace_1681320 : CollatzResearch.WordTrace tailWord_1681320 prefixEnd_1681320 575550196011644707645171 := by
  unfold tailWord_1681320
  simp only [CollatzResearch.WordTrace]
  refine ⟨30661389134436130720100707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40881852179248174293467609 30661389134436130720100707)
  ·
    refine ⟨45992083701654196080151061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30661389134436130720100707 45992083701654196080151061)
    ·
      refine ⟨2155878923515040441257081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45992083701654196080151061 2155878923515040441257081)
      ·
        refine ⟨1616909192636280330942811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2155878923515040441257081 1616909192636280330942811)
        ·
          refine ⟨2425363788954420496414217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616909192636280330942811 2425363788954420496414217)
          ·
            refine ⟨1819022841715815372310663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425363788954420496414217 1819022841715815372310663)
            ·
              refine ⟨2728534262573723058465995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819022841715815372310663 2728534262573723058465995)
              ·
                refine ⟨4092801393860584587698993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728534262573723058465995 4092801393860584587698993)
                ·
                  refine ⟨3069601045395438440774245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4092801393860584587698993 3069601045395438440774245)
                  ·
                    refine ⟨575550196011644707645171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3069601045395438440774245 575550196011644707645171)
                    ·
                      rfl

theorem cell22_1681320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1681320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681320 prefixEnd_1681320 := by exact prefixLift 1681320
  have htrace : WordTrace (prefixWord ++ tailWord_1681320) baseStart_1681320 baseEnd_1681320 := by
    simpa [prefixWord, tailWord_1681320, baseEnd_1681320] using wordTrace_append hprefix tailTrace_1681320
  have hstable : (prefixWord ++ tailWord_1681320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681320).length < 2 ^ (prefixWord ++ tailWord_1681320).sum := by decide
  have hdescent : baseEnd_1681320 < baseStart_1681320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681327 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 1, 7]
def baseStart_1681327 : Nat := 118140960795 + 1681327 * 2 ^ 59
def prefixEnd_1681327 : Nat := 4983230072969 + 3 ^ 40 * 1681327 * 2
def baseEnd_1681327 : Nat := 575552592254699022720149

theorem tailTrace_1681327 : CollatzResearch.WordTrace tailWord_1681327 prefixEnd_1681327 575552592254699022720149 := by
  unfold tailWord_1681327
  simp only [CollatzResearch.WordTrace]
  refine ⟨61323033579846901635706235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40882022386564601090470823 61323033579846901635706235)
  ·
    refine ⟨91984550369770352453559353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61323033579846901635706235 91984550369770352453559353)
    ·
      refine ⟨68988412777327764340169515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91984550369770352453559353 68988412777327764340169515)
      ·
        refine ⟨103482619165991646510254273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68988412777327764340169515 103482619165991646510254273)
        ·
          refine ⟨77611964374493734882690705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103482619165991646510254273 77611964374493734882690705)
          ·
            refine ⟨58208973280870301162018029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77611964374493734882690705 58208973280870301162018029)
            ·
              refine ⟨21828364980326362935756761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58208973280870301162018029 21828364980326362935756761)
              ·
                refine ⟨16371273735244772201817571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21828364980326362935756761 16371273735244772201817571)
                ·
                  refine ⟨24556910602867158302726357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16371273735244772201817571 24556910602867158302726357)
                  ·
                    refine ⟨575552592254699022720149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24556910602867158302726357 575552592254699022720149)
                    ·
                      rfl

theorem cell22_1681327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_1681327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681327 prefixEnd_1681327 := by exact prefixLift 1681327
  have htrace : WordTrace (prefixWord ++ tailWord_1681327) baseStart_1681327 baseEnd_1681327 := by
    simpa [prefixWord, tailWord_1681327, baseEnd_1681327] using wordTrace_append hprefix tailTrace_1681327
  have hstable : (prefixWord ++ tailWord_1681327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681327).length < 2 ^ (prefixWord ++ tailWord_1681327).sum := by decide
  have hdescent : baseEnd_1681327 < baseStart_1681327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681333 : List Nat := [1, 3, 3, 2, 1, 2, 1, 5, 1, 3]
def baseStart_1681333 : Nat := 118140960795 + 1681333 * 2 ^ 59
def prefixEnd_1681333 : Nat := 4983230072969 + 3 ^ 40 * 1681333 * 2
def baseEnd_1681333 : Nat := 575554646177317007070131

theorem tailTrace_1681333 : CollatzResearch.WordTrace tailWord_1681333 prefixEnd_1681333 575554646177317007070131 := by
  unfold tailWord_1681333
  simp only [CollatzResearch.WordTrace]
  refine ⟨61323252417825164660424653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40882168278550109773616435 61323252417825164660424653)
  ·
    refine ⟨22996219656684436747659245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61323252417825164660424653 22996219656684436747659245)
    ·
      refine ⟨8623582371256663780372217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22996219656684436747659245 8623582371256663780372217)
      ·
        refine ⟨6467686778442497835279163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8623582371256663780372217 6467686778442497835279163)
        ·
          refine ⟨9701530167663746752918745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6467686778442497835279163 9701530167663746752918745)
          ·
            refine ⟨7276147625747810064689059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9701530167663746752918745 7276147625747810064689059)
            ·
              refine ⟨10914221438621715097033589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7276147625747810064689059 10914221438621715097033589)
              ·
                refine ⟨1023208259870785790346899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10914221438621715097033589 1023208259870785790346899)
                ·
                  refine ⟨1534812389806178685520349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023208259870785790346899 1534812389806178685520349)
                  ·
                    refine ⟨575554646177317007070131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1534812389806178685520349 575554646177317007070131)
                    ·
                      rfl

theorem cell22_1681333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_1681333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681333 prefixEnd_1681333 := by exact prefixLift 1681333
  have htrace : WordTrace (prefixWord ++ tailWord_1681333) baseStart_1681333 baseEnd_1681333 := by
    simpa [prefixWord, tailWord_1681333, baseEnd_1681333] using wordTrace_append hprefix tailTrace_1681333
  have hstable : (prefixWord ++ tailWord_1681333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681333).length < 2 ^ (prefixWord ++ tailWord_1681333).sum := by decide
  have hdescent : baseEnd_1681333 < baseStart_1681333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681419 : List Nat := [1, 1, 1, 1, 6, 1, 4, 7]
def baseStart_1681419 : Nat := 118140960795 + 1681419 * 2 ^ 59
def prefixEnd_1681419 : Nat := 4983230072969 + 3 ^ 40 * 1681419 * 2
def baseEnd_1681419 : Nat := 63953787303871272157763

theorem tailTrace_1681419 : CollatzResearch.WordTrace tailWord_1681419 prefixEnd_1681419 63953787303871272157763 := by
  unfold tailWord_1681419
  simp only [CollatzResearch.WordTrace]
  refine ⟨61326389095513601348055311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40884259397009067565370207 61326389095513601348055311)
  ·
    refine ⟨91989583643270402022082967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61326389095513601348055311 91989583643270402022082967)
    ·
      refine ⟨137984375464905603033124451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91989583643270402022082967 137984375464905603033124451)
      ·
        refine ⟨206976563197358404549686677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137984375464905603033124451 206976563197358404549686677)
        ·
          refine ⟨9702026399876175213266563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 206976563197358404549686677 9702026399876175213266563)
          ·
            refine ⟨14553039599814262819899845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9702026399876175213266563 14553039599814262819899845)
            ·
              refine ⟨2728694924965174278731221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14553039599814262819899845 2728694924965174278731221)
              ·
                refine ⟨63953787303871272157763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2728694924965174278731221 63953787303871272157763)
                ·
                  rfl

theorem cell22_1681419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 7].length) (baseStart_1681419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681419 prefixEnd_1681419 := by exact prefixLift 1681419
  have htrace : WordTrace (prefixWord ++ tailWord_1681419) baseStart_1681419 baseEnd_1681419 := by
    simpa [prefixWord, tailWord_1681419, baseEnd_1681419] using wordTrace_append hprefix tailTrace_1681419
  have hstable : (prefixWord ++ tailWord_1681419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681419).length < 2 ^ (prefixWord ++ tailWord_1681419).sum := by decide
  have hdescent : baseEnd_1681419 < baseStart_1681419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681470 : List Nat := [4, 2, 1, 3, 3, 1, 1, 7]
def baseStart_1681470 : Nat := 118140960795 + 1681470 * 2 ^ 59
def prefixEnd_1681470 : Nat := 4983230072969 + 3 ^ 40 * 1681470 * 2
def baseEnd_1681470 : Nat := 63955727119677146266079

theorem tailTrace_1681470 : CollatzResearch.WordTrace tailWord_1681470 prefixEnd_1681470 63955727119677146266079 := by
  unfold tailWord_1681470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7666031152291104632270233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40885499478885891372107909 7666031152291104632270233)
  ·
    refine ⟨5749523364218328474202675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7666031152291104632270233 5749523364218328474202675)
    ·
      refine ⟨8624285046327492711304013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5749523364218328474202675 8624285046327492711304013)
      ·
        refine ⟨3234106892372809766739005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8624285046327492711304013 3234106892372809766739005)
        ·
          refine ⟨1212790084639803662527127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3234106892372809766739005 1212790084639803662527127)
          ·
            refine ⟨1819185126959705493790691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212790084639803662527127 1819185126959705493790691)
            ·
              refine ⟨2728777690439558240686037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819185126959705493790691 2728777690439558240686037)
              ·
                refine ⟨63955727119677146266079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2728777690439558240686037 63955727119677146266079)
                ·
                  rfl

theorem cell22_1681470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_1681470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681470 prefixEnd_1681470 := by exact prefixLift 1681470
  have htrace : WordTrace (prefixWord ++ tailWord_1681470) baseStart_1681470 baseEnd_1681470 := by
    simpa [prefixWord, tailWord_1681470, baseEnd_1681470] using wordTrace_append hprefix tailTrace_1681470
  have hstable : (prefixWord ++ tailWord_1681470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681470).length < 2 ^ (prefixWord ++ tailWord_1681470).sum := by decide
  have hdescent : baseEnd_1681470 < baseStart_1681470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681631 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 2, 5]
def baseStart_1681631 : Nat := 118140960795 + 1681631 * 2 ^ 59
def prefixEnd_1681631 : Nat := 4983230072969 + 3 ^ 40 * 1681631 * 2
def baseEnd_1681631 : Nat := 575656657667343563119217

theorem tailTrace_1681631 : CollatzResearch.WordTrace tailWord_1681631 prefixEnd_1681631 575656657667343563119217 := by
  unfold tailWord_1681631
  simp only [CollatzResearch.WordTrace]
  refine ⟨61334121370745561554772747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40889414247163707703181831 61334121370745561554772747)
  ·
    refine ⟨92001182056118342332159121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61334121370745561554772747 92001182056118342332159121)
    ·
      refine ⟨69000886542088756749119341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92001182056118342332159121 69000886542088756749119341)
      ·
        refine ⟨25875332453283283780919753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69000886542088756749119341 25875332453283283780919753)
        ·
          refine ⟨19406499339962462835689815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25875332453283283780919753 19406499339962462835689815)
          ·
            refine ⟨29109749009943694253534723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19406499339962462835689815 29109749009943694253534723)
            ·
              refine ⟨43664623514915541380302085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29109749009943694253534723 43664623514915541380302085)
              ·
                refine ⟨8187116909046664008806641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43664623514915541380302085 8187116909046664008806641)
                ·
                  refine ⟨6140337681784998006604981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8187116909046664008806641 6140337681784998006604981)
                  ·
                    refine ⟨575656657667343563119217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6140337681784998006604981 575656657667343563119217)
                    ·
                      rfl

theorem cell22_1681631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_1681631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681631 prefixEnd_1681631 := by exact prefixLift 1681631
  have htrace : WordTrace (prefixWord ++ tailWord_1681631) baseStart_1681631 baseEnd_1681631 := by
    simpa [prefixWord, tailWord_1681631, baseEnd_1681631] using wordTrace_append hprefix tailTrace_1681631
  have hstable : (prefixWord ++ tailWord_1681631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681631).length < 2 ^ (prefixWord ++ tailWord_1681631).sum := by decide
  have hdescent : baseEnd_1681631 < baseStart_1681631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681633 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 5]
def baseStart_1681633 : Nat := 118140960795 + 1681633 * 2 ^ 59
def prefixEnd_1681633 : Nat := 4983230072969 + 3 ^ 40 * 1681633 * 2
def baseEnd_1681633 : Nat := 191885780769405408189737

theorem tailTrace_1681633 : CollatzResearch.WordTrace tailWord_1681633 prefixEnd_1681633 191885780769405408189737 := by
  unfold tailWord_1681633
  simp only [CollatzResearch.WordTrace]
  refine ⟨61334194316738315896345553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40889462877825543930897035 61334194316738315896345553)
  ·
    refine ⟨46000645737553736922259165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61334194316738315896345553 46000645737553736922259165)
    ·
      refine ⟨17250242151582651345847187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46000645737553736922259165 17250242151582651345847187)
      ·
        refine ⟨25875363227373977018770781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17250242151582651345847187 25875363227373977018770781)
        ·
          refine ⟨9703261210265241382039043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25875363227373977018770781 9703261210265241382039043)
          ·
            refine ⟨14554891815397862073058565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9703261210265241382039043 14554891815397862073058565)
            ·
              refine ⟨2729042215387099138698481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14554891815397862073058565 2729042215387099138698481)
              ·
                refine ⟨2046781661540324354023861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2729042215387099138698481 2046781661540324354023861)
                ·
                  refine ⟨191885780769405408189737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2046781661540324354023861 191885780769405408189737)
                  ·
                    rfl

theorem cell22_1681633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_1681633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681633 prefixEnd_1681633 := by exact prefixLift 1681633
  have htrace : WordTrace (prefixWord ++ tailWord_1681633) baseStart_1681633 baseEnd_1681633 := by
    simpa [prefixWord, tailWord_1681633, baseEnd_1681633] using wordTrace_append hprefix tailTrace_1681633
  have hstable : (prefixWord ++ tailWord_1681633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681633).length < 2 ^ (prefixWord ++ tailWord_1681633).sum := by decide
  have hdescent : baseEnd_1681633 < baseStart_1681633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681637 : List Nat := [1, 3, 1, 4, 2, 2, 1, 4, 1, 3]
def baseStart_1681637 : Nat := 118140960795 + 1681637 * 2 ^ 59
def prefixEnd_1681637 : Nat := 4983230072969 + 3 ^ 40 * 1681637 * 2
def baseEnd_1681637 : Nat := 575658711589961547469199

theorem tailTrace_1681637 : CollatzResearch.WordTrace tailWord_1681637 prefixEnd_1681637 575658711589961547469199 := by
  unfold tailWord_1681637
  simp only [CollatzResearch.WordTrace]
  refine ⟨61334340208723824579491165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40889560139149216386327443 61334340208723824579491165)
  ·
    refine ⟨23000377578271434217309187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61334340208723824579491165 23000377578271434217309187)
    ·
      refine ⟨34500566367407151325963781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23000377578271434217309187 34500566367407151325963781)
      ·
        refine ⟨6468856193888840873618209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34500566367407151325963781 6468856193888840873618209)
        ·
          refine ⟨4851642145416630655213657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6468856193888840873618209 4851642145416630655213657)
          ·
            refine ⟨3638731609062472991410243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4851642145416630655213657 3638731609062472991410243)
            ·
              refine ⟨5458097413593709487115365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638731609062472991410243 5458097413593709487115365)
              ·
                refine ⟨1023393265048820528834131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5458097413593709487115365 1023393265048820528834131)
                ·
                  refine ⟨1535089897573230793251197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023393265048820528834131 1535089897573230793251197)
                  ·
                    refine ⟨575658711589961547469199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1535089897573230793251197 575658711589961547469199)
                    ·
                      rfl

theorem cell22_1681637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_1681637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681637 prefixEnd_1681637 := by exact prefixLift 1681637
  have htrace : WordTrace (prefixWord ++ tailWord_1681637) baseStart_1681637 baseEnd_1681637 := by
    simpa [prefixWord, tailWord_1681637, baseEnd_1681637] using wordTrace_append hprefix tailTrace_1681637
  have hstable : (prefixWord ++ tailWord_1681637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681637).length < 2 ^ (prefixWord ++ tailWord_1681637).sum := by decide
  have hdescent : baseEnd_1681637 < baseStart_1681637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681663 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 1, 4]
def baseStart_1681663 : Nat := 118140960795 + 1681663 * 2 ^ 59
def prefixEnd_1681663 : Nat := 4983230072969 + 3 ^ 40 * 1681663 * 2
def baseEnd_1681663 : Nat := 575667611921306146319119

theorem tailTrace_1681663 : CollatzResearch.WordTrace tailWord_1681663 prefixEnd_1681663 575667611921306146319119 := by
  unfold tailWord_1681663
  simp only [CollatzResearch.WordTrace]
  refine ⟨61335288506629631019937643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40890192337753087346625095 61335288506629631019937643)
  ·
    refine ⟨92002932759944446529906465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61335288506629631019937643 92002932759944446529906465)
    ·
      refine ⟨69002199569958334897429849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92002932759944446529906465 69002199569958334897429849)
      ·
        refine ⟨51751649677468751173072387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69002199569958334897429849 51751649677468751173072387)
        ·
          refine ⟨77627474516203126759608581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51751649677468751173072387 77627474516203126759608581)
          ·
            refine ⟨14555151471788086267426609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77627474516203126759608581 14555151471788086267426609)
            ·
              refine ⟨10916363603841064700569957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14555151471788086267426609 10916363603841064700569957)
              ·
                refine ⟨2046818175720199631356867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10916363603841064700569957 2046818175720199631356867)
                ·
                  refine ⟨3070227263580299447035301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046818175720199631356867 3070227263580299447035301)
                  ·
                    refine ⟨575667611921306146319119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3070227263580299447035301 575667611921306146319119)
                    ·
                      rfl

theorem cell22_1681663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_1681663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681663 prefixEnd_1681663 := by exact prefixLift 1681663
  have htrace : WordTrace (prefixWord ++ tailWord_1681663) baseStart_1681663 baseEnd_1681663 := by
    simpa [prefixWord, tailWord_1681663, baseEnd_1681663] using wordTrace_append hprefix tailTrace_1681663
  have hstable : (prefixWord ++ tailWord_1681663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681663).length < 2 ^ (prefixWord ++ tailWord_1681663).sum := by decide
  have hdescent : baseEnd_1681663 < baseStart_1681663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681695 : List Nat := [1, 1, 2, 4, 3, 1, 2, 4, 4]
def baseStart_1681695 : Nat := 118140960795 + 1681695 * 2 ^ 59
def prefixEnd_1681695 : Nat := 4983230072969 + 3 ^ 40 * 1681695 * 2
def baseEnd_1681695 : Nat := 191892855391756243173007

theorem tailTrace_1681695 : CollatzResearch.WordTrace tailWord_1681695 prefixEnd_1681695 191892855391756243173007 := by
  unfold tailWord_1681695
  simp only [CollatzResearch.WordTrace]
  refine ⟨61336455642513700485102539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40890970428342466990068359 61336455642513700485102539)
  ·
    refine ⟨92004683463770550727653809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61336455642513700485102539 92004683463770550727653809)
    ·
      refine ⟨69003512597827913045740357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92004683463770550727653809 69003512597827913045740357)
      ·
        refine ⟨12938158612092733696076317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69003512597827913045740357 12938158612092733696076317)
        ·
          refine ⟨4851809479534775136028619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12938158612092733696076317 4851809479534775136028619)
          ·
            refine ⟨7277714219302162704042929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4851809479534775136028619 7277714219302162704042929)
            ·
              refine ⟨5458285664476622028032197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7277714219302162704042929 5458285664476622028032197)
              ·
                refine ⟨1023428562089366630256037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5458285664476622028032197 1023428562089366630256037)
                ·
                  refine ⟨191892855391756243173007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1023428562089366630256037 191892855391756243173007)
                  ·
                    rfl

theorem cell22_1681695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 4].length) (baseStart_1681695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681695 prefixEnd_1681695 := by exact prefixLift 1681695
  have htrace : WordTrace (prefixWord ++ tailWord_1681695) baseStart_1681695 baseEnd_1681695 := by
    simpa [prefixWord, tailWord_1681695, baseEnd_1681695] using wordTrace_append hprefix tailTrace_1681695
  have hstable : (prefixWord ++ tailWord_1681695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681695).length < 2 ^ (prefixWord ++ tailWord_1681695).sum := by decide
  have hdescent : baseEnd_1681695 < baseStart_1681695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681729 : List Nat := [1, 2, 5, 2, 2, 2, 1, 3, 4]
def baseStart_1681729 : Nat := 118140960795 + 1681729 * 2 ^ 59
def prefixEnd_1681729 : Nat := 4983230072969 + 3 ^ 40 * 1681729 * 2
def baseEnd_1681729 : Nat := 191896735023367991389639

theorem tailTrace_1681729 : CollatzResearch.WordTrace tailWord_1681729 prefixEnd_1681729 191896735023367991389639 := by
  unfold tailWord_1681729
  simp only [CollatzResearch.WordTrace]
  refine ⟨61337695724390524291840241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40891797149593682861226827 61337695724390524291840241)
  ·
    refine ⟨46003271793292893218880181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61337695724390524291840241 46003271793292893218880181)
    ·
      refine ⟨4312806730621208739270017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46003271793292893218880181 4312806730621208739270017)
      ·
        refine ⟨3234605047965906554452513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4312806730621208739270017 3234605047965906554452513)
        ·
          refine ⟨2425953785974429915839385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3234605047965906554452513 2425953785974429915839385)
          ·
            refine ⟨1819465339480822436879539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425953785974429915839385 1819465339480822436879539)
            ·
              refine ⟨2729198009221233655319309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819465339480822436879539 2729198009221233655319309)
              ·
                refine ⟨1023449253457962620744741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2729198009221233655319309 1023449253457962620744741)
                ·
                  refine ⟨191896735023367991389639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1023449253457962620744741 191896735023367991389639)
                  ·
                    rfl

theorem cell22_1681729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 4].length) (baseStart_1681729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681729 prefixEnd_1681729 := by exact prefixLift 1681729
  have htrace : WordTrace (prefixWord ++ tailWord_1681729) baseStart_1681729 baseEnd_1681729 := by
    simpa [prefixWord, tailWord_1681729, baseEnd_1681729] using wordTrace_append hprefix tailTrace_1681729
  have hstable : (prefixWord ++ tailWord_1681729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681729).length < 2 ^ (prefixWord ++ tailWord_1681729).sum := by decide
  have hdescent : baseEnd_1681729 < baseStart_1681729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681806 : List Nat := [4, 1, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_1681806 : Nat := 118140960795 + 1681806 * 2 ^ 59
def prefixEnd_1681806 : Nat := 4983230072969 + 3 ^ 40 * 1681806 * 2
def baseEnd_1681806 : Nat := 575716563743701439993681

theorem tailTrace_1681806 : CollatzResearch.WordTrace tailWord_1681806 prefixEnd_1681806 575716563743701439993681 := by
  unfold tailWord_1681806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7667563018138945805299159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40893669430074377628262181 7667563018138945805299159)
  ·
    refine ⟨11501344527208418707948739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7667563018138945805299159 11501344527208418707948739)
    ·
      refine ⟨17252016790812628061923109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11501344527208418707948739 17252016790812628061923109)
      ·
        refine ⟨3234753148277367761610583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17252016790812628061923109 3234753148277367761610583)
        ·
          refine ⟨4852129722416051642415875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234753148277367761610583 4852129722416051642415875)
          ·
            refine ⟨7278194583624077463623813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852129722416051642415875 7278194583624077463623813)
            ·
              refine ⟨1364661484429514524429465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7278194583624077463623813 1364661484429514524429465)
              ·
                refine ⟨1023496113322135893322099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364661484429514524429465 1023496113322135893322099)
                ·
                  refine ⟨1535244169983203839983149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023496113322135893322099 1535244169983203839983149)
                  ·
                    refine ⟨575716563743701439993681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1535244169983203839983149 575716563743701439993681)
                    ·
                      rfl

theorem cell22_1681806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_1681806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681806 prefixEnd_1681806 := by exact prefixLift 1681806
  have htrace : WordTrace (prefixWord ++ tailWord_1681806) baseStart_1681806 baseEnd_1681806 := by
    simpa [prefixWord, tailWord_1681806, baseEnd_1681806] using wordTrace_append hprefix tailTrace_1681806
  have hstable : (prefixWord ++ tailWord_1681806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681806).length < 2 ^ (prefixWord ++ tailWord_1681806).sum := by decide
  have hdescent : baseEnd_1681806 < baseStart_1681806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681813 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 6]
def baseStart_1681813 : Nat := 118140960795 + 1681813 * 2 ^ 59
def prefixEnd_1681813 : Nat := 4983230072969 + 3 ^ 40 * 1681813 * 2
def baseEnd_1681813 : Nat := 191906319995585251689553

theorem tailTrace_1681813 : CollatzResearch.WordTrace tailWord_1681813 prefixEnd_1681813 191906319995585251689553 := by
  unfold tailWord_1681813
  simp only [CollatzResearch.WordTrace]
  refine ⟨61340759456086206637898093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40893839637390804425265395 61340759456086206637898093)
  ·
    refine ⟨23002784796032327489211785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61340759456086206637898093 23002784796032327489211785)
    ·
      refine ⟨17252088597024245616908839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23002784796032327489211785 17252088597024245616908839)
      ·
        refine ⟨25878132895536368425363259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17252088597024245616908839 25878132895536368425363259)
        ·
          refine ⟨38817199343304552638044889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25878132895536368425363259 38817199343304552638044889)
          ·
            refine ⟨29112899507478414478533667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38817199343304552638044889 29112899507478414478533667)
            ·
              refine ⟨43669349261217621717800501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29112899507478414478533667 43669349261217621717800501)
              ·
                refine ⟨4094001493239152036043797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43669349261217621717800501 4094001493239152036043797)
                ·
                  refine ⟨191906319995585251689553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4094001493239152036043797 191906319995585251689553)
                  ·
                    rfl

theorem cell22_1681813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_1681813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681813 prefixEnd_1681813 := by exact prefixLift 1681813
  have htrace : WordTrace (prefixWord ++ tailWord_1681813) baseStart_1681813 baseEnd_1681813 := by
    simpa [prefixWord, tailWord_1681813, baseEnd_1681813] using wordTrace_append hprefix tailTrace_1681813
  have hstable : (prefixWord ++ tailWord_1681813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681813).length < 2 ^ (prefixWord ++ tailWord_1681813).sum := by decide
  have hdescent : baseEnd_1681813 < baseStart_1681813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681832 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1681832 : Nat := 118140960795 + 1681832 * 2 ^ 59
def prefixEnd_1681832 : Nat := 4983230072969 + 3 ^ 40 * 1681832 * 2
def baseEnd_1681832 : Nat := 575725464075046038843601

theorem tailTrace_1681832 : CollatzResearch.WordTrace tailWord_1681832 prefixEnd_1681832 575725464075046038843601 := by
  unfold tailWord_1681832
  simp only [CollatzResearch.WordTrace]
  refine ⟨30670726221508686441419875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40894301628678248588559833 30670726221508686441419875)
  ·
    refine ⟨46006089332263029662129813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30670726221508686441419875 46006089332263029662129813)
    ·
      refine ⟨2156535437449829515412335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46006089332263029662129813 2156535437449829515412335)
      ·
        refine ⟨3234803156174744273118503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156535437449829515412335 3234803156174744273118503)
        ·
          refine ⟨4852204734262116409677755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234803156174744273118503 4852204734262116409677755)
          ·
            refine ⟨7278307101393174614516633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852204734262116409677755 7278307101393174614516633)
            ·
              refine ⟨5458730326044880960887475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7278307101393174614516633 5458730326044880960887475)
              ·
                refine ⟨8188095489067321441331213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5458730326044880960887475 8188095489067321441331213)
                ·
                  refine ⟨3070535808400245540499205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8188095489067321441331213 3070535808400245540499205)
                  ·
                    refine ⟨575725464075046038843601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3070535808400245540499205 575725464075046038843601)
                    ·
                      rfl

theorem cell22_1681832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1681832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681832 prefixEnd_1681832 := by exact prefixLift 1681832
  have htrace : WordTrace (prefixWord ++ tailWord_1681832) baseStart_1681832 baseEnd_1681832 := by
    simpa [prefixWord, tailWord_1681832, baseEnd_1681832] using wordTrace_append hprefix tailTrace_1681832
  have hstable : (prefixWord ++ tailWord_1681832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681832).length < 2 ^ (prefixWord ++ tailWord_1681832).sum := by decide
  have hdescent : baseEnd_1681832 < baseStart_1681832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681847 : List Nat := [1, 1, 3, 1, 3, 4, 2, 3, 4]
def baseStart_1681847 : Nat := 118140960795 + 1681847 * 2 ^ 59
def prefixEnd_1681847 : Nat := 4983230072969 + 3 ^ 40 * 1681847 * 2
def baseEnd_1681847 : Nat := 191910199627196999906185

theorem tailTrace_1681847 : CollatzResearch.WordTrace tailWord_1681847 prefixEnd_1681847 191910199627196999906185 := by
  unfold tailWord_1681847
  simp only [CollatzResearch.WordTrace]
  refine ⟨61341999537963030444635795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40894666358642020296423863 61341999537963030444635795)
  ·
    refine ⟨92012999306944545666953693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61341999537963030444635795 92012999306944545666953693)
    ·
      refine ⟨34504874740104204625107635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92012999306944545666953693 34504874740104204625107635)
      ·
        refine ⟨51757312110156306937661453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34504874740104204625107635 51757312110156306937661453)
        ·
          refine ⟨19408992041308615101623045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51757312110156306937661453 19408992041308615101623045)
          ·
            refine ⟨3639186007745365331554321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19408992041308615101623045 3639186007745365331554321)
            ·
              refine ⟨2729389505809023998665741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3639186007745365331554321 2729389505809023998665741)
              ·
                refine ⟨1023521064678383999499653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2729389505809023998665741 1023521064678383999499653)
                ·
                  refine ⟨191910199627196999906185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1023521064678383999499653 191910199627196999906185)
                  ·
                    rfl

theorem cell22_1681847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 4].length) (baseStart_1681847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681847 prefixEnd_1681847 := by exact prefixLift 1681847
  have htrace : WordTrace (prefixWord ++ tailWord_1681847) baseStart_1681847 baseEnd_1681847 := by
    simpa [prefixWord, tailWord_1681847, baseEnd_1681847] using wordTrace_append hprefix tailTrace_1681847
  have hstable : (prefixWord ++ tailWord_1681847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681847).length < 2 ^ (prefixWord ++ tailWord_1681847).sum := by decide
  have hdescent : baseEnd_1681847 < baseStart_1681847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681849 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 1, 4]
def baseStart_1681849 : Nat := 118140960795 + 1681849 * 2 ^ 59
def prefixEnd_1681849 : Nat := 4983230072969 + 3 ^ 40 * 1681849 * 2
def baseEnd_1681849 : Nat := 575731283522463661168549

theorem tailTrace_1681849 : CollatzResearch.WordTrace tailWord_1681849 prefixEnd_1681849 575731283522463661168549 := by
  unfold tailWord_1681849
  simp only [CollatzResearch.WordTrace]
  refine ⟨61342072483955784786208601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40894714989303856524139067 61342072483955784786208601)
  ·
    refine ⟨46006554362966838589656451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61342072483955784786208601 46006554362966838589656451)
    ·
      refine ⟨69009831544450257884484677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46006554362966838589656451 69009831544450257884484677)
      ·
        refine ⟨12939343414584423353340877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69009831544450257884484677 12939343414584423353340877)
        ·
          refine ⟨4852253780469158757502829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12939343414584423353340877 4852253780469158757502829)
          ·
            refine ⟨1819595167675934534063561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4852253780469158757502829 1819595167675934534063561)
            ·
              refine ⟨1364696375756950900547671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1819595167675934534063561 1364696375756950900547671)
              ·
                refine ⟨2047044563635426350821507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364696375756950900547671 2047044563635426350821507)
                ·
                  refine ⟨3070566845453139526232261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047044563635426350821507 3070566845453139526232261)
                  ·
                    refine ⟨575731283522463661168549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3070566845453139526232261 575731283522463661168549)
                    ·
                      rfl

theorem cell22_1681849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 4].length) (baseStart_1681849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681849 prefixEnd_1681849 := by exact prefixLift 1681849
  have htrace : WordTrace (prefixWord ++ tailWord_1681849) baseStart_1681849 baseEnd_1681849 := by
    simpa [prefixWord, tailWord_1681849, baseEnd_1681849] using wordTrace_append hprefix tailTrace_1681849
  have hstable : (prefixWord ++ tailWord_1681849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681849).length < 2 ^ (prefixWord ++ tailWord_1681849).sum := by decide
  have hdescent : baseEnd_1681849 < baseStart_1681849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681909 : List Nat := [1, 3, 5, 1, 3, 1, 8]
def baseStart_1681909 : Nat := 118140960795 + 1681909 * 2 ^ 59
def prefixEnd_1681909 : Nat := 4983230072969 + 3 ^ 40 * 1681909 * 2
def baseEnd_1681909 : Nat := 21324141583283092765495

theorem tailTrace_1681909 : CollatzResearch.WordTrace tailWord_1681909 prefixEnd_1681909 21324141583283092765495 := by
  unfold tailWord_1681909
  simp only [CollatzResearch.WordTrace]
  refine ⟨61344260863738415033392781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40896173909158943355595187 61344260863738415033392781)
  ·
    refine ⟨23004097823901905637522293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61344260863738415033392781 23004097823901905637522293)
    ·
      refine ⟨2156634170990803653517715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23004097823901905637522293 2156634170990803653517715)
      ·
        refine ⟨3234951256486205480276573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156634170990803653517715 3234951256486205480276573)
        ·
          refine ⟨1213106721182327055103715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3234951256486205480276573 1213106721182327055103715)
          ·
            refine ⟨1819660081773490582655573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213106721182327055103715 1819660081773490582655573)
            ·
              refine ⟨21324141583283092765495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1819660081773490582655573 21324141583283092765495)
              ·
                rfl

theorem cell22_1681909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 8].length) (baseStart_1681909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681909 prefixEnd_1681909 := by exact prefixLift 1681909
  have htrace : WordTrace (prefixWord ++ tailWord_1681909) baseStart_1681909 baseEnd_1681909 := by
    simpa [prefixWord, tailWord_1681909, baseEnd_1681909] using wordTrace_append hprefix tailTrace_1681909
  have hstable : (prefixWord ++ tailWord_1681909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681909).length < 2 ^ (prefixWord ++ tailWord_1681909).sum := by decide
  have hdescent : baseEnd_1681909 < baseStart_1681909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681924 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_1681924 : Nat := 118140960795 + 1681924 * 2 ^ 59
def prefixEnd_1681924 : Nat := 4983230072969 + 3 ^ 40 * 1681924 * 2
def baseEnd_1681924 : Nat := 575756957555188465543319

theorem tailTrace_1681924 : CollatzResearch.WordTrace tailWord_1681924 prefixEnd_1681924 575756957555188465543319 := by
  unfold tailWord_1681924
  simp only [CollatzResearch.WordTrace]
  refine ⟨30672403979342036297594413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40896538639122715063459217 30672403979342036297594413)
  ·
    refine ⟨11502151492253263611597905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30672403979342036297594413 11502151492253263611597905)
    ·
      refine ⟨8626613619189947708698429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11502151492253263611597905 8626613619189947708698429)
      ·
        refine ⟨3234980107196230390761911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8626613619189947708698429 3234980107196230390761911)
        ·
          refine ⟨4852470160794345586142867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234980107196230390761911 4852470160794345586142867)
          ·
            refine ⟨7278705241191518379214301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852470160794345586142867 7278705241191518379214301)
            ·
              refine ⟨2729514465446819392205363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7278705241191518379214301 2729514465446819392205363)
              ·
                refine ⟨4094271698170229088308045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2729514465446819392205363 4094271698170229088308045)
                ·
                  refine ⟨1535351886813835908115517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4094271698170229088308045 1535351886813835908115517)
                  ·
                    refine ⟨575756957555188465543319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1535351886813835908115517 575756957555188465543319)
                    ·
                      rfl

theorem cell22_1681924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_1681924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681924 prefixEnd_1681924 := by exact prefixLift 1681924
  have htrace : WordTrace (prefixWord ++ tailWord_1681924) baseStart_1681924 baseEnd_1681924 := by
    simpa [prefixWord, tailWord_1681924, baseEnd_1681924] using wordTrace_append hprefix tailTrace_1681924
  have hstable : (prefixWord ++ tailWord_1681924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681924).length < 2 ^ (prefixWord ++ tailWord_1681924).sum := by decide
  have hdescent : baseEnd_1681924 < baseStart_1681924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681926 : List Nat := [6, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1681926 : Nat := 118140960795 + 1681926 * 2 ^ 59
def prefixEnd_1681926 : Nat := 4983230072969 + 3 ^ 40 * 1681926 * 2
def baseEnd_1681926 : Nat := 63973071355117902999257

theorem tailTrace_1681926 : CollatzResearch.WordTrace tailWord_1681926 prefixEnd_1681926 63973071355117902999257 := by
  unfold tailWord_1681926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1917027528271150841773801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40896587269784551291174421 1917027528271150841773801)
  ·
    refine ⟨1437770646203363131330351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1917027528271150841773801 1437770646203363131330351)
    ·
      refine ⟨2156655969305044696995527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437770646203363131330351 2156655969305044696995527)
      ·
        refine ⟨3234983953957567045493291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156655969305044696995527 3234983953957567045493291)
        ·
          refine ⟨4852475930936350568239937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234983953957567045493291 4852475930936350568239937)
          ·
            refine ⟨3639356948202262926179953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4852475930936350568239937 3639356948202262926179953)
            ·
              refine ⟨2729517711151697194634965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3639356948202262926179953 2729517711151697194634965)
              ·
                refine ⟨63973071355117902999257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2729517711151697194634965 63973071355117902999257)
                ·
                  rfl

theorem cell22_1681926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1681926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681926 prefixEnd_1681926 := by exact prefixLift 1681926
  have htrace : WordTrace (prefixWord ++ tailWord_1681926) baseStart_1681926 baseEnd_1681926 := by
    simpa [prefixWord, tailWord_1681926, baseEnd_1681926] using wordTrace_append hprefix tailTrace_1681926
  have hstable : (prefixWord ++ tailWord_1681926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681926).length < 2 ^ (prefixWord ++ tailWord_1681926).sum := by decide
  have hdescent : baseEnd_1681926 < baseStart_1681926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681995 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 4, 4]
def baseStart_1681995 : Nat := 118140960795 + 1681995 * 2 ^ 59
def prefixEnd_1681995 : Nat := 4983230072969 + 3 ^ 40 * 1681995 * 2
def baseEnd_1681995 : Nat := 575781262306167947018101

theorem tailTrace_1681995 : CollatzResearch.WordTrace tailWord_1681995 prefixEnd_1681995 575781262306167947018101 := by
  unfold tailWord_1681995
  simp only [CollatzResearch.WordTrace]
  refine ⟨61347397541426851721023439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40898265027617901147348959 61347397541426851721023439)
  ·
    refine ⟨92021096312140277581535159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61347397541426851721023439 92021096312140277581535159)
    ·
      refine ⟨138031644468210416372302739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92021096312140277581535159 138031644468210416372302739)
      ·
        refine ⟨207047466702315624558454109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138031644468210416372302739 207047466702315624558454109)
        ·
          refine ⟨77642800013368359209420291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207047466702315624558454109 77642800013368359209420291)
          ·
            refine ⟨116464200020052538814130437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77642800013368359209420291 116464200020052538814130437)
            ·
              refine ⟨21837037503759851027649457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116464200020052538814130437 21837037503759851027649457)
              ·
                refine ⟨16377778127819888270737093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21837037503759851027649457 16377778127819888270737093)
                ·
                  refine ⟨3070833398966229050763205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16377778127819888270737093 3070833398966229050763205)
                  ·
                    refine ⟨575781262306167947018101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3070833398966229050763205 575781262306167947018101)
                    ·
                      rfl

theorem cell22_1681995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 4].length) (baseStart_1681995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1681995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1681995 prefixEnd_1681995 := by exact prefixLift 1681995
  have htrace : WordTrace (prefixWord ++ tailWord_1681995) baseStart_1681995 baseEnd_1681995 := by
    simpa [prefixWord, tailWord_1681995, baseEnd_1681995] using wordTrace_append hprefix tailTrace_1681995
  have hstable : (prefixWord ++ tailWord_1681995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681995).length < 2 ^ (prefixWord ++ tailWord_1681995).sum := by decide
  have hdescent : baseEnd_1681995 < baseStart_1681995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682136 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 1, 4]
def baseStart_1682136 : Nat := 118140960795 + 1682136 * 2 ^ 59
def prefixEnd_1682136 : Nat := 4983230072969 + 3 ^ 40 * 1682136 * 2
def baseEnd_1682136 : Nat := 575829529487690579242669

theorem tailTrace_1682136 : CollatzResearch.WordTrace tailWord_1682136 prefixEnd_1682136 575829529487690579242669 := by
  unfold tailWord_1682136
  simp only [CollatzResearch.WordTrace]
  refine ⟨30676270116958016400953131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40901693489277355201270841 30676270116958016400953131)
  ·
    refine ⟨46014405175437024601429697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30676270116958016400953131 46014405175437024601429697)
    ·
      refine ⟨34510803881577768451072273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46014405175437024601429697 34510803881577768451072273)
      ·
        refine ⟨25883102911183326338304205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34510803881577768451072273 25883102911183326338304205)
        ·
          refine ⟨9706163591693747376864077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25883102911183326338304205 9706163591693747376864077)
          ·
            refine ⟨3639811346885155266324029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9706163591693747376864077 3639811346885155266324029)
            ·
              refine ⟨1364929255081933224871511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3639811346885155266324029 1364929255081933224871511)
              ·
                refine ⟨2047393882622899837307267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364929255081933224871511 2047393882622899837307267)
                ·
                  refine ⟨3071090823934349755960901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047393882622899837307267 3071090823934349755960901)
                  ·
                    refine ⟨575829529487690579242669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071090823934349755960901 575829529487690579242669)
                    ·
                      rfl

theorem cell22_1682136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_1682136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682136 prefixEnd_1682136 := by exact prefixLift 1682136
  have htrace : WordTrace (prefixWord ++ tailWord_1682136) baseStart_1682136 baseEnd_1682136 := by
    simpa [prefixWord, tailWord_1682136, baseEnd_1682136] using wordTrace_append hprefix tailTrace_1682136
  have hstable : (prefixWord ++ tailWord_1682136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682136).length < 2 ^ (prefixWord ++ tailWord_1682136).sum := by decide
  have hdescent : baseEnd_1682136 < baseStart_1682136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682166 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_1682166 : Nat := 118140960795 + 1682166 * 2 ^ 59
def prefixEnd_1682166 : Nat := 4983230072969 + 3 ^ 40 * 1682166 * 2
def baseEnd_1682166 : Nat := 575839799100780500992577

theorem tailTrace_1682166 : CollatzResearch.WordTrace tailWord_1682166 prefixEnd_1682166 575839799100780500992577 := by
  unfold tailWord_1682166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3834602151487959245343647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40902422949204898616998901 3834602151487959245343647)
  ·
    refine ⟨5751903227231938868015471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3834602151487959245343647 5751903227231938868015471)
    ·
      refine ⟨8627854840847908302023207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5751903227231938868015471 8627854840847908302023207)
      ·
        refine ⟨12941782261271862453034811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8627854840847908302023207 12941782261271862453034811)
        ·
          refine ⟨19412673391907793679552217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12941782261271862453034811 19412673391907793679552217)
          ·
            refine ⟨14559505043930845259664163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19412673391907793679552217 14559505043930845259664163)
            ·
              refine ⟨21839257565896267889496245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14559505043930845259664163 21839257565896267889496245)
              ·
                refine ⟨2047430396802775114640273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21839257565896267889496245 2047430396802775114640273)
                ·
                  refine ⟨1535572797602081335980205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2047430396802775114640273 1535572797602081335980205)
                  ·
                    refine ⟨575839799100780500992577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1535572797602081335980205 575839799100780500992577)
                    ·
                      rfl

theorem cell22_1682166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_1682166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682166 prefixEnd_1682166 := by exact prefixLift 1682166
  have htrace : WordTrace (prefixWord ++ tailWord_1682166) baseStart_1682166 baseEnd_1682166 := by
    simpa [prefixWord, tailWord_1682166, baseEnd_1682166] using wordTrace_append hprefix tailTrace_1682166
  have hstable : (prefixWord ++ tailWord_1682166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682166).length < 2 ^ (prefixWord ++ tailWord_1682166).sum := by decide
  have hdescent : baseEnd_1682166 < baseStart_1682166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682230 : List Nat := [5, 1, 2, 2, 3, 1, 2, 6]
def baseStart_1682230 : Nat := 118140960795 + 1682230 * 2 ^ 59
def prefixEnd_1682230 : Nat := 4983230072969 + 3 ^ 40 * 1682230 * 2
def baseEnd_1682230 : Nat := 63984634178745074154709

theorem tailTrace_1682230 : CollatzResearch.WordTrace tailWord_1682230 prefixEnd_1682230 63984634178745074154709 := by
  unfold tailWord_1682230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3834748043473467928489259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40903979130383657903885429 3834748043473467928489259)
  ·
    refine ⟨5752122065210201892733889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3834748043473467928489259 5752122065210201892733889)
    ·
      refine ⟨4314091548907651419550417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5752122065210201892733889 4314091548907651419550417)
      ·
        refine ⟨3235568661680738564662813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4314091548907651419550417 3235568661680738564662813)
        ·
          refine ⟨1213338248130276961748555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3235568661680738564662813 1213338248130276961748555)
          ·
            refine ⟨1820007372195415442622833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213338248130276961748555 1820007372195415442622833)
            ·
              refine ⟨1365005529146561581967125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1820007372195415442622833 1365005529146561581967125)
              ·
                refine ⟨63984634178745074154709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1365005529146561581967125 63984634178745074154709)
                ·
                  rfl

theorem cell22_1682230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_1682230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682230 prefixEnd_1682230 := by exact prefixLift 1682230
  have htrace : WordTrace (prefixWord ++ tailWord_1682230) baseStart_1682230 baseEnd_1682230 := by
    simpa [prefixWord, tailWord_1682230, baseEnd_1682230] using wordTrace_append hprefix tailTrace_1682230
  have hstable : (prefixWord ++ tailWord_1682230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682230).length < 2 ^ (prefixWord ++ tailWord_1682230).sum := by decide
  have hdescent : baseEnd_1682230 < baseStart_1682230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682284 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_1682284 : Nat := 118140960795 + 1682284 * 2 ^ 59
def prefixEnd_1682284 : Nat := 4983230072969 + 3 ^ 40 * 1682284 * 2
def baseEnd_1682284 : Nat := 575880192912267526542215

theorem tailTrace_1682284 : CollatzResearch.WordTrace tailWord_1682284 prefixEnd_1682284 575880192912267526542215 := by
  unfold tailWord_1682284
  simp only [CollatzResearch.WordTrace]
  refine ⟨30678969118689927039146953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40905292158253236052195937 30678969118689927039146953)
  ·
    refine ⟨23009226839017445279360215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30678969118689927039146953 23009226839017445279360215)
    ·
      refine ⟨34513840258526167919040323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23009226839017445279360215 34513840258526167919040323)
      ·
        refine ⟨51770760387789251878560485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34513840258526167919040323 51770760387789251878560485)
        ·
          refine ⟨9707017572710484727230091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51770760387789251878560485 9707017572710484727230091)
          ·
            refine ⟨14560526359065727090845137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9707017572710484727230091 14560526359065727090845137)
            ·
              refine ⟨10920394769299295318133853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14560526359065727090845137 10920394769299295318133853)
              ·
                refine ⟨4095148038487235744300195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10920394769299295318133853 4095148038487235744300195)
                ·
                  refine ⟨6142722057730853616450293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4095148038487235744300195 6142722057730853616450293)
                  ·
                    refine ⟨575880192912267526542215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6142722057730853616450293 575880192912267526542215)
                    ·
                      rfl

theorem cell22_1682284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_1682284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682284 prefixEnd_1682284 := by exact prefixLift 1682284
  have htrace : WordTrace (prefixWord ++ tailWord_1682284) baseStart_1682284 baseEnd_1682284 := by
    simpa [prefixWord, tailWord_1682284, baseEnd_1682284] using wordTrace_append hprefix tailTrace_1682284
  have hstable : (prefixWord ++ tailWord_1682284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682284).length < 2 ^ (prefixWord ++ tailWord_1682284).sum := by decide
  have hdescent : baseEnd_1682284 < baseStart_1682284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682299 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 2, 4]
def baseStart_1682299 : Nat := 118140960795 + 1682299 * 2 ^ 59
def prefixEnd_1682299 : Nat := 4983230072969 + 3 ^ 40 * 1682299 * 2
def baseEnd_1682299 : Nat := 575885327718812487417169

theorem tailTrace_1682299 : CollatzResearch.WordTrace tailWord_1682299 prefixEnd_1682299 575885327718812487417169 := by
  unfold tailWord_1682299
  simp only [CollatzResearch.WordTrace]
  refine ⟨61358485332325511640089951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40905656888217007760059967 61358485332325511640089951)
  ·
    refine ⟨92037727998488267460134927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61358485332325511640089951 92037727998488267460134927)
    ·
      refine ⟨138056591997732401190202391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92037727998488267460134927 138056591997732401190202391)
      ·
        refine ⟨207084887996598601785303587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138056591997732401190202391 207084887996598601785303587)
        ·
          refine ⟨310627331994897902677955381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207084887996598601785303587 310627331994897902677955381)
          ·
            refine ⟨29121312374521678376058317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310627331994897902677955381 29121312374521678376058317)
            ·
              refine ⟨10920492140445629391021869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29121312374521678376058317 10920492140445629391021869)
              ·
                refine ⟨4095184552667111021633201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10920492140445629391021869 4095184552667111021633201)
                ·
                  refine ⟨3071388414500333266224901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4095184552667111021633201 3071388414500333266224901)
                  ·
                    refine ⟨575885327718812487417169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071388414500333266224901 575885327718812487417169)
                    ·
                      rfl

theorem cell22_1682299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 4].length) (baseStart_1682299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682299 prefixEnd_1682299 := by exact prefixLift 1682299
  have htrace : WordTrace (prefixWord ++ tailWord_1682299) baseStart_1682299 baseEnd_1682299 := by
    simpa [prefixWord, tailWord_1682299, baseEnd_1682299] using wordTrace_append hprefix tailTrace_1682299
  have hstable : (prefixWord ++ tailWord_1682299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682299).length < 2 ^ (prefixWord ++ tailWord_1682299).sum := by decide
  have hdescent : baseEnd_1682299 < baseStart_1682299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682314 : List Nat := [3, 1, 2, 4, 1, 11]
def baseStart_1682314 : Nat := 118140960795 + 1682314 * 2 ^ 59
def prefixEnd_1682314 : Nat := 4983230072969 + 3 ^ 40 * 1682314 * 2
def baseEnd_1682314 : Nat := 7109758796609351213483

theorem tailTrace_1682314 : CollatzResearch.WordTrace tailWord_1682314 prefixEnd_1682314 7109758796609351213483 := by
  unfold tailWord_1682314
  simp only [CollatzResearch.WordTrace]
  refine ⟨15339758106817792300471499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40906021618180779467923997 15339758106817792300471499)
  ·
    refine ⟨23009637160226688450707249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15339758106817792300471499 23009637160226688450707249)
    ·
      refine ⟨17257227870170016338030437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23009637160226688450707249 17257227870170016338030437)
      ·
        refine ⟨3235730225656878063380707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17257227870170016338030437 3235730225656878063380707)
        ·
          refine ⟨4853595338485317095071061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235730225656878063380707 4853595338485317095071061)
          ·
            refine ⟨7109758796609351213483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4853595338485317095071061 7109758796609351213483)
            ·
              rfl

theorem cell22_1682314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 11].length) (baseStart_1682314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682314 prefixEnd_1682314 := by exact prefixLift 1682314
  have htrace : WordTrace (prefixWord ++ tailWord_1682314) baseStart_1682314 baseEnd_1682314 := by
    simpa [prefixWord, tailWord_1682314, baseEnd_1682314] using wordTrace_append hprefix tailTrace_1682314
  have hstable : (prefixWord ++ tailWord_1682314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682314).length < 2 ^ (prefixWord ++ tailWord_1682314).sum := by decide
  have hdescent : baseEnd_1682314 < baseStart_1682314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682376 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 7]
def baseStart_1682376 : Nat := 118140960795 + 1682376 * 2 ^ 59
def prefixEnd_1682376 : Nat := 4983230072969 + 3 ^ 40 * 1682376 * 2
def baseEnd_1682376 : Nat := 191970562130803317747311

theorem tailTrace_1682376 : CollatzResearch.WordTrace tailWord_1682376 prefixEnd_1682376 191970562130803317747311 := by
  unfold tailWord_1682376
  simp only [CollatzResearch.WordTrace]
  refine ⟨30680646876523276895321491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40907529168697702527095321 30680646876523276895321491)
  ·
    refine ⟨46020970314784915342982237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30680646876523276895321491 46020970314784915342982237)
    ·
      refine ⟨17257863868044343253618339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46020970314784915342982237 17257863868044343253618339)
      ·
        refine ⟨25886795802066514880427509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17257863868044343253618339 25886795802066514880427509)
        ·
          refine ⟨2426887106443735770040079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25886795802066514880427509 2426887106443735770040079)
          ·
            refine ⟨3640330659665603655060119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426887106443735770040079 3640330659665603655060119)
            ·
              refine ⟨5460495989498405482590179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640330659665603655060119 5460495989498405482590179)
              ·
                refine ⟨8190743984247608223885269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5460495989498405482590179 8190743984247608223885269)
                ·
                  refine ⟨191970562130803317747311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8190743984247608223885269 191970562130803317747311)
                  ·
                    rfl

theorem cell22_1682376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_1682376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682376 prefixEnd_1682376 := by exact prefixLift 1682376
  have htrace : WordTrace (prefixWord ++ tailWord_1682376) baseStart_1682376 baseEnd_1682376 := by
    simpa [prefixWord, tailWord_1682376, baseEnd_1682376] using wordTrace_append hprefix tailTrace_1682376
  have hstable : (prefixWord ++ tailWord_1682376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682376).length < 2 ^ (prefixWord ++ tailWord_1682376).sum := by decide
  have hdescent : baseEnd_1682376 < baseStart_1682376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682393 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 5]
def baseStart_1682393 : Nat := 118140960795 + 1682393 * 2 ^ 59
def prefixEnd_1682393 : Nat := 4983230072969 + 3 ^ 40 * 1682393 * 2
def baseEnd_1682393 : Nat := 191972501946609191855627

theorem tailTrace_1682393 : CollatzResearch.WordTrace tailWord_1682393 prefixEnd_1682393 191972501946609191855627 := by
  unfold tailWord_1682393
  simp only [CollatzResearch.WordTrace]
  refine ⟨61361913793984965694011833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40907942529323310462674555 61361913793984965694011833)
  ·
    refine ⟨46021435345488724270508875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61361913793984965694011833 46021435345488724270508875)
    ·
      refine ⟨69032153018233086405763313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46021435345488724270508875 69032153018233086405763313)
      ·
        refine ⟨51774114763674814804322485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69032153018233086405763313 51774114763674814804322485)
        ·
          refine ⟨4853823259094513887905233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51774114763674814804322485 4853823259094513887905233)
          ·
            refine ⟨3640367444320885415928925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4853823259094513887905233 3640367444320885415928925)
            ·
              refine ⟨1365137791620332030973347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3640367444320885415928925 1365137791620332030973347)
              ·
                refine ⟨2047706687430498046460021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365137791620332030973347 2047706687430498046460021)
                ·
                  refine ⟨191972501946609191855627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2047706687430498046460021 191972501946609191855627)
                  ·
                    rfl

theorem cell22_1682393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 5].length) (baseStart_1682393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682393 prefixEnd_1682393 := by exact prefixLift 1682393
  have htrace : WordTrace (prefixWord ++ tailWord_1682393) baseStart_1682393 baseEnd_1682393 := by
    simpa [prefixWord, tailWord_1682393, baseEnd_1682393] using wordTrace_append hprefix tailTrace_1682393
  have hstable : (prefixWord ++ tailWord_1682393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682393).length < 2 ^ (prefixWord ++ tailWord_1682393).sum := by decide
  have hdescent : baseEnd_1682393 < baseStart_1682393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682404 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 8]
def baseStart_1682404 : Nat := 118140960795 + 1682404 * 2 ^ 59
def prefixEnd_1682404 : Nat := 4983230072969 + 3 ^ 40 * 1682404 * 2
def baseEnd_1682404 : Nat := 191973757121542404513949

theorem tailTrace_1682404 : CollatzResearch.WordTrace tailWord_1682404 prefixEnd_1682404 191973757121542404513949 := by
  unfold tailWord_1682404
  simp only [CollatzResearch.WordTrace]
  refine ⟨30681157498472557286331133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40908209997963409715108177 30681157498472557286331133)
  ·
    refine ⟨11505434061927208982374175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30681157498472557286331133 11505434061927208982374175)
    ·
      refine ⟨17258151092890813473561263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11505434061927208982374175 17258151092890813473561263)
      ·
        refine ⟨25887226639336220210341895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17258151092890813473561263 25887226639336220210341895)
        ·
          refine ⟨38830839959004330315512843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25887226639336220210341895 38830839959004330315512843)
          ·
            refine ⟨58246259938506495473269265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38830839959004330315512843 58246259938506495473269265)
            ·
              refine ⟨43684694953879871604951949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58246259938506495473269265 43684694953879871604951949)
              ·
                refine ⟨16381760607704951851856981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43684694953879871604951949 16381760607704951851856981)
                ·
                  refine ⟨191973757121542404513949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16381760607704951851856981 191973757121542404513949)
                  ·
                    rfl

theorem cell22_1682404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_1682404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682404 prefixEnd_1682404 := by exact prefixLift 1682404
  have htrace : WordTrace (prefixWord ++ tailWord_1682404) baseStart_1682404 baseEnd_1682404 := by
    simpa [prefixWord, tailWord_1682404, baseEnd_1682404] using wordTrace_append hprefix tailTrace_1682404
  have hstable : (prefixWord ++ tailWord_1682404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682404).length < 2 ^ (prefixWord ++ tailWord_1682404).sum := by decide
  have hdescent : baseEnd_1682404 < baseStart_1682404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682414 : List Nat := [4, 1, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_1682414 : Nat := 118140960795 + 1682414 * 2 ^ 59
def prefixEnd_1682414 : Nat := 4983230072969 + 3 ^ 40 * 1682414 * 2
def baseEnd_1682414 : Nat := 575924694568990520791817

theorem tailTrace_1682414 : CollatzResearch.WordTrace tailWord_1682414 prefixEnd_1682414 575924694568990520791817 := by
  unfold tailWord_1682414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670334965863610785065787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40908453151272590853684197 7670334965863610785065787)
  ·
    refine ⟨11505502448795416177598681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7670334965863610785065787 11505502448795416177598681)
    ·
      refine ⟨8629126836596562133199011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11505502448795416177598681 8629126836596562133199011)
      ·
        refine ⟨12943690254894843199798517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8629126836596562133199011 12943690254894843199798517)
        ·
          refine ⟨1213470961396391549981111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12943690254894843199798517 1213470961396391549981111)
          ·
            refine ⟨1820206442094587324971667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213470961396391549981111 1820206442094587324971667)
            ·
              refine ⟨2730309663141880987457501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820206442094587324971667 2730309663141880987457501)
              ·
                refine ⟨1023866123678205370296563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2730309663141880987457501 1023866123678205370296563)
                ·
                  refine ⟨1535799185517308055444845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023866123678205370296563 1535799185517308055444845)
                  ·
                    refine ⟨575924694568990520791817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1535799185517308055444845 575924694568990520791817)
                    ·
                      rfl

theorem cell22_1682414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_1682414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682414 prefixEnd_1682414 := by exact prefixLift 1682414
  have htrace : WordTrace (prefixWord ++ tailWord_1682414) baseStart_1682414 baseEnd_1682414 := by
    simpa [prefixWord, tailWord_1682414, baseEnd_1682414] using wordTrace_append hprefix tailTrace_1682414
  have hstable : (prefixWord ++ tailWord_1682414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682414).length < 2 ^ (prefixWord ++ tailWord_1682414).sum := by decide
  have hdescent : baseEnd_1682414 < baseStart_1682414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682466 : List Nat := [3, 3, 1, 1, 1, 3, 2, 8]
def baseStart_1682466 : Nat := 118140960795 + 1682466 * 2 ^ 59
def prefixEnd_1682466 : Nat := 4983230072969 + 3 ^ 40 * 1682466 * 2
def baseEnd_1682466 : Nat := 63993610581297746499073

theorem tailTrace_1682466 : CollatzResearch.WordTrace tailWord_1682466 prefixEnd_1682466 63993610581297746499073 := by
  unfold tailWord_1682466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15341144080680124790354813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40909717548480332774279501 15341144080680124790354813)
  ·
    refine ⟨5752929030255046796383055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15341144080680124790354813 5752929030255046796383055)
    ·
      refine ⟨8629393545382570194574583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5752929030255046796383055 8629393545382570194574583)
      ·
        refine ⟨12944090318073855291861875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8629393545382570194574583 12944090318073855291861875)
        ·
          refine ⟨19416135477110782937792813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12944090318073855291861875 19416135477110782937792813)
          ·
            refine ⟨7281050803916543601672305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19416135477110782937792813 7281050803916543601672305)
            ·
              refine ⟨5460788102937407701254229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7281050803916543601672305 5460788102937407701254229)
              ·
                refine ⟨63993610581297746499073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5460788102937407701254229 63993610581297746499073)
                ·
                  rfl

theorem cell22_1682466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_1682466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682466 prefixEnd_1682466 := by exact prefixLift 1682466
  have htrace : WordTrace (prefixWord ++ tailWord_1682466) baseStart_1682466 baseEnd_1682466 := by
    simpa [prefixWord, tailWord_1682466, baseEnd_1682466] using wordTrace_append hprefix tailTrace_1682466
  have hstable : (prefixWord ++ tailWord_1682466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682466).length < 2 ^ (prefixWord ++ tailWord_1682466).sum := by decide
  have hdescent : baseEnd_1682466 < baseStart_1682466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682468 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_1682468 : Nat := 118140960795 + 1682468 * 2 ^ 59
def prefixEnd_1682468 : Nat := 4983230072969 + 3 ^ 40 * 1682468 * 2
def baseEnd_1682468 : Nat := 575943179872552379941651

theorem tailTrace_1682468 : CollatzResearch.WordTrace tailWord_1682468 prefixEnd_1682468 575943179872552379941651 := by
  unfold tailWord_1682468
  simp only [CollatzResearch.WordTrace]
  refine ⟨30682324634356626751496029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40909766179142169001994705 30682324634356626751496029)
  ·
    refine ⟨11505871737883735031811011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30682324634356626751496029 11505871737883735031811011)
    ·
      refine ⟨17258807606825602547716517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11505871737883735031811011 17258807606825602547716517)
      ·
        refine ⟨3236026426279800477696847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17258807606825602547716517 3236026426279800477696847)
        ·
          refine ⟨4854039639419700716545271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236026426279800477696847 4854039639419700716545271)
          ·
            refine ⟨7281059459129551074817907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4854039639419700716545271 7281059459129551074817907)
            ·
              refine ⟨10921589188694326612226861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7281059459129551074817907 10921589188694326612226861)
              ·
                refine ⟨4095595945760372479585073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10921589188694326612226861 4095595945760372479585073)
                ·
                  refine ⟨3071696959320279359688805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4095595945760372479585073 3071696959320279359688805)
                  ·
                    refine ⟨575943179872552379941651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071696959320279359688805 575943179872552379941651)
                    ·
                      rfl

theorem cell22_1682468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_1682468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682468 prefixEnd_1682468 := by exact prefixLift 1682468
  have htrace : WordTrace (prefixWord ++ tailWord_1682468) baseStart_1682468 baseEnd_1682468 := by
    simpa [prefixWord, tailWord_1682468, baseEnd_1682468] using wordTrace_append hprefix tailTrace_1682468
  have hstable : (prefixWord ++ tailWord_1682468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682468).length < 2 ^ (prefixWord ++ tailWord_1682468).sum := by decide
  have hdescent : baseEnd_1682468 < baseStart_1682468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682616 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_1682616 : Nat := 118140960795 + 1682616 * 2 ^ 59
def prefixEnd_1682616 : Nat := 4983230072969 + 3 ^ 40 * 1682616 * 2
def baseEnd_1682616 : Nat := 575993843297129327241197

theorem tailTrace_1682616 : CollatzResearch.WordTrace tailWord_1682616 prefixEnd_1682616 575993843297129327241197 := by
  unfold tailWord_1682616
  simp only [CollatzResearch.WordTrace]
  refine ⟨30685023636088537389689851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40913364848118049852919801 30685023636088537389689851)
  ·
    refine ⟨46027535454132806084534777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30685023636088537389689851 46027535454132806084534777)
    ·
      refine ⟨34520651590599604563401083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46027535454132806084534777 34520651590599604563401083)
      ·
        refine ⟨51780977385899406845101625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34520651590599604563401083 51780977385899406845101625)
        ·
          refine ⟨38835733039424555133826219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51780977385899406845101625 38835733039424555133826219)
          ·
            refine ⟨58253599559136832700739329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38835733039424555133826219 58253599559136832700739329)
            ·
              refine ⟨43690199669352624525554497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58253599559136832700739329 43690199669352624525554497)
              ·
                refine ⟨32767649752014468394165873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43690199669352624525554497 32767649752014468394165873)
                ·
                  refine ⟨24575737314010851295624405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32767649752014468394165873 24575737314010851295624405)
                  ·
                    refine ⟨575993843297129327241197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24575737314010851295624405 575993843297129327241197)
                    ·
                      rfl

theorem cell22_1682616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_1682616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682616 prefixEnd_1682616 := by exact prefixLift 1682616
  have htrace : WordTrace (prefixWord ++ tailWord_1682616) baseStart_1682616 baseEnd_1682616 := by
    simpa [prefixWord, tailWord_1682616, baseEnd_1682616] using wordTrace_append hprefix tailTrace_1682616
  have hstable : (prefixWord ++ tailWord_1682616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682616).length < 2 ^ (prefixWord ++ tailWord_1682616).sum := by decide
  have hdescent : baseEnd_1682616 < baseStart_1682616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682622 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_1682622 : Nat := 118140960795 + 1682622 * 2 ^ 59
def prefixEnd_1682622 : Nat := 4983230072969 + 3 ^ 40 * 1682622 * 2
def baseEnd_1682622 : Nat := 575995897219747311591179

theorem tailTrace_1682622 : CollatzResearch.WordTrace tailWord_1682622 prefixEnd_1682622 575995897219747311591179 := by
  unfold tailWord_1682622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7671283263769417225512265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40913510740103558536065413 7671283263769417225512265)
  ·
    refine ⟨5753462447827062919134199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7671283263769417225512265 5753462447827062919134199)
    ·
      refine ⟨8630193671740594378701299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5753462447827062919134199 8630193671740594378701299)
      ·
        refine ⟨12945290507610891568051949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8630193671740594378701299 12945290507610891568051949)
        ·
          refine ⟨4854483940354084338019481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12945290507610891568051949 4854483940354084338019481)
          ·
            refine ⟨3640862955265563253514611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4854483940354084338019481 3640862955265563253514611)
            ·
              refine ⟨5461294432898344880271917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640862955265563253514611 5461294432898344880271917)
              ·
                refine ⟨2047985412336879330101969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5461294432898344880271917 2047985412336879330101969)
                ·
                  refine ⟨1535989059252659497576477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2047985412336879330101969 1535989059252659497576477)
                  ·
                    refine ⟨575995897219747311591179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1535989059252659497576477 575995897219747311591179)
                    ·
                      rfl

theorem cell22_1682622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_1682622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682622 prefixEnd_1682622 := by exact prefixLift 1682622
  have htrace : WordTrace (prefixWord ++ tailWord_1682622) baseStart_1682622 baseEnd_1682622 := by
    simpa [prefixWord, tailWord_1682622, baseEnd_1682622] using wordTrace_append hprefix tailTrace_1682622
  have hstable : (prefixWord ++ tailWord_1682622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682622).length < 2 ^ (prefixWord ++ tailWord_1682622).sum := by decide
  have hdescent : baseEnd_1682622 < baseStart_1682622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682626 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1682626 : Nat := 118140960795 + 1682626 * 2 ^ 59
def prefixEnd_1682626 : Nat := 4983230072969 + 3 ^ 40 * 1682626 * 2
def baseEnd_1682626 : Nat := 575997266501492634491167

theorem tailTrace_1682626 : CollatzResearch.WordTrace tailWord_1682626 prefixEnd_1682626 575997266501492634491167 := by
  unfold tailWord_1682626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15342603000535211621810933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40913608001427230991495821 15342603000535211621810933)
  ·
    refine ⟨1438369031300176089544775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15342603000535211621810933 1438369031300176089544775)
    ·
      refine ⟨2157553546950264134317163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1438369031300176089544775 2157553546950264134317163)
      ·
        refine ⟨3236330320425396201475745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2157553546950264134317163 3236330320425396201475745)
        ·
          refine ⟨2427247740319047151106809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3236330320425396201475745 2427247740319047151106809)
          ·
            refine ⟨1820435805239285363330107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2427247740319047151106809 1820435805239285363330107)
            ·
              refine ⟨2730653707858928044995161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820435805239285363330107 2730653707858928044995161)
              ·
                refine ⟨2047990280894196033746371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2730653707858928044995161 2047990280894196033746371)
                ·
                  refine ⟨3071985421341294050619557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047990280894196033746371 3071985421341294050619557)
                  ·
                    refine ⟨575997266501492634491167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071985421341294050619557 575997266501492634491167)
                    ·
                      rfl

theorem cell22_1682626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1682626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682626 prefixEnd_1682626 := by exact prefixLift 1682626
  have htrace : WordTrace (prefixWord ++ tailWord_1682626) baseStart_1682626 baseEnd_1682626 := by
    simpa [prefixWord, tailWord_1682626, baseEnd_1682626] using wordTrace_append hprefix tailTrace_1682626
  have hstable : (prefixWord ++ tailWord_1682626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682626).length < 2 ^ (prefixWord ++ tailWord_1682626).sum := by decide
  have hdescent : baseEnd_1682626 < baseStart_1682626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682667 : List Nat := [1, 1, 1, 1, 2, 7, 1, 4, 1, 3]
def baseStart_1682667 : Nat := 118140960795 + 1682667 * 2 ^ 59
def prefixEnd_1682667 : Nat := 4983230072969 + 3 ^ 40 * 1682667 * 2
def baseEnd_1682667 : Nat := 576011301639382194216041

theorem tailTrace_1682667 : CollatzResearch.WordTrace tailWord_1682667 prefixEnd_1682667 576011301639382194216041 := by
  unfold tailWord_1682667
  simp only [CollatzResearch.WordTrace]
  refine ⟨61371907394992310489486255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40914604929994873659657503 61371907394992310489486255)
  ·
    refine ⟨92057861092488465734229383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61371907394992310489486255 92057861092488465734229383)
    ·
      refine ⟨138086791638732698601344075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92057861092488465734229383 138086791638732698601344075)
      ·
        refine ⟨207130187458099047902016113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138086791638732698601344075 207130187458099047902016113)
        ·
          refine ⟨155347640593574285926512085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207130187458099047902016113 155347640593574285926512085)
          ·
            refine ⟨3640960326411897326402627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 155347640593574285926512085 3640960326411897326402627)
            ·
              refine ⟨5461440489617845989603941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640960326411897326402627 5461440489617845989603941)
              ·
                refine ⟨1024020091803346123050739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5461440489617845989603941 1024020091803346123050739)
                ·
                  refine ⟨1536030137705019184576109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024020091803346123050739 1536030137705019184576109)
                  ·
                    refine ⟨576011301639382194216041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536030137705019184576109 576011301639382194216041)
                    ·
                      rfl

theorem cell22_1682667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 1, 3].length) (baseStart_1682667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682667 prefixEnd_1682667 := by exact prefixLift 1682667
  have htrace : WordTrace (prefixWord ++ tailWord_1682667) baseStart_1682667 baseEnd_1682667 := by
    simpa [prefixWord, tailWord_1682667, baseEnd_1682667] using wordTrace_append hprefix tailTrace_1682667
  have hstable : (prefixWord ++ tailWord_1682667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682667).length < 2 ^ (prefixWord ++ tailWord_1682667).sum := by decide
  have hdescent : baseEnd_1682667 < baseStart_1682667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682693 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_1682693 : Nat := 118140960795 + 1682693 * 2 ^ 59
def prefixEnd_1682693 : Nat := 4983230072969 + 3 ^ 40 * 1682693 * 2
def baseEnd_1682693 : Nat := 576020201970726793065961

theorem tailTrace_1682693 : CollatzResearch.WordTrace tailWord_1682693 prefixEnd_1682693 576020201970726793065961 := by
  unfold tailWord_1682693
  simp only [CollatzResearch.WordTrace]
  refine ⟨61372855692898116929932733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40915237128598744619955155 61372855692898116929932733)
  ·
    refine ⟨23014820884836793848724775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61372855692898116929932733 23014820884836793848724775)
    ·
      refine ⟨34522231327255190773087163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23014820884836793848724775 34522231327255190773087163)
      ·
        refine ⟨51783346990882786159630745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34522231327255190773087163 51783346990882786159630745)
        ·
          refine ⟨38837510243162089619723059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51783346990882786159630745 38837510243162089619723059)
          ·
            refine ⟨58256265364743134429584589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38837510243162089619723059 58256265364743134429584589)
            ·
              refine ⟨21846099511778675411094221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58256265364743134429584589 21846099511778675411094221)
              ·
                refine ⟨8192287316917003279160333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21846099511778675411094221 8192287316917003279160333)
                ·
                  refine ⟨3072107743843876229685125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8192287316917003279160333 3072107743843876229685125)
                  ·
                    refine ⟨576020201970726793065961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3072107743843876229685125 576020201970726793065961)
                    ·
                      rfl

theorem cell22_1682693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_1682693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682693 prefixEnd_1682693 := by exact prefixLift 1682693
  have htrace : WordTrace (prefixWord ++ tailWord_1682693) baseStart_1682693 baseEnd_1682693 := by
    simpa [prefixWord, tailWord_1682693, baseEnd_1682693] using wordTrace_append hprefix tailTrace_1682693
  have hstable : (prefixWord ++ tailWord_1682693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682693).length < 2 ^ (prefixWord ++ tailWord_1682693).sum := by decide
  have hdescent : baseEnd_1682693 < baseStart_1682693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682725 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 6]
def baseStart_1682725 : Nat := 118140960795 + 1682725 * 2 ^ 59
def prefixEnd_1682725 : Nat := 4983230072969 + 3 ^ 40 * 1682725 * 2
def baseEnd_1682725 : Nat := 192010385408229792088621

theorem tailTrace_1682725 : CollatzResearch.WordTrace tailWord_1682725 prefixEnd_1682725 192010385408229792088621 := by
  unfold tailWord_1682725
  simp only [CollatzResearch.WordTrace]
  refine ⟨61374022828782186395097629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40916015219188124263398419 61374022828782186395097629)
  ·
    refine ⟨23015258560793319898161611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61374022828782186395097629 23015258560793319898161611)
    ·
      refine ⟨34522887841189979847242417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23015258560793319898161611 34522887841189979847242417)
      ·
        refine ⟨25892165880892484885431813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34522887841189979847242417 25892165880892484885431813)
        ·
          refine ⟨4854781102667340916018465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25892165880892484885431813 4854781102667340916018465)
          ·
            refine ⟨3641085827000505687013849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4854781102667340916018465 3641085827000505687013849)
            ·
              refine ⟨2730814370250379265260387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3641085827000505687013849 2730814370250379265260387)
              ·
                refine ⟨4096221555375568897890581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2730814370250379265260387 4096221555375568897890581)
                ·
                  refine ⟨192010385408229792088621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4096221555375568897890581 192010385408229792088621)
                  ·
                    rfl

theorem cell22_1682725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_1682725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682725 prefixEnd_1682725 := by exact prefixLift 1682725
  have htrace : WordTrace (prefixWord ++ tailWord_1682725) baseStart_1682725 baseEnd_1682725 := by
    simpa [prefixWord, tailWord_1682725, baseEnd_1682725] using wordTrace_append hprefix tailTrace_1682725
  have hstable : (prefixWord ++ tailWord_1682725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682725).length < 2 ^ (prefixWord ++ tailWord_1682725).sum := by decide
  have hdescent : baseEnd_1682725 < baseStart_1682725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682783 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 2, 6]
def baseStart_1682783 : Nat := 118140960795 + 1682783 * 2 ^ 59
def prefixEnd_1682783 : Nat := 4983230072969 + 3 ^ 40 * 1682783 * 2
def baseEnd_1682783 : Nat := 576051010809996558315685

theorem tailTrace_1682783 : CollatzResearch.WordTrace tailWord_1682783 prefixEnd_1682783 576051010809996558315685 := by
  unfold tailWord_1682783
  simp only [CollatzResearch.WordTrace]
  refine ⟨61376138262572062300709003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40917425508381374867139335 61376138262572062300709003)
  ·
    refine ⟨92064207393858093451063505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61376138262572062300709003 92064207393858093451063505)
    ·
      refine ⟨69048155545393570088297629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92064207393858093451063505 69048155545393570088297629)
      ·
        refine ⟨25893058329522588783111611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69048155545393570088297629 25893058329522588783111611)
        ·
          refine ⟨38839587494283883174667417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25893058329522588783111611 38839587494283883174667417)
          ·
            refine ⟨29129690620712912381000563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38839587494283883174667417 29129690620712912381000563)
            ·
              refine ⟨43694535931069368571500845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29129690620712912381000563 43694535931069368571500845)
              ·
                refine ⟨16385450974151013214312817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43694535931069368571500845 16385450974151013214312817)
                ·
                  refine ⟨12289088230613259910734613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16385450974151013214312817 12289088230613259910734613)
                  ·
                    refine ⟨576051010809996558315685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12289088230613259910734613 576051010809996558315685)
                    ·
                      rfl

theorem cell22_1682783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_1682783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682783 prefixEnd_1682783 := by exact prefixLift 1682783
  have htrace : WordTrace (prefixWord ++ tailWord_1682783) baseStart_1682783 baseEnd_1682783 := by
    simpa [prefixWord, tailWord_1682783, baseEnd_1682783] using wordTrace_append hprefix tailTrace_1682783
  have hstable : (prefixWord ++ tailWord_1682783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682783).length < 2 ^ (prefixWord ++ tailWord_1682783).sum := by decide
  have hdescent : baseEnd_1682783 < baseStart_1682783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682791 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 2, 3]
def baseStart_1682791 : Nat := 118140960795 + 1682791 * 2 ^ 59
def prefixEnd_1682791 : Nat := 4983230072969 + 3 ^ 40 * 1682791 * 2
def baseEnd_1682791 : Nat := 576053749373487204115661

theorem tailTrace_1682791 : CollatzResearch.WordTrace tailWord_1682791 prefixEnd_1682791 576053749373487204115661 := by
  unfold tailWord_1682791
  simp only [CollatzResearch.WordTrace]
  refine ⟨61376430046543079667000227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40917620031028719778000151 61376430046543079667000227)
  ·
    refine ⟨92064645069814619500500341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61376430046543079667000227 92064645069814619500500341)
    ·
      refine ⟨8631060475295120578171907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92064645069814619500500341 8631060475295120578171907)
      ·
        refine ⟨12946590712942680867257861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8631060475295120578171907 12946590712942680867257861)
        ·
          refine ⟨2427485758676752662610849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12946590712942680867257861 2427485758676752662610849)
          ·
            refine ⟨1820614319007564496958137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2427485758676752662610849 1820614319007564496958137)
            ·
              refine ⟨1365460739255673372718603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1820614319007564496958137 1365460739255673372718603)
              ·
                refine ⟨2048191108883510059077905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365460739255673372718603 2048191108883510059077905)
                ·
                  refine ⟨1536143331662632544308429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2048191108883510059077905 1536143331662632544308429)
                  ·
                    refine ⟨576053749373487204115661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536143331662632544308429 576053749373487204115661)
                    ·
                      rfl

theorem cell22_1682791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_1682791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682791 prefixEnd_1682791 := by exact prefixLift 1682791
  have htrace : WordTrace (prefixWord ++ tailWord_1682791) baseStart_1682791 baseEnd_1682791 := by
    simpa [prefixWord, tailWord_1682791, baseEnd_1682791] using wordTrace_append hprefix tailTrace_1682791
  have hstable : (prefixWord ++ tailWord_1682791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682791).length < 2 ^ (prefixWord ++ tailWord_1682791).sum := by decide
  have hdescent : baseEnd_1682791 < baseStart_1682791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682836 : List Nat := [2, 4, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1682836 : Nat := 118140960795 + 1682836 * 2 ^ 59
def prefixEnd_1682836 : Nat := 4983230072969 + 3 ^ 40 * 1682836 * 2
def baseEnd_1682836 : Nat := 576069153793122086740523

theorem tailTrace_1682836 : CollatzResearch.WordTrace tailWord_1682836 prefixEnd_1682836 576069153793122086740523 := by
  unfold tailWord_1682836
  simp only [CollatzResearch.WordTrace]
  refine ⟨30689035665690026176194181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40918714220920034901592241 30689035665690026176194181)
  ·
    refine ⟨5754194187316879908036409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30689035665690026176194181 5754194187316879908036409)
    ·
      refine ⟨4315645640487659931027307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5754194187316879908036409 4315645640487659931027307)
      ·
        refine ⟨6473468460731489896540961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4315645640487659931027307 6473468460731489896540961)
        ·
          refine ⟨4855101345548617422405721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6473468460731489896540961 4855101345548617422405721)
          ·
            refine ⟨3641326009161463066804291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4855101345548617422405721 3641326009161463066804291)
            ·
              refine ⟨5461989013742194600206437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641326009161463066804291 5461989013742194600206437)
              ·
                refine ⟨1024122940076661487538707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5461989013742194600206437 1024122940076661487538707)
                ·
                  refine ⟨1536184410114992231308061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024122940076661487538707 1536184410114992231308061)
                  ·
                    refine ⟨576069153793122086740523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536184410114992231308061 576069153793122086740523)
                    ·
                      rfl

theorem cell22_1682836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1682836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682836 prefixEnd_1682836 := by exact prefixLift 1682836
  have htrace : WordTrace (prefixWord ++ tailWord_1682836) baseStart_1682836 baseEnd_1682836 := by
    simpa [prefixWord, tailWord_1682836, baseEnd_1682836] using wordTrace_append hprefix tailTrace_1682836
  have hstable : (prefixWord ++ tailWord_1682836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682836).length < 2 ^ (prefixWord ++ tailWord_1682836).sum := by decide
  have hdescent : baseEnd_1682836 < baseStart_1682836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682909 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_1682909 : Nat := 118140960795 + 1682909 * 2 ^ 59
def prefixEnd_1682909 : Nat := 4983230072969 + 3 ^ 40 * 1682909 * 2
def baseEnd_1682909 : Nat := 576094143184974229665299

theorem tailTrace_1682909 : CollatzResearch.WordTrace tailWord_1682909 prefixEnd_1682909 576094143184974229665299 := by
  unfold tailWord_1682909
  simp only [CollatzResearch.WordTrace]
  refine ⟨61380733860115585819795781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40920489240077057213197187 61380733860115585819795781)
  ·
    refine ⟨11508887598771672341211709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61380733860115585819795781 11508887598771672341211709)
    ·
      refine ⟨4315832849539377127954391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11508887598771672341211709 4315832849539377127954391)
      ·
        refine ⟨6473749274309065691931587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4315832849539377127954391 6473749274309065691931587)
        ·
          refine ⟨9710623911463598537897381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473749274309065691931587 9710623911463598537897381)
          ·
            refine ⟨1820741983399424725855759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9710623911463598537897381 1820741983399424725855759)
            ·
              refine ⟨2731112975099137088783639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820741983399424725855759 2731112975099137088783639)
              ·
                refine ⟨4096669462648705633175459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731112975099137088783639 4096669462648705633175459)
                ·
                  refine ⟨6145004193973058449763189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4096669462648705633175459 6145004193973058449763189)
                  ·
                    refine ⟨576094143184974229665299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6145004193973058449763189 576094143184974229665299)
                    ·
                      rfl

theorem cell22_1682909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_1682909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682909 prefixEnd_1682909 := by exact prefixLift 1682909
  have htrace : WordTrace (prefixWord ++ tailWord_1682909) baseStart_1682909 baseEnd_1682909 := by
    simpa [prefixWord, tailWord_1682909, baseEnd_1682909] using wordTrace_append hprefix tailTrace_1682909
  have hstable : (prefixWord ++ tailWord_1682909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682909).length < 2 ^ (prefixWord ++ tailWord_1682909).sum := by decide
  have hdescent : baseEnd_1682909 < baseStart_1682909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682920 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1682920 : Nat := 118140960795 + 1682920 * 2 ^ 59
def prefixEnd_1682920 : Nat := 4983230072969 + 3 ^ 40 * 1682920 * 2
def baseEnd_1682920 : Nat := 576097908709773867640265

theorem tailTrace_1682920 : CollatzResearch.WordTrace tailWord_1682920 prefixEnd_1682920 576097908709773867640265 := by
  unfold tailWord_1682920
  simp only [CollatzResearch.WordTrace]
  refine ⟨30690567531537867349223107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40920756708717156465630809 30690567531537867349223107)
  ·
    refine ⟨46035851297306801023834661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30690567531537867349223107 46035851297306801023834661)
    ·
      refine ⟨8631722118245025191968999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46035851297306801023834661 8631722118245025191968999)
      ·
        refine ⟨12947583177367537787953499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8631722118245025191968999 12947583177367537787953499)
        ·
          refine ⟨19421374766051306681930249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12947583177367537787953499 19421374766051306681930249)
          ·
            refine ⟨14566031074538480011447687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19421374766051306681930249 14566031074538480011447687)
            ·
              refine ⟨21849046611807720017171531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14566031074538480011447687 21849046611807720017171531)
              ·
                refine ⟨32773569917711580025757297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21849046611807720017171531 32773569917711580025757297)
                ·
                  refine ⟨24580177438283685019317973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32773569917711580025757297 24580177438283685019317973)
                  ·
                    refine ⟨576097908709773867640265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24580177438283685019317973 576097908709773867640265)
                    ·
                      rfl

theorem cell22_1682920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1682920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682920 prefixEnd_1682920 := by exact prefixLift 1682920
  have htrace : WordTrace (prefixWord ++ tailWord_1682920) baseStart_1682920 baseEnd_1682920 := by
    simpa [prefixWord, tailWord_1682920, baseEnd_1682920] using wordTrace_append hprefix tailTrace_1682920
  have hstable : (prefixWord ++ tailWord_1682920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682920).length < 2 ^ (prefixWord ++ tailWord_1682920).sum := by decide
  have hdescent : baseEnd_1682920 < baseStart_1682920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682922 : List Nat := [3, 1, 3, 1, 4, 1, 1, 8]
def baseStart_1682922 : Nat := 118140960795 + 1682922 * 2 ^ 59
def prefixEnd_1682922 : Nat := 4983230072969 + 3 ^ 40 * 1682922 * 2
def baseEnd_1682922 : Nat := 64010954816738503232251

theorem tailTrace_1682922 : CollatzResearch.WordTrace tailWord_1682922 prefixEnd_1682922 64010954816738503232251 := by
  unfold tailWord_1682922
  simp only [CollatzResearch.WordTrace]
  refine ⟨15345302002267122260004755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40920805339378992693346013 15345302002267122260004755)
  ·
    refine ⟨23017953003400683390007133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15345302002267122260004755 23017953003400683390007133)
    ·
      refine ⟨8631732376275256271252675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23017953003400683390007133 8631732376275256271252675)
      ·
        refine ⟨12947598564412884406879013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8631732376275256271252675 12947598564412884406879013)
        ·
          refine ⟨2427674730827415826289815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12947598564412884406879013 2427674730827415826289815)
          ·
            refine ⟨3641512096241123739434723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427674730827415826289815 3641512096241123739434723)
            ·
              refine ⟨5462268144361685609152085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641512096241123739434723 5462268144361685609152085)
              ·
                refine ⟨64010954816738503232251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5462268144361685609152085 64010954816738503232251)
                ·
                  rfl

theorem cell22_1682922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_1682922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682922 prefixEnd_1682922 := by exact prefixLift 1682922
  have htrace : WordTrace (prefixWord ++ tailWord_1682922) baseStart_1682922 baseEnd_1682922 := by
    simpa [prefixWord, tailWord_1682922, baseEnd_1682922] using wordTrace_append hprefix tailTrace_1682922
  have hstable : (prefixWord ++ tailWord_1682922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682922).length < 2 ^ (prefixWord ++ tailWord_1682922).sum := by decide
  have hdescent : baseEnd_1682922 < baseStart_1682922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682954 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 3, 3]
def baseStart_1682954 : Nat := 118140960795 + 1682954 * 2 ^ 59
def prefixEnd_1682954 : Nat := 4983230072969 + 3 ^ 40 * 1682954 * 2
def baseEnd_1682954 : Nat := 576109547604609112290161

theorem tailTrace_1682954 : CollatzResearch.WordTrace tailWord_1682954 prefixEnd_1682954 576109547604609112290161 := by
  unfold tailWord_1682954
  simp only [CollatzResearch.WordTrace]
  refine ⟨15345593786238139626295979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40921583429968372336789277 15345593786238139626295979)
  ·
    refine ⟨23018390679357209439443969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15345593786238139626295979 23018390679357209439443969)
    ·
      refine ⟨17263793009517907079582977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23018390679357209439443969 17263793009517907079582977)
      ·
        refine ⟨12947844757138430309687233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17263793009517907079582977 12947844757138430309687233)
        ·
          refine ⟨9710883567853822732265425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12947844757138430309687233 9710883567853822732265425)
          ·
            refine ⟨7283162675890367049199069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9710883567853822732265425 7283162675890367049199069)
            ·
              refine ⟨2731186003458887643449651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7283162675890367049199069 2731186003458887643449651)
              ·
                refine ⟨4096779005188331465174477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731186003458887643449651 4096779005188331465174477)
                ·
                  refine ⟨1536292126945624299440429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4096779005188331465174477 1536292126945624299440429)
                  ·
                    refine ⟨576109547604609112290161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536292126945624299440429 576109547604609112290161)
                    ·
                      rfl

theorem cell22_1682954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_1682954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1682954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1682954 prefixEnd_1682954 := by exact prefixLift 1682954
  have htrace : WordTrace (prefixWord ++ tailWord_1682954) baseStart_1682954 baseEnd_1682954 := by
    simpa [prefixWord, tailWord_1682954, baseEnd_1682954] using wordTrace_append hprefix tailTrace_1682954
  have hstable : (prefixWord ++ tailWord_1682954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682954).length < 2 ^ (prefixWord ++ tailWord_1682954).sum := by decide
  have hdescent : baseEnd_1682954 < baseStart_1682954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683005 : List Nat := [1, 4, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_1683005 : Nat := 118140960795 + 1683005 * 2 ^ 59
def prefixEnd_1683005 : Nat := 4983230072969 + 3 ^ 40 * 1683005 * 2
def baseEnd_1683005 : Nat := 576127005946861979265005

theorem tailTrace_1683005 : CollatzResearch.WordTrace tailWord_1683005 prefixEnd_1683005 576127005946861979265005 := by
  unfold tailWord_1683005
  simp only [CollatzResearch.WordTrace]
  refine ⟨61384235267767794215290469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40922823511845196143526979 61384235267767794215290469)
  ·
    refine ⟨11509544112706461415366963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61384235267767794215290469 11509544112706461415366963)
    ·
      refine ⟨17264316169059692123050445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11509544112706461415366963 17264316169059692123050445)
      ·
        refine ⟨6474118563397384546143917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17264316169059692123050445 6474118563397384546143917)
        ·
          refine ⟨2427794461274019204803969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6474118563397384546143917 2427794461274019204803969)
          ·
            refine ⟨1820845845955514403602977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2427794461274019204803969 1820845845955514403602977)
            ·
              refine ⟨1365634384466635802702233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1820845845955514403602977 1365634384466635802702233)
              ·
                refine ⟨1024225788349976852026675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1365634384466635802702233 1024225788349976852026675)
                ·
                  refine ⟨1536338682524965278040013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024225788349976852026675 1536338682524965278040013)
                  ·
                    refine ⟨576127005946861979265005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536338682524965278040013 576127005946861979265005)
                    ·
                      rfl

theorem cell22_1683005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_1683005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683005 prefixEnd_1683005 := by exact prefixLift 1683005
  have htrace : WordTrace (prefixWord ++ tailWord_1683005) baseStart_1683005 baseEnd_1683005 := by
    simpa [prefixWord, tailWord_1683005, baseEnd_1683005] using wordTrace_append hprefix tailTrace_1683005
  have hstable : (prefixWord ++ tailWord_1683005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683005).length < 2 ^ (prefixWord ++ tailWord_1683005).sum := by decide
  have hdescent : baseEnd_1683005 < baseStart_1683005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683048 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 1, 4]
def baseStart_1683048 : Nat := 118140960795 + 1683048 * 2 ^ 59
def prefixEnd_1683048 : Nat := 4983230072969 + 3 ^ 40 * 1683048 * 2
def baseEnd_1683048 : Nat := 576141725725624200439873

theorem tailTrace_1683048 : CollatzResearch.WordTrace tailWord_1683048 prefixEnd_1683048 576141725725624200439873 := by
  unfold tailWord_1683048
  simp only [CollatzResearch.WordTrace]
  refine ⟨30692901803306006279552899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40923869071074675039403865 30692901803306006279552899)
  ·
    refine ⟨46039352704959009419329349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30692901803306006279552899 46039352704959009419329349)
    ·
      refine ⟨8632378632179814266124253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46039352704959009419329349 8632378632179814266124253)
      ·
        refine ⟨3237141987067430349796595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8632378632179814266124253 3237141987067430349796595)
        ·
          refine ⟨4855712980601145524694893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3237141987067430349796595 4855712980601145524694893)
          ·
            refine ⟨1820892367725429571760585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4855712980601145524694893 1820892367725429571760585)
            ·
              refine ⟨1365669275794072178820439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1820892367725429571760585 1365669275794072178820439)
              ·
                refine ⟨2048503913691108268230659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365669275794072178820439 2048503913691108268230659)
                ·
                  refine ⟨3072755870536662402345989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048503913691108268230659 3072755870536662402345989)
                  ·
                    refine ⟨576141725725624200439873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3072755870536662402345989 576141725725624200439873)
                    ·
                      rfl

theorem cell22_1683048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_1683048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683048 prefixEnd_1683048 := by exact prefixLift 1683048
  have htrace : WordTrace (prefixWord ++ tailWord_1683048) baseStart_1683048 baseEnd_1683048 := by
    simpa [prefixWord, tailWord_1683048, baseEnd_1683048] using wordTrace_append hprefix tailTrace_1683048
  have hstable : (prefixWord ++ tailWord_1683048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683048).length < 2 ^ (prefixWord ++ tailWord_1683048).sum := by decide
  have hdescent : baseEnd_1683048 < baseStart_1683048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683061 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1683061 : Nat := 118140960795 + 1683061 * 2 ^ 59
def prefixEnd_1683061 : Nat := 4983230072969 + 3 ^ 40 * 1683061 * 2
def baseEnd_1683061 : Nat := 576146175891296499864833

theorem tailTrace_1683061 : CollatzResearch.WordTrace tailWord_1683061 prefixEnd_1683061 576146175891296499864833 := by
  unfold tailWord_1683061
  simp only [CollatzResearch.WordTrace]
  refine ⟨61386277755564915779329037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40924185170376610519552691 61386277755564915779329037)
  ·
    refine ⟨23019854158336843417248389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61386277755564915779329037 23019854158336843417248389)
    ·
      refine ⟨4316222654688158140734073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23019854158336843417248389 4316222654688158140734073)
      ·
        refine ⟨3237166991016118605550555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4316222654688158140734073 3237166991016118605550555)
        ·
          refine ⟨4855750486524177908325833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3237166991016118605550555 4855750486524177908325833)
          ·
            refine ⟨3641812864893133431244375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4855750486524177908325833 3641812864893133431244375)
            ·
              refine ⟨5462719297339700146866563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641812864893133431244375 5462719297339700146866563)
              ·
                refine ⟨8194078946009550220299845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5462719297339700146866563 8194078946009550220299845)
                ·
                  refine ⟨1536389802376790666306221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8194078946009550220299845 1536389802376790666306221)
                  ·
                    refine ⟨576146175891296499864833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536389802376790666306221 576146175891296499864833)
                    ·
                      rfl

theorem cell22_1683061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1683061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683061 prefixEnd_1683061 := by exact prefixLift 1683061
  have htrace : WordTrace (prefixWord ++ tailWord_1683061) baseStart_1683061 baseEnd_1683061 := by
    simpa [prefixWord, tailWord_1683061, baseEnd_1683061] using wordTrace_append hprefix tailTrace_1683061
  have hstable : (prefixWord ++ tailWord_1683061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683061).length < 2 ^ (prefixWord ++ tailWord_1683061).sum := by decide
  have hdescent : baseEnd_1683061 < baseStart_1683061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683123 : List Nat := [1, 1, 1, 2, 3, 3, 5, 2, 1, 3]
def baseStart_1683123 : Nat := 118140960795 + 1683123 * 2 ^ 59
def prefixEnd_1683123 : Nat := 4983230072969 + 3 ^ 40 * 1683123 * 2
def baseEnd_1683123 : Nat := 576167399758349004814643

theorem tailTrace_1683123 : CollatzResearch.WordTrace tailWord_1683123 prefixEnd_1683123 576167399758349004814643 := by
  unfold tailWord_1683123
  simp only [CollatzResearch.WordTrace]
  refine ⟨61388539081340300368086023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40925692720893533578724015 61388539081340300368086023)
  ·
    refine ⟨92082808622010450552129035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61388539081340300368086023 92082808622010450552129035)
    ·
      refine ⟨138124212933015675828193553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92082808622010450552129035 138124212933015675828193553)
      ·
        refine ⟨103593159699761756871145165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138124212933015675828193553 103593159699761756871145165)
        ·
          refine ⟨38847434887410658826679437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103593159699761756871145165 38847434887410658826679437)
          ·
            refine ⟨14567788082778997060004789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38847434887410658826679437 14567788082778997060004789)
            ·
              refine ⟨1365730132760530974375449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14567788082778997060004789 1365730132760530974375449)
              ·
                refine ⟨1024297599570398230781587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1365730132760530974375449 1024297599570398230781587)
                ·
                  refine ⟨1536446399355597346172381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024297599570398230781587 1536446399355597346172381)
                  ·
                    refine ⟨576167399758349004814643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536446399355597346172381 576167399758349004814643)
                    ·
                      rfl

theorem cell22_1683123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 1, 3].length) (baseStart_1683123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683123 prefixEnd_1683123 := by exact prefixLift 1683123
  have htrace : WordTrace (prefixWord ++ tailWord_1683123) baseStart_1683123 baseEnd_1683123 := by
    simpa [prefixWord, tailWord_1683123, baseEnd_1683123] using wordTrace_append hprefix tailTrace_1683123
  have hstable : (prefixWord ++ tailWord_1683123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683123).length < 2 ^ (prefixWord ++ tailWord_1683123).sum := by decide
  have hdescent : baseEnd_1683123 < baseStart_1683123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683147 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 6]
def baseStart_1683147 : Nat := 118140960795 + 1683147 * 2 ^ 59
def prefixEnd_1683147 : Nat := 4983230072969 + 3 ^ 40 * 1683147 * 2
def baseEnd_1683147 : Nat := 192058538482940314071523

theorem tailTrace_1683147 : CollatzResearch.WordTrace tailWord_1683147 prefixEnd_1683147 192058538482940314071523 := by
  unfold tailWord_1683147
  simp only [CollatzResearch.WordTrace]
  refine ⟨61389414433253352466959695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40926276288835568311306463 61389414433253352466959695)
  ·
    refine ⟨92084121649880028700439543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61389414433253352466959695 92084121649880028700439543)
    ·
      refine ⟨138126182474820043050659315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92084121649880028700439543 138126182474820043050659315)
      ·
        refine ⟨207189273712230064575988973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138126182474820043050659315 207189273712230064575988973)
        ·
          refine ⟨77695977642086274215995865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207189273712230064575988973 77695977642086274215995865)
          ·
            refine ⟨58271983231564705661996899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77695977642086274215995865 58271983231564705661996899)
            ·
              refine ⟨87407974847347058492995349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58271983231564705661996899 87407974847347058492995349)
              ·
                refine ⟨4097248820969393366859157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87407974847347058492995349 4097248820969393366859157)
                ·
                  refine ⟨192058538482940314071523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4097248820969393366859157 192058538482940314071523)
                  ·
                    rfl

theorem cell22_1683147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 6].length) (baseStart_1683147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683147 prefixEnd_1683147 := by exact prefixLift 1683147
  have htrace : WordTrace (prefixWord ++ tailWord_1683147) baseStart_1683147 baseEnd_1683147 := by
    simpa [prefixWord, tailWord_1683147, baseEnd_1683147] using wordTrace_append hprefix tailTrace_1683147
  have hstable : (prefixWord ++ tailWord_1683147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683147).length < 2 ^ (prefixWord ++ tailWord_1683147).sum := by decide
  have hdescent : baseEnd_1683147 < baseStart_1683147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683177 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_1683177 : Nat := 118140960795 + 1683177 * 2 ^ 59
def prefixEnd_1683177 : Nat := 4983230072969 + 3 ^ 40 * 1683177 * 2
def baseEnd_1683177 : Nat := 576185885061910863964477

theorem tailTrace_1683177 : CollatzResearch.WordTrace tailWord_1683177 prefixEnd_1683177 576185885061910863964477 := by
  unfold tailWord_1683177
  simp only [CollatzResearch.WordTrace]
  refine ⟨61390508623144667590551785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40927005748763111727034523 61390508623144667590551785)
  ·
    refine ⟨46042881467358500692913839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61390508623144667590551785 46042881467358500692913839)
    ·
      refine ⟨69064322201037751039370759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46042881467358500692913839 69064322201037751039370759)
      ·
        refine ⟨103596483301556626559056139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69064322201037751039370759 103596483301556626559056139)
        ·
          refine ⟨155394724952334939838584209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103596483301556626559056139 155394724952334939838584209)
          ·
            refine ⟨116546043714251204878938157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155394724952334939838584209 116546043714251204878938157)
            ·
              refine ⟨43704766392844201829601809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116546043714251204878938157 43704766392844201829601809)
              ·
                refine ⟨32778574794633151372201357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43704766392844201829601809 32778574794633151372201357)
                ·
                  refine ⟨12291965547987431764575509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32778574794633151372201357 12291965547987431764575509)
                  ·
                    refine ⟨576185885061910863964477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12291965547987431764575509 576185885061910863964477)
                    ·
                      rfl

theorem cell22_1683177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_1683177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683177 prefixEnd_1683177 := by exact prefixLift 1683177
  have htrace : WordTrace (prefixWord ++ tailWord_1683177) baseStart_1683177 baseEnd_1683177 := by
    simpa [prefixWord, tailWord_1683177, baseEnd_1683177] using wordTrace_append hprefix tailTrace_1683177
  have hstable : (prefixWord ++ tailWord_1683177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683177).length < 2 ^ (prefixWord ++ tailWord_1683177).sum := by decide
  have hdescent : baseEnd_1683177 < baseStart_1683177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683179 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 4, 3]
def baseStart_1683179 : Nat := 118140960795 + 1683179 * 2 ^ 59
def prefixEnd_1683179 : Nat := 4983230072969 + 3 ^ 40 * 1683179 * 2
def baseEnd_1683179 : Nat := 576186569702783525414471

theorem tailTrace_1683179 : CollatzResearch.WordTrace tailWord_1683179 prefixEnd_1683179 576186569702783525414471 := by
  unfold tailWord_1683179
  simp only [CollatzResearch.WordTrace]
  refine ⟨61390581569137421932124591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40927054379424947954749727 61390581569137421932124591)
  ·
    refine ⟨92085872353706132898186887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61390581569137421932124591 92085872353706132898186887)
    ·
      refine ⟨138128808530559199347280331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92085872353706132898186887 138128808530559199347280331)
      ·
        refine ⟨207193212795838799020920497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138128808530559199347280331 207193212795838799020920497)
        ·
          refine ⟨155394909596879099265690373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207193212795838799020920497 155394909596879099265690373)
          ·
            refine ⟨29136545549414831112316945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155394909596879099265690373 29136545549414831112316945)
            ·
              refine ⟨21852409162061123334237709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29136545549414831112316945 21852409162061123334237709)
              ·
                refine ⟨8194653435772921250339141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21852409162061123334237709 8194653435772921250339141)
                ·
                  refine ⟨1536497519207422734438589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8194653435772921250339141 1536497519207422734438589)
                  ·
                    refine ⟨576186569702783525414471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536497519207422734438589 576186569702783525414471)
                    ·
                      rfl

theorem cell22_1683179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 3].length) (baseStart_1683179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683179 prefixEnd_1683179 := by exact prefixLift 1683179
  have htrace : WordTrace (prefixWord ++ tailWord_1683179) baseStart_1683179 baseEnd_1683179 := by
    simpa [prefixWord, tailWord_1683179, baseEnd_1683179] using wordTrace_append hprefix tailTrace_1683179
  have hstable : (prefixWord ++ tailWord_1683179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683179).length < 2 ^ (prefixWord ++ tailWord_1683179).sum := by decide
  have hdescent : baseEnd_1683179 < baseStart_1683179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683192 : List Nat := [2, 1, 2, 1, 1, 2, 2, 11]
def baseStart_1683192 : Nat := 118140960795 + 1683192 * 2 ^ 59
def prefixEnd_1683192 : Nat := 4983230072969 + 3 ^ 40 * 1683192 * 2
def baseEnd_1683192 : Nat := 64021224429828424982159

theorem tailTrace_1683192 : CollatzResearch.WordTrace tailWord_1683192 prefixEnd_1683192 64021224429828424982159 := by
  unfold tailWord_1683192
  simp only [CollatzResearch.WordTrace]
  refine ⟨30695527859045162576173915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40927370478726883434898553 30695527859045162576173915)
  ·
    refine ⟨46043291788567743864260873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30695527859045162576173915 46043291788567743864260873)
    ·
      refine ⟨34532468841425807898195655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46043291788567743864260873 34532468841425807898195655)
      ·
        refine ⟨51798703262138711847293483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34532468841425807898195655 51798703262138711847293483)
        ·
          refine ⟨77698054893208067770940225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51798703262138711847293483 77698054893208067770940225)
          ·
            refine ⟨58273541169906050828205169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77698054893208067770940225 58273541169906050828205169)
            ·
              refine ⟨43705155877429538121153877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58273541169906050828205169 43705155877429538121153877)
              ·
                refine ⟨64021224429828424982159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 43705155877429538121153877 64021224429828424982159)
                ·
                  rfl

theorem cell22_1683192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 11].length) (baseStart_1683192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683192 prefixEnd_1683192 := by exact prefixLift 1683192
  have htrace : WordTrace (prefixWord ++ tailWord_1683192) baseStart_1683192 baseEnd_1683192 := by
    simpa [prefixWord, tailWord_1683192, baseEnd_1683192] using wordTrace_append hprefix tailTrace_1683192
  have hstable : (prefixWord ++ tailWord_1683192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683192).length < 2 ^ (prefixWord ++ tailWord_1683192).sum := by decide
  have hdescent : baseEnd_1683192 < baseStart_1683192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683196 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 2, 3]
def baseStart_1683196 : Nat := 118140960795 + 1683196 * 2 ^ 59
def prefixEnd_1683196 : Nat := 4983230072969 + 3 ^ 40 * 1683196 * 2
def baseEnd_1683196 : Nat := 576192389150201147739419

theorem tailTrace_1683196 : CollatzResearch.WordTrace tailWord_1683196 prefixEnd_1683196 576192389150201147739419 := by
  unfold tailWord_1683196
  simp only [CollatzResearch.WordTrace]
  refine ⟨30695600805037916917746721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40927467740050555890328961 30695600805037916917746721)
  ·
    refine ⟨23021700603778437688310041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30695600805037916917746721 23021700603778437688310041)
    ·
      refine ⟨17266275452833828266232531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23021700603778437688310041 17266275452833828266232531)
      ·
        refine ⟨25899413179250742399348797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17266275452833828266232531 25899413179250742399348797)
        ·
          refine ⟨9712279942219028399755799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25899413179250742399348797 9712279942219028399755799)
          ·
            refine ⟨14568419913328542599633699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9712279942219028399755799 14568419913328542599633699)
            ·
              refine ⟨21852629869992813899450549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14568419913328542599633699 21852629869992813899450549)
              ·
                refine ⟨2048684050311826303073489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21852629869992813899450549 2048684050311826303073489)
                ·
                  refine ⟨1536513037733869727305117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2048684050311826303073489 1536513037733869727305117)
                  ·
                    refine ⟨576192389150201147739419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536513037733869727305117 576192389150201147739419)
                    ·
                      rfl

theorem cell22_1683196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_1683196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683196 prefixEnd_1683196 := by exact prefixLift 1683196
  have htrace : WordTrace (prefixWord ++ tailWord_1683196) baseStart_1683196 baseEnd_1683196 := by
    simpa [prefixWord, tailWord_1683196, baseEnd_1683196] using wordTrace_append hprefix tailTrace_1683196
  have hstable : (prefixWord ++ tailWord_1683196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683196).length < 2 ^ (prefixWord ++ tailWord_1683196).sum := by decide
  have hdescent : baseEnd_1683196 < baseStart_1683196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683292 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 3, 3]
def baseStart_1683292 : Nat := 118140960795 + 1683292 * 2 ^ 59
def prefixEnd_1683292 : Nat := 4983230072969 + 3 ^ 40 * 1683292 * 2
def baseEnd_1683292 : Nat := 576225251912088897339125

theorem tailTrace_1683292 : CollatzResearch.WordTrace tailWord_1683292 prefixEnd_1683292 576225251912088897339125 := by
  unfold tailWord_1683292
  simp only [CollatzResearch.WordTrace]
  refine ⟨30697351508864021115494065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40929802011818694820658753 30697351508864021115494065)
  ·
    refine ⟨23023013631648015836620549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30697351508864021115494065 23023013631648015836620549)
    ·
      refine ⟨4316815055934002969366353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23023013631648015836620549 4316815055934002969366353)
      ·
        refine ⟨3237611291950502227024765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4316815055934002969366353 3237611291950502227024765)
        ·
          refine ⟨1214104234481438335134287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3237611291950502227024765 1214104234481438335134287)
          ·
            refine ⟨1821156351722157502701431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214104234481438335134287 1821156351722157502701431)
            ·
              refine ⟨2731734527583236254052147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1821156351722157502701431 2731734527583236254052147)
              ·
                refine ⟨4097601791374854381078221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731734527583236254052147 4097601791374854381078221)
                ·
                  refine ⟨1536600671765570392904333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4097601791374854381078221 1536600671765570392904333)
                  ·
                    refine ⟨576225251912088897339125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536600671765570392904333 576225251912088897339125)
                    ·
                      rfl

theorem cell22_1683292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_1683292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683292 prefixEnd_1683292 := by exact prefixLift 1683292
  have htrace : WordTrace (prefixWord ++ tailWord_1683292) baseStart_1683292 baseEnd_1683292 := by
    simpa [prefixWord, tailWord_1683292, baseEnd_1683292] using wordTrace_append hprefix tailTrace_1683292
  have hstable : (prefixWord ++ tailWord_1683292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683292).length < 2 ^ (prefixWord ++ tailWord_1683292).sum := by decide
  have hdescent : baseEnd_1683292 < baseStart_1683292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683331 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 1, 5]
def baseStart_1683331 : Nat := 118140960795 + 1683331 * 2 ^ 59
def prefixEnd_1683331 : Nat := 4983230072969 + 3 ^ 40 * 1683331 * 2
def baseEnd_1683331 : Nat := 576238602409105795614005

theorem tailTrace_1683331 : CollatzResearch.WordTrace tailWord_1683331 prefixEnd_1683331 576238602409105795614005 := by
  unfold tailWord_1683331
  simp only [CollatzResearch.WordTrace]
  refine ⟨61396125464586751891657847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40930750309724501261105231 61396125464586751891657847)
  ·
    refine ⟨92094188196880127837486771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61396125464586751891657847 92094188196880127837486771)
    ·
      refine ⟨138141282295320191756230157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92094188196880127837486771 138141282295320191756230157)
      ·
        refine ⟨51802980860745071908586309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138141282295320191756230157 51802980860745071908586309)
        ·
          refine ⟨9713058911389700982859933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51802980860745071908586309 9713058911389700982859933)
          ·
            refine ⟨3642397091771137868572475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9713058911389700982859933 3642397091771137868572475)
            ·
              refine ⟨5463595637656706802858713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3642397091771137868572475 5463595637656706802858713)
              ·
                refine ⟨4097696728242530102144035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5463595637656706802858713 4097696728242530102144035)
                ·
                  refine ⟨6146545092363795153216053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097696728242530102144035 6146545092363795153216053)
                  ·
                    refine ⟨576238602409105795614005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6146545092363795153216053 576238602409105795614005)
                    ·
                      rfl

theorem cell22_1683331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 5].length) (baseStart_1683331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683331 prefixEnd_1683331 := by exact prefixLift 1683331
  have htrace : WordTrace (prefixWord ++ tailWord_1683331) baseStart_1683331 baseEnd_1683331 := by
    simpa [prefixWord, tailWord_1683331, baseEnd_1683331] using wordTrace_append hprefix tailTrace_1683331
  have hstable : (prefixWord ++ tailWord_1683331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683331).length < 2 ^ (prefixWord ++ tailWord_1683331).sum := by decide
  have hdescent : baseEnd_1683331 < baseStart_1683331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683335 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 1, 4]
def baseStart_1683335 : Nat := 118140960795 + 1683335 * 2 ^ 59
def prefixEnd_1683335 : Nat := 4983230072969 + 3 ^ 40 * 1683335 * 2
def baseEnd_1683335 : Nat := 576239971690851118513993

theorem tailTrace_1683335 : CollatzResearch.WordTrace tailWord_1683335 prefixEnd_1683335 576239971690851118513993 := by
  unfold tailWord_1683335
  simp only [CollatzResearch.WordTrace]
  refine ⟨61396271356572260574803459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40930847571048173716535639 61396271356572260574803459)
  ·
    refine ⟨92094407034858390862205189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61396271356572260574803459 92094407034858390862205189)
    ·
      refine ⟨17267701319035948286663473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92094407034858390862205189 17267701319035948286663473)
      ·
        refine ⟨12950775989276961214997605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17267701319035948286663473 12950775989276961214997605)
        ·
          refine ⟨2428270497989430227812051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12950775989276961214997605 2428270497989430227812051)
          ·
            refine ⟨3642405746984145341718077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428270497989430227812051 3642405746984145341718077)
            ·
              refine ⟨1365902155119054503144279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3642405746984145341718077 1365902155119054503144279)
              ·
                refine ⟨2048853232678581754716419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365902155119054503144279 2048853232678581754716419)
                ·
                  refine ⟨3073279849017872632074629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048853232678581754716419 3073279849017872632074629)
                  ·
                    refine ⟨576239971690851118513993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3073279849017872632074629 576239971690851118513993)
                    ·
                      rfl

theorem cell22_1683335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_1683335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683335 prefixEnd_1683335 := by exact prefixLift 1683335
  have htrace : WordTrace (prefixWord ++ tailWord_1683335) baseStart_1683335 baseEnd_1683335 := by
    simpa [prefixWord, tailWord_1683335, baseEnd_1683335] using wordTrace_append hprefix tailTrace_1683335
  have hstable : (prefixWord ++ tailWord_1683335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683335).length < 2 ^ (prefixWord ++ tailWord_1683335).sum := by decide
  have hdescent : baseEnd_1683335 < baseStart_1683335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683380 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1683380 : Nat := 118140960795 + 1683380 * 2 ^ 59
def prefixEnd_1683380 : Nat := 4983230072969 + 3 ^ 40 * 1683380 * 2
def baseEnd_1683380 : Nat := 576255376110486001138855

theorem tailTrace_1683380 : CollatzResearch.WordTrace tailWord_1683380 prefixEnd_1683380 576255376110486001138855 := by
  unfold tailWord_1683380
  simp only [CollatzResearch.WordTrace]
  refine ⟨30698956320704616630095797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40931941760939488840127729 30698956320704616630095797)
  ·
    refine ⟨2878027155066057809071481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30698956320704616630095797 2878027155066057809071481)
    ·
      refine ⟨2158520366299543356803611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2878027155066057809071481 2158520366299543356803611)
      ·
        refine ⟨3237780549449315035205417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2158520366299543356803611 3237780549449315035205417)
        ·
          refine ⟨2428335412086986276404063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3237780549449315035205417 2428335412086986276404063)
          ·
            refine ⟨3642503118130479414606095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428335412086986276404063 3642503118130479414606095)
            ·
              refine ⟨5463754677195719121909143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3642503118130479414606095 5463754677195719121909143)
              ·
                refine ⟨8195632015793578682863715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5463754677195719121909143 8195632015793578682863715)
                ·
                  refine ⟨12293448023690368024295573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8195632015793578682863715 12293448023690368024295573)
                  ·
                    refine ⟨576255376110486001138855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12293448023690368024295573 576255376110486001138855)
                    ·
                      rfl

theorem cell22_1683380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1683380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683380 prefixEnd_1683380 := by exact prefixLift 1683380
  have htrace : WordTrace (prefixWord ++ tailWord_1683380) baseStart_1683380 baseEnd_1683380 := by
    simpa [prefixWord, tailWord_1683380, baseEnd_1683380] using wordTrace_append hprefix tailTrace_1683380
  have hstable : (prefixWord ++ tailWord_1683380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683380).length < 2 ^ (prefixWord ++ tailWord_1683380).sum := by decide
  have hdescent : baseEnd_1683380 < baseStart_1683380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683406 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_1683406 : Nat := 118140960795 + 1683406 * 2 ^ 59
def prefixEnd_1683406 : Nat := 4983230072969 + 3 ^ 40 * 1683406 * 2
def baseEnd_1683406 : Nat := 192088092147276866662925

theorem tailTrace_1683406 : CollatzResearch.WordTrace tailWord_1683406 prefixEnd_1683406 192088092147276866662925 := by
  unfold tailWord_1683406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7674857617414379962579759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40932573959543359800425381 7674857617414379962579759)
  ·
    refine ⟨11512286426121569943869639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7674857617414379962579759 11512286426121569943869639)
    ·
      refine ⟨17268429639182354915804459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11512286426121569943869639 17268429639182354915804459)
      ·
        refine ⟨25902644458773532373706689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17268429639182354915804459 25902644458773532373706689)
        ·
          refine ⟨19426983344080149280280017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25902644458773532373706689 19426983344080149280280017)
          ·
            refine ⟨14570237508060111960210013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19426983344080149280280017 14570237508060111960210013)
            ·
              refine ⟨5463839065522541985078755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14570237508060111960210013 5463839065522541985078755)
              ·
                refine ⟨8195758598283812977618133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5463839065522541985078755 8195758598283812977618133)
                ·
                  refine ⟨192088092147276866662925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8195758598283812977618133 192088092147276866662925)
                  ·
                    rfl

theorem cell22_1683406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_1683406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683406 prefixEnd_1683406 := by exact prefixLift 1683406
  have htrace : WordTrace (prefixWord ++ tailWord_1683406) baseStart_1683406 baseEnd_1683406 := by
    simpa [prefixWord, tailWord_1683406, baseEnd_1683406] using wordTrace_append hprefix tailTrace_1683406
  have hstable : (prefixWord ++ tailWord_1683406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683406).length < 2 ^ (prefixWord ++ tailWord_1683406).sum := by decide
  have hdescent : baseEnd_1683406 < baseStart_1683406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683436 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_1683436 : Nat := 118140960795 + 1683436 * 2 ^ 59
def prefixEnd_1683436 : Nat := 4983230072969 + 3 ^ 40 * 1683436 * 2
def baseEnd_1683436 : Nat := 576274546054920521738683

theorem tailTrace_1683436 : CollatzResearch.WordTrace tailWord_1683436 prefixEnd_1683436 576274546054920521738683 := by
  unfold tailWord_1683436
  simp only [CollatzResearch.WordTrace]
  refine ⟨30699977564603177412115081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40933303419470903216153441 30699977564603177412115081)
  ·
    refine ⟨23024983173452383059086311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30699977564603177412115081 23024983173452383059086311)
    ·
      refine ⟨34537474760178574588629467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23024983173452383059086311 34537474760178574588629467)
      ·
        refine ⟨51806212140267861882944201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34537474760178574588629467 51806212140267861882944201)
        ·
          refine ⟨38854659105200896412208151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51806212140267861882944201 38854659105200896412208151)
          ·
            refine ⟨58281988657801344618312227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38854659105200896412208151 58281988657801344618312227)
            ·
              refine ⟨87422982986702016927468341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58281988657801344618312227 87422982986702016927468341)
              ·
                refine ⟨8195904655003314086950157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87422982986702016927468341 8195904655003314086950157)
                ·
                  refine ⟨3073464245626242782606309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8195904655003314086950157 3073464245626242782606309)
                  ·
                    refine ⟨576274546054920521738683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3073464245626242782606309 576274546054920521738683)
                    ·
                      rfl

theorem cell22_1683436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_1683436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683436 prefixEnd_1683436 := by exact prefixLift 1683436
  have htrace : WordTrace (prefixWord ++ tailWord_1683436) baseStart_1683436 baseEnd_1683436 := by
    simpa [prefixWord, tailWord_1683436, baseEnd_1683436] using wordTrace_append hprefix tailTrace_1683436
  have hstable : (prefixWord ++ tailWord_1683436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683436).length < 2 ^ (prefixWord ++ tailWord_1683436).sum := by decide
  have hdescent : baseEnd_1683436 < baseStart_1683436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683453 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1683453 : Nat := 118140960795 + 1683453 * 2 ^ 59
def prefixEnd_1683453 : Nat := 4983230072969 + 3 ^ 40 * 1683453 * 2
def baseEnd_1683453 : Nat := 576280365502338144063631

theorem tailTrace_1683453 : CollatzResearch.WordTrace tailWord_1683453 prefixEnd_1683453 576280365502338144063631 := by
  unfold tailWord_1683453
  simp only [CollatzResearch.WordTrace]
  refine ⟨61400575170144766727599013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40933716780096511151732675 61400575170144766727599013)
  ·
    refine ⟨11512607844402143761424815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61400575170144766727599013 11512607844402143761424815)
    ·
      refine ⟨17268911766603215642137223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11512607844402143761424815 17268911766603215642137223)
      ·
        refine ⟨25903367649904823463205835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17268911766603215642137223 25903367649904823463205835)
        ·
          refine ⟨38855051474857235194808753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25903367649904823463205835 38855051474857235194808753)
          ·
            refine ⟨29141288606142926396106565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38855051474857235194808753 29141288606142926396106565)
            ·
              refine ⟨5463991613651798699269981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29141288606142926396106565 5463991613651798699269981)
              ·
                refine ⟨2048996855119424512226243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5463991613651798699269981 2048996855119424512226243)
                ·
                  refine ⟨3073495282679136768339365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048996855119424512226243 3073495282679136768339365)
                  ·
                    refine ⟨576280365502338144063631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3073495282679136768339365 576280365502338144063631)
                    ·
                      rfl

theorem cell22_1683453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1683453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683453 prefixEnd_1683453 := by exact prefixLift 1683453
  have htrace : WordTrace (prefixWord ++ tailWord_1683453) baseStart_1683453 baseEnd_1683453 := by
    simpa [prefixWord, tailWord_1683453, baseEnd_1683453] using wordTrace_append hprefix tailTrace_1683453
  have hstable : (prefixWord ++ tailWord_1683453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683453).length < 2 ^ (prefixWord ++ tailWord_1683453).sum := by decide
  have hdescent : baseEnd_1683453 < baseStart_1683453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683481 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 6, 4]
def baseStart_1683481 : Nat := 118140960795 + 1683481 * 2 ^ 59
def prefixEnd_1683481 : Nat := 4983230072969 + 3 ^ 40 * 1683481 * 2
def baseEnd_1683481 : Nat := 576289950474555404363545

theorem tailTrace_1683481 : CollatzResearch.WordTrace tailWord_1683481 prefixEnd_1683481 576289950474555404363545 := by
  unfold tailWord_1683481
  simp only [CollatzResearch.WordTrace]
  refine ⟨61401596414043327509618297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40934397609362218339745531 61401596414043327509618297)
  ·
    refine ⟨46051197310532495632213723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61401596414043327509618297 46051197310532495632213723)
    ·
      refine ⟨69076795965798743448320585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46051197310532495632213723 69076795965798743448320585)
      ·
        refine ⟨51807596974349057586240439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69076795965798743448320585 51807596974349057586240439)
        ·
          refine ⟨77711395461523586379360659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51807596974349057586240439 77711395461523586379360659)
          ·
            refine ⟨116567093192285379569040989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77711395461523586379360659 116567093192285379569040989)
            ·
              refine ⟨43712659947107017338390371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116567093192285379569040989 43712659947107017338390371)
              ·
                refine ⟨65568989920660526007585557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43712659947107017338390371 65568989920660526007585557)
                ·
                  refine ⟨3073546402530962156605573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65568989920660526007585557 3073546402530962156605573)
                  ·
                    refine ⟨576289950474555404363545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3073546402530962156605573 576289950474555404363545)
                    ·
                      rfl

theorem cell22_1683481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_1683481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683481 prefixEnd_1683481 := by exact prefixLift 1683481
  have htrace : WordTrace (prefixWord ++ tailWord_1683481) baseStart_1683481 baseEnd_1683481 := by
    simpa [prefixWord, tailWord_1683481, baseEnd_1683481] using wordTrace_append hprefix tailTrace_1683481
  have hstable : (prefixWord ++ tailWord_1683481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683481).length < 2 ^ (prefixWord ++ tailWord_1683481).sum := by decide
  have hdescent : baseEnd_1683481 < baseStart_1683481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683513 : List Nat := [1, 2, 1, 5, 4, 9]
def baseStart_1683513 : Nat := 118140960795 + 1683513 * 2 ^ 59
def prefixEnd_1683513 : Nat := 4983230072969 + 3 ^ 40 * 1683513 * 2
def baseEnd_1683513 : Nat := 7114825984302691204487

theorem tailTrace_1683513 : CollatzResearch.WordTrace tailWord_1683513 prefixEnd_1683513 7114825984302691204487 := by
  unfold tailWord_1683513
  simp only [CollatzResearch.WordTrace]
  refine ⟨61402763549927396974783193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40935175699951597983188795 61402763549927396974783193)
  ·
    refine ⟨46052072662445547731087395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61402763549927396974783193 46052072662445547731087395)
    ·
      refine ⟨69078108993668321596631093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46052072662445547731087395 69078108993668321596631093)
      ·
        refine ⟨6476072718156405149684165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69078108993668321596631093 6476072718156405149684165)
        ·
          refine ⟨1214263634654325965565781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6476072718156405149684165 1214263634654325965565781)
          ·
            refine ⟨7114825984302691204487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1214263634654325965565781 7114825984302691204487)
            ·
              rfl

theorem cell22_1683513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 9].length) (baseStart_1683513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683513 prefixEnd_1683513 := by exact prefixLift 1683513
  have htrace : WordTrace (prefixWord ++ tailWord_1683513) baseStart_1683513 baseEnd_1683513 := by
    simpa [prefixWord, tailWord_1683513, baseEnd_1683513] using wordTrace_append hprefix tailTrace_1683513
  have hstable : (prefixWord ++ tailWord_1683513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683513).length < 2 ^ (prefixWord ++ tailWord_1683513).sum := by decide
  have hdescent : baseEnd_1683513 < baseStart_1683513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683575 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 5]
def baseStart_1683575 : Nat := 118140960795 + 1683575 * 2 ^ 59
def prefixEnd_1683575 : Nat := 4983230072969 + 3 ^ 40 * 1683575 * 2
def baseEnd_1683575 : Nat := 192107376198523497504419

theorem tailTrace_1683575 : CollatzResearch.WordTrace tailWord_1683575 prefixEnd_1683575 192107376198523497504419 := by
  unfold tailWord_1683575
  simp only [CollatzResearch.WordTrace]
  refine ⟨61405024875702781563540179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40936683250468521042360119 61405024875702781563540179)
  ·
    refine ⟨92107537313554172345310269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61405024875702781563540179 92107537313554172345310269)
    ·
      refine ⟨34540326492582814629491351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92107537313554172345310269 34540326492582814629491351)
      ·
        refine ⟨51810489738874221944237027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34540326492582814629491351 51810489738874221944237027)
        ·
          refine ⟨77715734608311332916355541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51810489738874221944237027 77715734608311332916355541)
          ·
            refine ⟨1821462529882296865227083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 77715734608311332916355541 1821462529882296865227083)
            ·
              refine ⟨2732193794823445297840625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1821462529882296865227083 2732193794823445297840625)
              ·
                refine ⟨2049145346117583973380469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2732193794823445297840625 2049145346117583973380469)
                ·
                  refine ⟨192107376198523497504419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2049145346117583973380469 192107376198523497504419)
                  ·
                    rfl

theorem cell22_1683575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 5].length) (baseStart_1683575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683575 prefixEnd_1683575 := by exact prefixLift 1683575
  have htrace : WordTrace (prefixWord ++ tailWord_1683575) baseStart_1683575 baseEnd_1683575 := by
    simpa [prefixWord, tailWord_1683575, baseEnd_1683575] using wordTrace_append hprefix tailTrace_1683575
  have hstable : (prefixWord ++ tailWord_1683575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683575).length < 2 ^ (prefixWord ++ tailWord_1683575).sum := by decide
  have hdescent : baseEnd_1683575 < baseStart_1683575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683592 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 5]
def baseStart_1683592 : Nat := 118140960795 + 1683592 * 2 ^ 59
def prefixEnd_1683592 : Nat := 4983230072969 + 3 ^ 40 * 1683592 * 2
def baseEnd_1683592 : Nat := 192109316014329371612735

theorem tailTrace_1683592 : CollatzResearch.WordTrace tailWord_1683592 prefixEnd_1683592 192109316014329371612735 := by
  unfold tailWord_1683592
  simp only [CollatzResearch.WordTrace]
  refine ⟨30702822458320596733454515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40937096611094128977939353 30702822458320596733454515)
  ·
    refine ⟨46054233687480895100181773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30702822458320596733454515 46054233687480895100181773)
    ·
      refine ⟨17270337632805335662568165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46054233687480895100181773 17270337632805335662568165)
      ·
        refine ⟨3238188306151000436731531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17270337632805335662568165 3238188306151000436731531)
        ·
          refine ⟨4857282459226500655097297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238188306151000436731531 4857282459226500655097297)
          ·
            refine ⟨3642961844419875491322973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4857282459226500655097297 3642961844419875491322973)
            ·
              refine ⟨1366110691657453309246115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3642961844419875491322973 1366110691657453309246115)
              ·
                refine ⟨2049166037486179963869173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366110691657453309246115 2049166037486179963869173)
                ·
                  refine ⟨192109316014329371612735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2049166037486179963869173 192109316014329371612735)
                  ·
                    rfl

theorem cell22_1683592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 5].length) (baseStart_1683592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683592 prefixEnd_1683592 := by exact prefixLift 1683592
  have htrace : WordTrace (prefixWord ++ tailWord_1683592) baseStart_1683592 baseEnd_1683592 := by
    simpa [prefixWord, tailWord_1683592, baseEnd_1683592] using wordTrace_append hprefix tailTrace_1683592
  have hstable : (prefixWord ++ tailWord_1683592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683592).length < 2 ^ (prefixWord ++ tailWord_1683592).sum := by decide
  have hdescent : baseEnd_1683592 < baseStart_1683592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683605 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_1683605 : Nat := 118140960795 + 1683605 * 2 ^ 59
def prefixEnd_1683605 : Nat := 4983230072969 + 3 ^ 40 * 1683605 * 2
def baseEnd_1683605 : Nat := 576332398208660414263165

theorem tailTrace_1683605 : CollatzResearch.WordTrace tailWord_1683605 prefixEnd_1683605 576332398208660414263165 := by
  unfold tailWord_1683605
  simp only [CollatzResearch.WordTrace]
  refine ⟨61406119065594096687132269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40937412710396064458088179 61406119065594096687132269)
  ·
    refine ⟨23027294649597786257674601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61406119065594096687132269 23027294649597786257674601)
    ·
      refine ⟨17270470987198339693255951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23027294649597786257674601 17270470987198339693255951)
      ·
        refine ⟨25905706480797509539883927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17270470987198339693255951 25905706480797509539883927)
        ·
          refine ⟨38858559721196264309825891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25905706480797509539883927 38858559721196264309825891)
          ·
            refine ⟨58287839581794396464738837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38858559721196264309825891 58287839581794396464738837)
            ·
              refine ⟨2732242480396612334284633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58287839581794396464738837 2732242480396612334284633)
              ·
                refine ⟨2049181860297459250713475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2732242480396612334284633 2049181860297459250713475)
                ·
                  refine ⟨3073772790446188876070213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049181860297459250713475 3073772790446188876070213)
                  ·
                    refine ⟨576332398208660414263165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3073772790446188876070213 576332398208660414263165)
                    ·
                      rfl

theorem cell22_1683605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_1683605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683605 prefixEnd_1683605 := by exact prefixLift 1683605
  have htrace : WordTrace (prefixWord ++ tailWord_1683605) baseStart_1683605 baseEnd_1683605 := by
    simpa [prefixWord, tailWord_1683605, baseEnd_1683605] using wordTrace_append hprefix tailTrace_1683605
  have hstable : (prefixWord ++ tailWord_1683605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683605).length < 2 ^ (prefixWord ++ tailWord_1683605).sum := by decide
  have hdescent : baseEnd_1683605 < baseStart_1683605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683635 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 2, 3]
def baseStart_1683635 : Nat := 118140960795 + 1683635 * 2 ^ 59
def prefixEnd_1683635 : Nat := 4983230072969 + 3 ^ 40 * 1683635 * 2
def baseEnd_1683635 : Nat := 576342667821750336013073

theorem tailTrace_1683635 : CollatzResearch.WordTrace tailWord_1683635 prefixEnd_1683635 576342667821750336013073 := by
  unfold tailWord_1683635
  simp only [CollatzResearch.WordTrace]
  refine ⟨61407213255485411810724359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40938142170323607873816239 61407213255485411810724359)
  ·
    refine ⟨92110819883228117716086539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61407213255485411810724359 92110819883228117716086539)
    ·
      refine ⟨138166229824842176574129809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92110819883228117716086539 138166229824842176574129809)
      ·
        refine ⟨103624672368631632430597357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138166229824842176574129809 103624672368631632430597357)
        ·
          refine ⟨38859252138236862161474009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103624672368631632430597357 38859252138236862161474009)
          ·
            refine ⟨29144439103677646621105507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38859252138236862161474009 29144439103677646621105507)
            ·
              refine ⟨43716658655516469931658261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29144439103677646621105507 43716658655516469931658261)
              ·
                refine ⟨2049218374477334528046481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43716658655516469931658261 2049218374477334528046481)
                ·
                  refine ⟨1536913780858000896034861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2049218374477334528046481 1536913780858000896034861)
                  ·
                    refine ⟨576342667821750336013073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536913780858000896034861 576342667821750336013073)
                    ·
                      rfl

theorem cell22_1683635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 3].length) (baseStart_1683635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683635 prefixEnd_1683635 := by exact prefixLift 1683635
  have htrace : WordTrace (prefixWord ++ tailWord_1683635) baseStart_1683635 baseEnd_1683635 := by
    simpa [prefixWord, tailWord_1683635, baseEnd_1683635] using wordTrace_append hprefix tailTrace_1683635
  have hstable : (prefixWord ++ tailWord_1683635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683635).length < 2 ^ (prefixWord ++ tailWord_1683635).sum := by decide
  have hdescent : baseEnd_1683635 < baseStart_1683635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683648 : List Nat := [2, 1, 1, 2, 5, 1, 1, 9]
def baseStart_1683648 : Nat := 118140960795 + 1683648 * 2 ^ 59
def prefixEnd_1683648 : Nat := 4983230072969 + 3 ^ 40 * 1683648 * 2
def baseEnd_1683648 : Nat := 64038568665269181715337

theorem tailTrace_1683648 : CollatzResearch.WordTrace tailWord_1683648 prefixEnd_1683648 64038568665269181715337 := by
  unfold tailWord_1683648
  simp only [CollatzResearch.WordTrace]
  refine ⟨30703843702219157515473799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40938458269625543353965065 30703843702219157515473799)
  ·
    refine ⟨46055765553328736273210699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30703843702219157515473799 46055765553328736273210699)
    ·
      refine ⟨69083648329993104409816049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46055765553328736273210699 69083648329993104409816049)
      ·
        refine ⟨51812736247494828307362037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69083648329993104409816049 51812736247494828307362037)
        ·
          refine ⟨4857444023202640153815191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51812736247494828307362037 4857444023202640153815191)
          ·
            refine ⟨7286166034803960230722787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4857444023202640153815191 7286166034803960230722787)
            ·
              refine ⟨10929249052205940346084181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286166034803960230722787 10929249052205940346084181)
              ·
                refine ⟨64038568665269181715337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10929249052205940346084181 64038568665269181715337)
                ·
                  rfl

theorem cell22_1683648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 9].length) (baseStart_1683648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683648 prefixEnd_1683648 := by exact prefixLift 1683648
  have htrace : WordTrace (prefixWord ++ tailWord_1683648) baseStart_1683648 baseEnd_1683648 := by
    simpa [prefixWord, tailWord_1683648, baseEnd_1683648] using wordTrace_append hprefix tailTrace_1683648
  have hstable : (prefixWord ++ tailWord_1683648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683648).length < 2 ^ (prefixWord ++ tailWord_1683648).sum := by decide
  have hdescent : baseEnd_1683648 < baseStart_1683648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683682 : List Nat := [3, 3, 4, 1, 11]
def baseStart_1683682 : Nat := 118140960795 + 1683682 * 2 ^ 59
def prefixEnd_1683682 : Nat := 4983230072969 + 3 ^ 40 * 1683682 * 2
def baseEnd_1683682 : Nat := 2371846736140978930403

theorem tailTrace_1683682 : CollatzResearch.WordTrace tailWord_1683682 prefixEnd_1683682 2371846736140978930403 := by
  unfold tailWord_1683682
  simp only [CollatzResearch.WordTrace]
  refine ⟨15352231871578784709421325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40939284990876759225123533 15352231871578784709421325)
  ·
    refine ⟨5757086951842044266032997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15352231871578784709421325 5757086951842044266032997)
    ·
      refine ⟨1079453803470383299881187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5757086951842044266032997 1079453803470383299881187)
      ·
        refine ⟨1619180705205574949821781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1079453803470383299881187 1619180705205574949821781)
        ·
          refine ⟨2371846736140978930403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1619180705205574949821781 2371846736140978930403)
          ·
            rfl

theorem cell22_1683682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 11].length) (baseStart_1683682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683682 prefixEnd_1683682 := by exact prefixLift 1683682
  have htrace : WordTrace (prefixWord ++ tailWord_1683682) baseStart_1683682 baseEnd_1683682 := by
    simpa [prefixWord, tailWord_1683682, baseEnd_1683682] using wordTrace_append hprefix tailTrace_1683682
  have hstable : (prefixWord ++ tailWord_1683682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683682).length < 2 ^ (prefixWord ++ tailWord_1683682).sum := by decide
  have hdescent : baseEnd_1683682 < baseStart_1683682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683714 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1683714 : Nat := 118140960795 + 1683714 * 2 ^ 59
def prefixEnd_1683714 : Nat := 4983230072969 + 3 ^ 40 * 1683714 * 2
def baseEnd_1683714 : Nat := 576369711136220463287831

theorem tailTrace_1683714 : CollatzResearch.WordTrace tailWord_1683714 prefixEnd_1683714 576369711136220463287831 := by
  unfold tailWord_1683714
  simp only [CollatzResearch.WordTrace]
  refine ⟨15352523655549802075712549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40940063081466138868566797 15352523655549802075712549)
  ·
    refine ⟨2878598185415587889196103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15352523655549802075712549 2878598185415587889196103)
    ·
      refine ⟨4317897278123381833794155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2878598185415587889196103 4317897278123381833794155)
      ·
        refine ⟨6476845917185072750691233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4317897278123381833794155 6476845917185072750691233)
        ·
          refine ⟨4857634437888804563018425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6476845917185072750691233 4857634437888804563018425)
          ·
            refine ⟨3643225828416603422263819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4857634437888804563018425 3643225828416603422263819)
            ·
              refine ⟨5464838742624905133395729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643225828416603422263819 5464838742624905133395729)
              ·
                refine ⟨4098629056968678850046797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5464838742624905133395729 4098629056968678850046797)
                ·
                  refine ⟨1536985896363254568767549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4098629056968678850046797 1536985896363254568767549)
                  ·
                    refine ⟨576369711136220463287831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536985896363254568767549 576369711136220463287831)
                    ·
                      rfl

theorem cell22_1683714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1683714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683714 prefixEnd_1683714 := by exact prefixLift 1683714
  have htrace : WordTrace (prefixWord ++ tailWord_1683714) baseStart_1683714 baseEnd_1683714 := by
    simpa [prefixWord, tailWord_1683714, baseEnd_1683714] using wordTrace_append hprefix tailTrace_1683714
  have hstable : (prefixWord ++ tailWord_1683714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683714).length < 2 ^ (prefixWord ++ tailWord_1683714).sum := by decide
  have hdescent : baseEnd_1683714 < baseStart_1683714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683774 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1683774 : Nat := 118140960795 + 1683774 * 2 ^ 59
def prefixEnd_1683774 : Nat := 4983230072969 + 3 ^ 40 * 1683774 * 2
def baseEnd_1683774 : Nat := 576390250362400306787647

theorem tailTrace_1683774 : CollatzResearch.WordTrace tailWord_1683774 prefixEnd_1683774 576390250362400306787647 := by
  unfold tailWord_1683774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7676535375247729818754297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40941522001321225700022917 7676535375247729818754297)
  ·
    refine ⟨5757401531435797364065723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7676535375247729818754297 5757401531435797364065723)
    ·
      refine ⟨8636102297153696046098585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5757401531435797364065723 8636102297153696046098585)
      ·
        refine ⟨6477076722865272034573939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8636102297153696046098585 6477076722865272034573939)
        ·
          refine ⟨9715615084297908051860909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6477076722865272034573939 9715615084297908051860909)
          ·
            refine ⟨3643355656611715519447841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9715615084297908051860909 3643355656611715519447841)
            ·
              refine ⟨2732516742458786639585881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3643355656611715519447841 2732516742458786639585881)
              ·
                refine ⟨2049387556844089979689411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2732516742458786639585881 2049387556844089979689411)
                ·
                  refine ⟨3074081335266134969534117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049387556844089979689411 3074081335266134969534117)
                  ·
                    refine ⟨576390250362400306787647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3074081335266134969534117 576390250362400306787647)
                    ·
                      rfl

theorem cell22_1683774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1683774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683774 prefixEnd_1683774 := by exact prefixLift 1683774
  have htrace : WordTrace (prefixWord ++ tailWord_1683774) baseStart_1683774 baseEnd_1683774 := by
    simpa [prefixWord, tailWord_1683774, baseEnd_1683774] using wordTrace_append hprefix tailTrace_1683774
  have hstable : (prefixWord ++ tailWord_1683774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683774).length < 2 ^ (prefixWord ++ tailWord_1683774).sum := by decide
  have hdescent : baseEnd_1683774 < baseStart_1683774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683785 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 2, 4]
def baseStart_1683785 : Nat := 118140960795 + 1683785 * 2 ^ 59
def prefixEnd_1683785 : Nat := 4983230072969 + 3 ^ 40 * 1683785 * 2
def baseEnd_1683785 : Nat := 576394015887199944762613

theorem tailTrace_1683785 : CollatzResearch.WordTrace tailWord_1683785 prefixEnd_1683785 576394015887199944762613 := by
  unfold tailWord_1683785
  simp only [CollatzResearch.WordTrace]
  refine ⟨61412684204941987428684809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40941789469961324952456539 61412684204941987428684809)
  ·
    refine ⟨46059513153706490571513607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61412684204941987428684809 46059513153706490571513607)
    ·
      refine ⟨69089269730559735857270411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46059513153706490571513607 69089269730559735857270411)
      ·
        refine ⟨103633904595839603785905617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69089269730559735857270411 103633904595839603785905617)
        ·
          refine ⟨77725428446879702839429213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103633904595839603785905617 77725428446879702839429213)
          ·
            refine ⟨29147035667579888564785955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77725428446879702839429213 29147035667579888564785955)
            ·
              refine ⟨43720553501369832847178933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29147035667579888564785955 43720553501369832847178933)
              ·
                refine ⟨4098801890753421829423025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43720553501369832847178933 4098801890753421829423025)
                ·
                  refine ⟨3074101418065066372067269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4098801890753421829423025 3074101418065066372067269)
                  ·
                    refine ⟨576394015887199944762613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3074101418065066372067269 576394015887199944762613)
                    ·
                      rfl

theorem cell22_1683785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_1683785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683785 prefixEnd_1683785 := by exact prefixLift 1683785
  have htrace : WordTrace (prefixWord ++ tailWord_1683785) baseStart_1683785 baseEnd_1683785 := by
    simpa [prefixWord, tailWord_1683785, baseEnd_1683785] using wordTrace_append hprefix tailTrace_1683785
  have hstable : (prefixWord ++ tailWord_1683785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683785).length < 2 ^ (prefixWord ++ tailWord_1683785).sum := by decide
  have hdescent : baseEnd_1683785 < baseStart_1683785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683866 : List Nat := [3, 1, 1, 4, 1, 3, 1, 4, 1, 3]
def baseStart_1683866 : Nat := 118140960795 + 1683866 * 2 ^ 59
def prefixEnd_1683866 : Nat := 4983230072969 + 3 ^ 40 * 1683866 * 2
def baseEnd_1683866 : Nat := 576421743842542733487365

theorem tailTrace_1683866 : CollatzResearch.WordTrace tailWord_1683866 prefixEnd_1683866 576421743842542733487365 := by
  unfold tailWord_1683866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15353909629412134565595863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40943759011765692174922301 15353909629412134565595863)
  ·
    refine ⟨23030864444118201848393795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15353909629412134565595863 23030864444118201848393795)
    ·
      refine ⟨34546296666177302772590693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23030864444118201848393795 34546296666177302772590693)
      ·
        refine ⟨6477430624908244269860755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34546296666177302772590693 6477430624908244269860755)
        ·
          refine ⟨9716145937362366404791133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6477430624908244269860755 9716145937362366404791133)
          ·
            refine ⟨3643554726510887401796675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9716145937362366404791133 3643554726510887401796675)
            ·
              refine ⟨5465332089766331102695013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643554726510887401796675 5465332089766331102695013)
              ·
                refine ⟨1024749766831187081755315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5465332089766331102695013 1024749766831187081755315)
                ·
                  refine ⟨1537124650246780622632973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024749766831187081755315 1537124650246780622632973)
                  ·
                    refine ⟨576421743842542733487365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1537124650246780622632973 576421743842542733487365)
                    ·
                      rfl

theorem cell22_1683866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_1683866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683866 prefixEnd_1683866 := by exact prefixLift 1683866
  have htrace : WordTrace (prefixWord ++ tailWord_1683866) baseStart_1683866 baseEnd_1683866 := by
    simpa [prefixWord, tailWord_1683866, baseEnd_1683866] using wordTrace_append hprefix tailTrace_1683866
  have hstable : (prefixWord ++ tailWord_1683866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683866).length < 2 ^ (prefixWord ++ tailWord_1683866).sum := by decide
  have hdescent : baseEnd_1683866 < baseStart_1683866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683920 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_1683920 : Nat := 118140960795 + 1683920 * 2 ^ 59
def prefixEnd_1683920 : Nat := 4983230072969 + 3 ^ 40 * 1683920 * 2
def baseEnd_1683920 : Nat := 576440229146104592637199

theorem tailTrace_1683920 : CollatzResearch.WordTrace tailWord_1683920 prefixEnd_1683920 576440229146104592637199 := by
  unfold tailWord_1683920
  simp only [CollatzResearch.WordTrace]
  refine ⟨30708804029726452742424607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40945072039635270323232809 30708804029726452742424607)
  ·
    refine ⟨46063206044589679113636911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30708804029726452742424607 46063206044589679113636911)
    ·
      refine ⟨69094809066884518670455367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46063206044589679113636911 69094809066884518670455367)
      ·
        refine ⟨103642213600326778005683051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69094809066884518670455367 103642213600326778005683051)
        ·
          refine ⟨155463320400490167008524577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103642213600326778005683051 155463320400490167008524577)
          ·
            refine ⟨116597490300367625256393433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155463320400490167008524577 116597490300367625256393433)
            ·
              refine ⟨87448117725275718942295075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116597490300367625256393433 87448117725275718942295075)
              ·
                refine ⟨131172176587913578413442613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87448117725275718942295075 131172176587913578413442613)
                ·
                  refine ⟨12297391555116897976260245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131172176587913578413442613 12297391555116897976260245)
                  ·
                    refine ⟨576440229146104592637199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12297391555116897976260245 576440229146104592637199)
                    ·
                      rfl

theorem cell22_1683920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_1683920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683920 prefixEnd_1683920 := by exact prefixLift 1683920
  have htrace : WordTrace (prefixWord ++ tailWord_1683920) baseStart_1683920 baseEnd_1683920 := by
    simpa [prefixWord, tailWord_1683920, baseEnd_1683920] using wordTrace_append hprefix tailTrace_1683920
  have hstable : (prefixWord ++ tailWord_1683920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683920).length < 2 ^ (prefixWord ++ tailWord_1683920).sum := by decide
  have hdescent : baseEnd_1683920 < baseStart_1683920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1683924 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 6]
def baseStart_1683924 : Nat := 118140960795 + 1683924 * 2 ^ 59
def prefixEnd_1683924 : Nat := 4983230072969 + 3 ^ 40 * 1683924 * 2
def baseEnd_1683924 : Nat := 192147199475949971845729

theorem tailTrace_1683924 : CollatzResearch.WordTrace tailWord_1683924 prefixEnd_1683924 192147199475949971845729 := by
  unfold tailWord_1683924
  simp only [CollatzResearch.WordTrace]
  refine ⟨30708876975719207083997413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40945169300958942778663217 30708876975719207083997413)
  ·
    refine ⟨5757914432947351328249515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30708876975719207083997413 5757914432947351328249515)
    ·
      refine ⟨8636871649421026992374273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5757914432947351328249515 8636871649421026992374273)
      ·
        refine ⟨6477653737065770244280705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8636871649421026992374273 6477653737065770244280705)
        ·
          refine ⟨4858240302799327683210529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6477653737065770244280705 4858240302799327683210529)
          ·
            refine ⟨3643680227099495762407897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4858240302799327683210529 3643680227099495762407897)
            ·
              refine ⟨2732760170324621821805923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3643680227099495762407897 2732760170324621821805923)
              ·
                refine ⟨4099140255486932732708885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2732760170324621821805923 4099140255486932732708885)
                ·
                  refine ⟨192147199475949971845729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4099140255486932732708885 192147199475949971845729)
                  ·
                    rfl

theorem cell22_1683924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_1683924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1683924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1683924 prefixEnd_1683924 := by exact prefixLift 1683924
  have htrace : WordTrace (prefixWord ++ tailWord_1683924) baseStart_1683924 baseEnd_1683924 := by
    simpa [prefixWord, tailWord_1683924, baseEnd_1683924] using wordTrace_append hprefix tailTrace_1683924
  have hstable : (prefixWord ++ tailWord_1683924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1683924).length < 2 ^ (prefixWord ++ tailWord_1683924).sum := by decide
  have hdescent : baseEnd_1683924 < baseStart_1683924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1683924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684074 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1684074 : Nat := 118140960795 + 1684074 * 2 ^ 59
def prefixEnd_1684074 : Nat := 4983230072969 + 3 ^ 40 * 1684074 * 2
def baseEnd_1684074 : Nat := 576492946493299524286727

theorem tailTrace_1684074 : CollatzResearch.WordTrace tailWord_1684074 prefixEnd_1684074 576492946493299524286727 := by
  unfold tailWord_1684074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15355806225223747446488819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40948816600596659857303517 15355806225223747446488819)
  ·
    refine ⟨23033709337835621169733229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15355806225223747446488819 23033709337835621169733229)
    ·
      refine ⟨8637641001688357938649961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23033709337835621169733229 8637641001688357938649961)
      ·
        refine ⟨6478230751266268453987471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8637641001688357938649961 6478230751266268453987471)
        ·
          refine ⟨9717346126899402680981207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6478230751266268453987471 9717346126899402680981207)
          ·
            refine ⟨14576019190349104021471811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717346126899402680981207 14576019190349104021471811)
            ·
              refine ⟨21864028785523656032207717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14576019190349104021471811 21864028785523656032207717)
              ·
                refine ⟨4099505397285685506038947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21864028785523656032207717 4099505397285685506038947)
                ·
                  refine ⟨6149258095928528259058421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4099505397285685506038947 6149258095928528259058421)
                  ·
                    refine ⟨576492946493299524286727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6149258095928528259058421 576492946493299524286727)
                    ·
                      rfl

theorem cell22_1684074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1684074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684074 prefixEnd_1684074 := by exact prefixLift 1684074
  have htrace : WordTrace (prefixWord ++ tailWord_1684074) baseStart_1684074 baseEnd_1684074 := by
    simpa [prefixWord, tailWord_1684074, baseEnd_1684074] using wordTrace_append hprefix tailTrace_1684074
  have hstable : (prefixWord ++ tailWord_1684074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684074).length < 2 ^ (prefixWord ++ tailWord_1684074).sum := by decide
  have hdescent : baseEnd_1684074 < baseStart_1684074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684078 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_1684078 : Nat := 118140960795 + 1684078 * 2 ^ 59
def prefixEnd_1684078 : Nat := 4983230072969 + 3 ^ 40 * 1684078 * 2
def baseEnd_1684078 : Nat := 576494315775044847186715

theorem tailTrace_1684078 : CollatzResearch.WordTrace tailWord_1684078 prefixEnd_1684078 576494315775044847186715 := by
  unfold tailWord_1684078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7677921349110062308637611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40948913861920332312733925 7677921349110062308637611)
  ·
    refine ⟨11516882023665093462956417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7677921349110062308637611 11516882023665093462956417)
    ·
      refine ⟨8637661517748820097217313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11516882023665093462956417 8637661517748820097217313)
      ·
        refine ⟨6478246138311615072912985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8637661517748820097217313 6478246138311615072912985)
        ·
          refine ⟨4858684603733711304684739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6478246138311615072912985 4858684603733711304684739)
          ·
            refine ⟨7288026905600566957027109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4858684603733711304684739 7288026905600566957027109)
            ·
              refine ⟨1366505044800106304442583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7288026905600566957027109 1366505044800106304442583)
              ·
                refine ⟨2049757567200159456663875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366505044800106304442583 2049757567200159456663875)
                ·
                  refine ⟨3074636350800239184995813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049757567200159456663875 3074636350800239184995813)
                  ·
                    refine ⟨576494315775044847186715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3074636350800239184995813 576494315775044847186715)
                    ·
                      rfl

theorem cell22_1684078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_1684078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684078 prefixEnd_1684078 := by exact prefixLift 1684078
  have htrace : WordTrace (prefixWord ++ tailWord_1684078) baseStart_1684078 baseEnd_1684078 := by
    simpa [prefixWord, tailWord_1684078, baseEnd_1684078] using wordTrace_append hprefix tailTrace_1684078
  have hstable : (prefixWord ++ tailWord_1684078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684078).length < 2 ^ (prefixWord ++ tailWord_1684078).sum := by decide
  have hdescent : baseEnd_1684078 < baseStart_1684078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684138 : List Nat := [3, 1, 5, 2, 1, 2, 8]
def baseStart_1684138 : Nat := 118140960795 + 1684138 * 2 ^ 59
def prefixEnd_1684138 : Nat := 4983230072969 + 3 ^ 40 * 1684138 * 2
def baseEnd_1684138 : Nat := 21352402037082395951353

theorem tailTrace_1684138 : CollatzResearch.WordTrace tailWord_1684138 prefixEnd_1684138 21352402037082395951353 := by
  unfold tailWord_1684138
  simp only [CollatzResearch.WordTrace]
  refine ⟨15356389793165782179071267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40950372781775419144190045 15356389793165782179071267)
  ·
    refine ⟨23034584689748673268606901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15356389793165782179071267 23034584689748673268606901)
    ·
      refine ⟨2159492314663938118931897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23034584689748673268606901 2159492314663938118931897)
      ·
        refine ⟨1619619235997953589198923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2159492314663938118931897 1619619235997953589198923)
        ·
          refine ⟨2429428853996930383798385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619619235997953589198923 2429428853996930383798385)
          ·
            refine ⟨1822071640497697787848789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2429428853996930383798385 1822071640497697787848789)
            ·
              refine ⟨21352402037082395951353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1822071640497697787848789 21352402037082395951353)
              ·
                rfl

theorem cell22_1684138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 8].length) (baseStart_1684138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684138 prefixEnd_1684138 := by exact prefixLift 1684138
  have htrace : WordTrace (prefixWord ++ tailWord_1684138) baseStart_1684138 baseEnd_1684138 := by
    simpa [prefixWord, tailWord_1684138, baseEnd_1684138] using wordTrace_append hprefix tailTrace_1684138
  have hstable : (prefixWord ++ tailWord_1684138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684138).length < 2 ^ (prefixWord ++ tailWord_1684138).sum := by decide
  have hdescent : baseEnd_1684138 < baseStart_1684138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684209 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_1684209 : Nat := 118140960795 + 1684209 * 2 ^ 59
def prefixEnd_1684209 : Nat := 4983230072969 + 3 ^ 40 * 1684209 * 2
def baseEnd_1684209 : Nat := 576539159752204172161313

theorem tailTrace_1684209 : CollatzResearch.WordTrace tailWord_1684209 prefixEnd_1684209 576539159752204172161313 := by
  unfold tailWord_1684209
  simp only [CollatzResearch.WordTrace]
  refine ⟨61428148755405907842119681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40952099170270605228079787 61428148755405907842119681)
  ·
    refine ⟨46071111566554430881589761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61428148755405907842119681 46071111566554430881589761)
    ·
      refine ⟨34553333674915823161192321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46071111566554430881589761 34553333674915823161192321)
      ·
        refine ⟨25915000256186867370894241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34553333674915823161192321 25915000256186867370894241)
        ·
          refine ⟨19436250192140150528170681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25915000256186867370894241 19436250192140150528170681)
          ·
            refine ⟨14577187644105112896128011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19436250192140150528170681 14577187644105112896128011)
            ·
              refine ⟨21865781466157669344192017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14577187644105112896128011 21865781466157669344192017)
              ·
                refine ⟨16399336099618252008144013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21865781466157669344192017 16399336099618252008144013)
                ·
                  refine ⟨6149751037356844503054005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16399336099618252008144013 6149751037356844503054005)
                  ·
                    refine ⟨576539159752204172161313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6149751037356844503054005 576539159752204172161313)
                    ·
                      rfl

theorem cell22_1684209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_1684209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684209 prefixEnd_1684209 := by exact prefixLift 1684209
  have htrace : WordTrace (prefixWord ++ tailWord_1684209) baseStart_1684209 baseEnd_1684209 := by
    simpa [prefixWord, tailWord_1684209, baseEnd_1684209] using wordTrace_append hprefix tailTrace_1684209
  have hstable : (prefixWord ++ tailWord_1684209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684209).length < 2 ^ (prefixWord ++ tailWord_1684209).sum := by decide
  have hdescent : baseEnd_1684209 < baseStart_1684209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684241 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 2, 4]
def baseStart_1684241 : Nat := 118140960795 + 1684241 * 2 ^ 59
def prefixEnd_1684241 : Nat := 4983230072969 + 3 ^ 40 * 1684241 * 2
def baseEnd_1684241 : Nat := 576550114006166755361215

theorem tailTrace_1684241 : CollatzResearch.WordTrace tailWord_1684241 prefixEnd_1684241 576550114006166755361215 := by
  unfold tailWord_1684241
  simp only [CollatzResearch.WordTrace]
  refine ⟨61429315891289977307284577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40952877260859984871523051 61429315891289977307284577)
  ·
    refine ⟨46071986918467482980463433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61429315891289977307284577 46071986918467482980463433)
    ·
      refine ⟨34553990188850612235347575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46071986918467482980463433 34553990188850612235347575)
      ·
        refine ⟨51830985283275918353021363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34553990188850612235347575 51830985283275918353021363)
        ·
          refine ⟨77746477924913877529532045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51830985283275918353021363 77746477924913877529532045)
          ·
            refine ⟨29154929221842704073574517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77746477924913877529532045 29154929221842704073574517)
            ·
              refine ⟨2733274614547753506897611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29154929221842704073574517 2733274614547753506897611)
              ·
                refine ⟨4099911921821630260346417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733274614547753506897611 4099911921821630260346417)
                ·
                  refine ⟨3074933941366222695259813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4099911921821630260346417 3074933941366222695259813)
                  ·
                    refine ⟨576550114006166755361215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3074933941366222695259813 576550114006166755361215)
                    ·
                      rfl

theorem cell22_1684241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_1684241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684241 prefixEnd_1684241 := by exact prefixLift 1684241
  have htrace : WordTrace (prefixWord ++ tailWord_1684241) baseStart_1684241 baseEnd_1684241 := by
    simpa [prefixWord, tailWord_1684241, baseEnd_1684241] using wordTrace_append hprefix tailTrace_1684241
  have hstable : (prefixWord ++ tailWord_1684241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684241).length < 2 ^ (prefixWord ++ tailWord_1684241).sum := by decide
  have hdescent : baseEnd_1684241 < baseStart_1684241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684247 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 1, 4]
def baseStart_1684247 : Nat := 118140960795 + 1684247 * 2 ^ 59
def prefixEnd_1684247 : Nat := 4983230072969 + 3 ^ 40 * 1684247 * 2
def baseEnd_1684247 : Nat := 576552167928784739711197

theorem tailTrace_1684247 : CollatzResearch.WordTrace tailWord_1684247 prefixEnd_1684247 576552167928784739711197 := by
  unfold tailWord_1684247
  simp only [CollatzResearch.WordTrace]
  refine ⟨61429534729268240332002995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40953023152845493554668663 61429534729268240332002995)
  ·
    refine ⟨92144302093902360498004493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61429534729268240332002995 92144302093902360498004493)
    ·
      refine ⟨34554113285213385186751685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92144302093902360498004493 34554113285213385186751685)
      ·
        refine ⟨6478896240977509722515941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34554113285213385186751685 6478896240977509722515941)
        ·
          refine ⟨1214793045183283072971739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6478896240977509722515941 1214793045183283072971739)
          ·
            refine ⟨1822189567774924609457609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214793045183283072971739 1822189567774924609457609)
            ·
              refine ⟨1366642175831193457093207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1822189567774924609457609 1366642175831193457093207)
              ·
                refine ⟨2049963263746790185639811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366642175831193457093207 2049963263746790185639811)
                ·
                  refine ⟨3074944895620185278459717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049963263746790185639811 3074944895620185278459717)
                  ·
                    refine ⟨576552167928784739711197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3074944895620185278459717 576552167928784739711197)
                    ·
                      rfl

theorem cell22_1684247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_1684247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684247 prefixEnd_1684247 := by exact prefixLift 1684247
  have htrace : WordTrace (prefixWord ++ tailWord_1684247) baseStart_1684247 baseEnd_1684247 := by
    simpa [prefixWord, tailWord_1684247, baseEnd_1684247] using wordTrace_append hprefix tailTrace_1684247
  have hstable : (prefixWord ++ tailWord_1684247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684247).length < 2 ^ (prefixWord ++ tailWord_1684247).sum := by decide
  have hdescent : baseEnd_1684247 < baseStart_1684247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684322 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1684322 : Nat := 118140960795 + 1684322 * 2 ^ 59
def prefixEnd_1684322 : Nat := 4983230072969 + 3 ^ 40 * 1684322 * 2
def baseEnd_1684322 : Nat := 576577841961509544085967

theorem tailTrace_1684322 : CollatzResearch.WordTrace tailWord_1684322 prefixEnd_1684322 576577841961509544085967 := by
  unfold tailWord_1684322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15358067550999132035245805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40954846802664352093988813 15358067550999132035245805)
  ·
    refine ⟨5759275331624674513217177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15358067550999132035245805 5759275331624674513217177)
    ·
      refine ⟨4319456498718505884912883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5759275331624674513217177 4319456498718505884912883)
      ·
        refine ⟨6479184748077758827369325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4319456498718505884912883 6479184748077758827369325)
        ·
          refine ⟨2429694280529159560263497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6479184748077758827369325 2429694280529159560263497)
          ·
            refine ⟨1822270710396869670197623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2429694280529159560263497 1822270710396869670197623)
            ·
              refine ⟨2733406065595304505296435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822270710396869670197623 2733406065595304505296435)
              ·
                refine ⟨4100109098392956757944653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733406065595304505296435 4100109098392956757944653)
                ·
                  refine ⟨1537540911897358784229245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4100109098392956757944653 1537540911897358784229245)
                  ·
                    refine ⟨576577841961509544085967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1537540911897358784229245 576577841961509544085967)
                    ·
                      rfl

theorem cell22_1684322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1684322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684322 prefixEnd_1684322 := by exact prefixLift 1684322
  have htrace : WordTrace (prefixWord ++ tailWord_1684322) baseStart_1684322 baseEnd_1684322 := by
    simpa [prefixWord, tailWord_1684322, baseEnd_1684322] using wordTrace_append hprefix tailTrace_1684322
  have hstable : (prefixWord ++ tailWord_1684322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684322).length < 2 ^ (prefixWord ++ tailWord_1684322).sum := by decide
  have hdescent : baseEnd_1684322 < baseStart_1684322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684361 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_1684361 : Nat := 118140960795 + 1684361 * 2 ^ 59
def prefixEnd_1684361 : Nat := 4983230072969 + 3 ^ 40 * 1684361 * 2
def baseEnd_1684361 : Nat := 576591192458526442360847

theorem tailTrace_1684361 : CollatzResearch.WordTrace tailWord_1684361 prefixEnd_1684361 576591192458526442360847 := by
  unfold tailWord_1684361
  simp only [CollatzResearch.WordTrace]
  refine ⟨61433692650855237801652937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40955795100570158534435291 61433692650855237801652937)
  ·
    refine ⟨46075269488141428351239703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61433692650855237801652937 46075269488141428351239703)
    ·
      refine ⟨69112904232212142526859555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46075269488141428351239703 69112904232212142526859555)
      ·
        refine ⟨103669356348318213790289333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69112904232212142526859555 103669356348318213790289333)
        ·
          refine ⟨9719002157654832542839625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103669356348318213790289333 9719002157654832542839625)
          ·
            refine ⟨7289251618241124407129719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9719002157654832542839625 7289251618241124407129719)
            ·
              refine ⟨10933877427361686610694579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7289251618241124407129719 10933877427361686610694579)
              ·
                refine ⟨16400816141042529916041869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10933877427361686610694579 16400816141042529916041869)
                ·
                  refine ⟨6150306052890948718515701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16400816141042529916041869 6150306052890948718515701)
                  ·
                    refine ⟨576591192458526442360847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6150306052890948718515701 576591192458526442360847)
                    ·
                      rfl

theorem cell22_1684361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_1684361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684361 prefixEnd_1684361 := by exact prefixLift 1684361
  have htrace : WordTrace (prefixWord ++ tailWord_1684361) baseStart_1684361 baseEnd_1684361 := by
    simpa [prefixWord, tailWord_1684361, baseEnd_1684361] using wordTrace_append hprefix tailTrace_1684361
  have hstable : (prefixWord ++ tailWord_1684361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684361).length < 2 ^ (prefixWord ++ tailWord_1684361).sum := by decide
  have hdescent : baseEnd_1684361 < baseStart_1684361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684408 : List Nat := [2, 1, 2, 1, 2, 5, 3, 6]
def baseStart_1684408 : Nat := 118140960795 + 1684408 * 2 ^ 59
def prefixEnd_1684408 : Nat := 4983230072969 + 3 ^ 40 * 1684408 * 2
def baseEnd_1684408 : Nat := 64067475724337109603967

theorem tailTrace_1684408 : CollatzResearch.WordTrace tailWord_1684408 prefixEnd_1684408 64067475724337109603967 := by
  unfold tailWord_1684408
  simp only [CollatzResearch.WordTrace]
  refine ⟨30717703440842482414306939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40956937921123309885742585 30717703440842482414306939)
  ·
    refine ⟨46076555161263723621460409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30717703440842482414306939 46076555161263723621460409)
    ·
      refine ⟨34557416370947792716095307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46076555161263723621460409 34557416370947792716095307)
      ·
        refine ⟨51836124556421689074142961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34557416370947792716095307 51836124556421689074142961)
        ·
          refine ⟨38877093417316266805607221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51836124556421689074142961 38877093417316266805607221)
          ·
            refine ⟨3644727507873400013025677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38877093417316266805607221 3644727507873400013025677)
            ·
              refine ⟨1366772815452525004884629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3644727507873400013025677 1366772815452525004884629)
              ·
                refine ⟨64067475724337109603967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1366772815452525004884629 64067475724337109603967)
                ·
                  rfl

theorem cell22_1684408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 6].length) (baseStart_1684408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684408 prefixEnd_1684408 := by exact prefixLift 1684408
  have htrace : WordTrace (prefixWord ++ tailWord_1684408) baseStart_1684408 baseEnd_1684408 := by
    simpa [prefixWord, tailWord_1684408, baseEnd_1684408] using wordTrace_append hprefix tailTrace_1684408
  have hstable : (prefixWord ++ tailWord_1684408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684408).length < 2 ^ (prefixWord ++ tailWord_1684408).sum := by decide
  have hdescent : baseEnd_1684408 < baseStart_1684408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684440 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 3, 3]
def baseStart_1684440 : Nat := 118140960795 + 1684440 * 2 ^ 59
def prefixEnd_1684440 : Nat := 4983230072969 + 3 ^ 40 * 1684440 * 2
def baseEnd_1684440 : Nat := 576618235772996569635605

theorem tailTrace_1684440 : CollatzResearch.WordTrace tailWord_1684440 prefixEnd_1684440 576618235772996569635605 := by
  unfold tailWord_1684440
  simp only [CollatzResearch.WordTrace]
  refine ⟨30718287008784517146889387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40957716011712689529185849 30718287008784517146889387)
  ·
    refine ⟨46077430513176775720334081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30718287008784517146889387 46077430513176775720334081)
    ·
      refine ⟨34558072884882581790250561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46077430513176775720334081 34558072884882581790250561)
      ·
        refine ⟨25918554663661936342687921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34558072884882581790250561 25918554663661936342687921)
        ·
          refine ⟨19438915997746452257015941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25918554663661936342687921 19438915997746452257015941)
          ·
            refine ⟨3644796749577459798190489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19438915997746452257015941 3644796749577459798190489)
            ·
              refine ⟨2733597562183094848642867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3644796749577459798190489 2733597562183094848642867)
              ·
                refine ⟨4100396343274642272964301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733597562183094848642867 4100396343274642272964301)
                ·
                  refine ⟨1537648628727990852361613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4100396343274642272964301 1537648628727990852361613)
                  ·
                    refine ⟨576618235772996569635605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1537648628727990852361613 576618235772996569635605)
                    ·
                      rfl

theorem cell22_1684440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_1684440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684440 prefixEnd_1684440 := by exact prefixLift 1684440
  have htrace : WordTrace (prefixWord ++ tailWord_1684440) baseStart_1684440 baseEnd_1684440 := by
    simpa [prefixWord, tailWord_1684440, baseEnd_1684440] using wordTrace_append hprefix tailTrace_1684440
  have hstable : (prefixWord ++ tailWord_1684440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684440).length < 2 ^ (prefixWord ++ tailWord_1684440).sum := by decide
  have hdescent : baseEnd_1684440 < baseStart_1684440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684496 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_1684496 : Nat := 118140960795 + 1684496 * 2 ^ 59
def prefixEnd_1684496 : Nat := 4983230072969 + 3 ^ 40 * 1684496 * 2
def baseEnd_1684496 : Nat := 576637405717431090235433

theorem tailTrace_1684496 : CollatzResearch.WordTrace tailWord_1684496 prefixEnd_1684496 576637405717431090235433 := by
  unfold tailWord_1684496
  simp only [CollatzResearch.WordTrace]
  refine ⟨30719308252683077928908671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40959077670244103905211561 30719308252683077928908671)
  ·
    refine ⟨46078962379024616893363007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30719308252683077928908671 46078962379024616893363007)
    ·
      refine ⟨69118443568536925340044511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46078962379024616893363007 69118443568536925340044511)
      ·
        refine ⟨103677665352805388010066767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69118443568536925340044511 103677665352805388010066767)
        ·
          refine ⟨155516498029208082015100151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103677665352805388010066767 155516498029208082015100151)
          ·
            refine ⟨233274747043812123022650227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155516498029208082015100151 233274747043812123022650227)
            ·
              refine ⟨349912120565718184533975341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233274747043812123022650227 349912120565718184533975341)
              ·
                refine ⟨131217045212144319200240753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349912120565718184533975341 131217045212144319200240753)
                ·
                  refine ⟨98412783909108239400180565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131217045212144319200240753 98412783909108239400180565)
                  ·
                    refine ⟨576637405717431090235433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 98412783909108239400180565 576637405717431090235433)
                    ·
                      rfl

theorem cell22_1684496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_1684496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684496 prefixEnd_1684496 := by exact prefixLift 1684496
  have htrace : WordTrace (prefixWord ++ tailWord_1684496) baseStart_1684496 baseEnd_1684496 := by
    simpa [prefixWord, tailWord_1684496, baseEnd_1684496] using wordTrace_append hprefix tailTrace_1684496
  have hstable : (prefixWord ++ tailWord_1684496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684496).length < 2 ^ (prefixWord ++ tailWord_1684496).sum := by decide
  have hdescent : baseEnd_1684496 < baseStart_1684496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684534 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1684534 : Nat := 118140960795 + 1684534 * 2 ^ 59
def prefixEnd_1684534 : Nat := 4983230072969 + 3 ^ 40 * 1684534 * 2
def baseEnd_1684534 : Nat := 576650413894011657785317

theorem tailTrace_1684534 : CollatzResearch.WordTrace tailWord_1684534 prefixEnd_1684534 576650413894011657785317 := by
  unfold tailWord_1684534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840000154951780521731291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40960001652818992231800437 3840000154951780521731291)
  ·
    refine ⟨5760000232427670782596937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3840000154951780521731291 5760000232427670782596937)
    ·
      refine ⟨4320000174320753086947703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5760000232427670782596937 4320000174320753086947703)
      ·
        refine ⟨6480000261481129630421555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4320000174320753086947703 6480000261481129630421555)
        ·
          refine ⟨9720000392221694445632333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6480000261481129630421555 9720000392221694445632333)
          ·
            refine ⟨3645000147083135417112125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9720000392221694445632333 3645000147083135417112125)
            ·
              refine ⟨1366875055156175781417047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3645000147083135417112125 1366875055156175781417047)
              ·
                refine ⟨2050312582734263672125571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366875055156175781417047 2050312582734263672125571)
                ·
                  refine ⟨3075468874101395508188357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050312582734263672125571 3075468874101395508188357)
                  ·
                    refine ⟨576650413894011657785317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3075468874101395508188357 576650413894011657785317)
                    ·
                      rfl

theorem cell22_1684534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1684534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684534 prefixEnd_1684534 := by exact prefixLift 1684534
  have htrace : WordTrace (prefixWord ++ tailWord_1684534) baseStart_1684534 baseEnd_1684534 := by
    simpa [prefixWord, tailWord_1684534, baseEnd_1684534] using wordTrace_append hprefix tailTrace_1684534
  have hstable : (prefixWord ++ tailWord_1684534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684534).length < 2 ^ (prefixWord ++ tailWord_1684534).sum := by decide
  have hdescent : baseEnd_1684534 < baseStart_1684534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684575 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 3, 3]
def baseStart_1684575 : Nat := 118140960795 + 1684575 * 2 ^ 59
def prefixEnd_1684575 : Nat := 4983230072969 + 3 ^ 40 * 1684575 * 2
def baseEnd_1684575 : Nat := 576664449031901217510191

theorem tailTrace_1684575 : CollatzResearch.WordTrace tailWord_1684575 prefixEnd_1684575 576664449031901217510191 := by
  unfold tailWord_1684575
  simp only [CollatzResearch.WordTrace]
  refine ⟨61441497872079952349943179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40960998581386634899962119 61441497872079952349943179)
  ·
    refine ⟨92162246808119928524914769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61441497872079952349943179 92162246808119928524914769)
    ·
      refine ⟨69121685106089946393686077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92162246808119928524914769 69121685106089946393686077)
      ·
        refine ⟨25920631914783729897632279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69121685106089946393686077 25920631914783729897632279)
        ·
          refine ⟨38880947872175594846448419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25920631914783729897632279 38880947872175594846448419)
          ·
            refine ⟨58321421808263392269672629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38880947872175594846448419 58321421808263392269672629)
            ·
              refine ⟨5467633294524693025281809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58321421808263392269672629 5467633294524693025281809)
              ·
                refine ⟨4100724970893519768961357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5467633294524693025281809 4100724970893519768961357)
                ·
                  refine ⟨1537771864085069913360509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4100724970893519768961357 1537771864085069913360509)
                  ·
                    refine ⟨576664449031901217510191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1537771864085069913360509 576664449031901217510191)
                    ·
                      rfl

theorem cell22_1684575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 3].length) (baseStart_1684575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684575 prefixEnd_1684575 := by exact prefixLift 1684575
  have htrace : WordTrace (prefixWord ++ tailWord_1684575) baseStart_1684575 baseEnd_1684575 := by
    simpa [prefixWord, tailWord_1684575, baseEnd_1684575] using wordTrace_append hprefix tailTrace_1684575
  have hstable : (prefixWord ++ tailWord_1684575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684575).length < 2 ^ (prefixWord ++ tailWord_1684575).sum := by decide
  have hdescent : baseEnd_1684575 < baseStart_1684575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684588 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 7]
def baseStart_1684588 : Nat := 118140960795 + 1684588 * 2 ^ 59
def prefixEnd_1684588 : Nat := 4983230072969 + 3 ^ 40 * 1684588 * 2
def baseEnd_1684588 : Nat := 192222966399191172311717

theorem tailTrace_1684588 : CollatzResearch.WordTrace tailWord_1684588 prefixEnd_1684588 192222966399191172311717 := by
  unfold tailWord_1684588
  simp only [CollatzResearch.WordTrace]
  refine ⟨30720986010516427785083209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40961314680688570380110945 30720986010516427785083209)
  ·
    refine ⟨23040739507887320838812407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30720986010516427785083209 23040739507887320838812407)
    ·
      refine ⟨34561109261830981258218611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23040739507887320838812407 34561109261830981258218611)
      ·
        refine ⟨51841663892746471887327917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34561109261830981258218611 51841663892746471887327917)
        ·
          refine ⟨19440623959779926957747969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51841663892746471887327917 19440623959779926957747969)
          ·
            refine ⟨14580467969834945218310977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19440623959779926957747969 14580467969834945218310977)
            ·
              refine ⟨10935350977376208913733233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14580467969834945218310977 10935350977376208913733233)
              ·
                refine ⟨8201513233032156685299925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10935350977376208913733233 8201513233032156685299925)
                ·
                  refine ⟨192222966399191172311717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8201513233032156685299925 192222966399191172311717)
                  ·
                    rfl

theorem cell22_1684588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_1684588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684588 prefixEnd_1684588 := by exact prefixLift 1684588
  have htrace : WordTrace (prefixWord ++ tailWord_1684588) baseStart_1684588 baseEnd_1684588 := by
    simpa [prefixWord, tailWord_1684588, baseEnd_1684588] using wordTrace_append hprefix tailTrace_1684588
  have hstable : (prefixWord ++ tailWord_1684588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684588).length < 2 ^ (prefixWord ++ tailWord_1684588).sum := by decide
  have hdescent : baseEnd_1684588 < baseStart_1684588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684609 : List Nat := [1, 2, 4, 2, 2, 1, 2, 4, 1, 3]
def baseStart_1684609 : Nat := 118140960795 + 1684609 * 2 ^ 59
def prefixEnd_1684609 : Nat := 4983230072969 + 3 ^ 40 * 1684609 * 2
def baseEnd_1684609 : Nat := 576676087926736462160087

theorem tailTrace_1684609 : CollatzResearch.WordTrace tailWord_1684609 prefixEnd_1684609 576676087926736462160087 := by
  unfold tailWord_1684609
  simp only [CollatzResearch.WordTrace]
  refine ⟨61442737953956776156680881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40961825302637850771120587 61442737953956776156680881)
  ·
    refine ⟨46082053465467582117510661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61442737953956776156680881 46082053465467582117510661)
    ·
      refine ⟨8640385024775171647033249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46082053465467582117510661 8640385024775171647033249)
      ·
        refine ⟨6480288768581378735274937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8640385024775171647033249 6480288768581378735274937)
        ·
          refine ⟨4860216576436034051456203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6480288768581378735274937 4860216576436034051456203)
          ·
            refine ⟨7290324864654051077184305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860216576436034051456203 7290324864654051077184305)
            ·
              refine ⟨5467743648490538307888229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7290324864654051077184305 5467743648490538307888229)
              ·
                refine ⟨1025201934091975932729043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5467743648490538307888229 1025201934091975932729043)
                ·
                  refine ⟨1537802901137963899093565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025201934091975932729043 1537802901137963899093565)
                  ·
                    refine ⟨576676087926736462160087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1537802901137963899093565 576676087926736462160087)
                    ·
                      rfl

theorem cell22_1684609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_1684609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684609 prefixEnd_1684609 := by exact prefixLift 1684609
  have htrace : WordTrace (prefixWord ++ tailWord_1684609) baseStart_1684609 baseEnd_1684609 := by
    simpa [prefixWord, tailWord_1684609, baseEnd_1684609] using wordTrace_append hprefix tailTrace_1684609
  have hstable : (prefixWord ++ tailWord_1684609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684609).length < 2 ^ (prefixWord ++ tailWord_1684609).sum := by decide
  have hdescent : baseEnd_1684609 < baseStart_1684609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684686 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_1684686 : Nat := 118140960795 + 1684686 * 2 ^ 59
def prefixEnd_1684686 : Nat := 4983230072969 + 3 ^ 40 * 1684686 * 2
def baseEnd_1684686 : Nat := 576702446600333927984851

theorem tailTrace_1684686 : CollatzResearch.WordTrace tailWord_1684686 prefixEnd_1684686 576702446600333927984851 := by
  unfold tailWord_1684686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7680693296834727288404239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40963697583118545538155941 7680693296834727288404239)
  ·
    refine ⟨11521039945252090932606359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7680693296834727288404239 11521039945252090932606359)
    ·
      refine ⟨17281559917878136398909539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11521039945252090932606359 17281559917878136398909539)
      ·
        refine ⟨25922339876817204598364309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17281559917878136398909539 25922339876817204598364309)
        ·
          refine ⟨1215109681725806465548327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25922339876817204598364309 1215109681725806465548327)
          ·
            refine ⟨1822664522588709698322491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215109681725806465548327 1822664522588709698322491)
            ·
              refine ⟨2733996783883064547483737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822664522588709698322491 2733996783883064547483737)
              ·
                refine ⟨2050497587912298410612803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2733996783883064547483737 2050497587912298410612803)
                ·
                  refine ⟨3075746381868447615919205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050497587912298410612803 3075746381868447615919205)
                  ·
                    refine ⟨576702446600333927984851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3075746381868447615919205 576702446600333927984851)
                    ·
                      rfl

theorem cell22_1684686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_1684686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684686 prefixEnd_1684686 := by exact prefixLift 1684686
  have htrace : WordTrace (prefixWord ++ tailWord_1684686) baseStart_1684686 baseEnd_1684686 := by
    simpa [prefixWord, tailWord_1684686, baseEnd_1684686] using wordTrace_append hprefix tailTrace_1684686
  have hstable : (prefixWord ++ tailWord_1684686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684686).length < 2 ^ (prefixWord ++ tailWord_1684686).sum := by decide
  have hdescent : baseEnd_1684686 < baseStart_1684686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684744 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 3, 3]
def baseStart_1684744 : Nat := 118140960795 + 1684744 * 2 ^ 59
def prefixEnd_1684744 : Nat := 4983230072969 + 3 ^ 40 * 1684744 * 2
def baseEnd_1684744 : Nat := 576722301185641110034673

theorem tailTrace_1684744 : CollatzResearch.WordTrace tailWord_1684744 prefixEnd_1684744 576722301185641110034673 := by
  unfold tailWord_1684744
  simp only [CollatzResearch.WordTrace]
  refine ⟨30723830904233847106422643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40965107872311796141896857 30723830904233847106422643)
  ·
    refine ⟨46085746356350770659633965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30723830904233847106422643 46085746356350770659633965)
    ·
      refine ⟨17282154883631538997362737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46085746356350770659633965 17282154883631538997362737)
      ·
        refine ⟨12961616162723654248022053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17282154883631538997362737 12961616162723654248022053)
        ·
          refine ⟨2430303030510685171504135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12961616162723654248022053 2430303030510685171504135)
          ·
            refine ⟨3645454545766027757256203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430303030510685171504135 3645454545766027757256203)
            ·
              refine ⟨5468181818649041635884305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3645454545766027757256203 5468181818649041635884305)
              ·
                refine ⟨4101136363986781226913229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5468181818649041635884305 4101136363986781226913229)
                ·
                  refine ⟨1537926136495042960092461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4101136363986781226913229 1537926136495042960092461)
                  ·
                    refine ⟨576722301185641110034673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1537926136495042960092461 576722301185641110034673)
                    ·
                      rfl

theorem cell22_1684744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_1684744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684744 prefixEnd_1684744 := by exact prefixLift 1684744
  have htrace : WordTrace (prefixWord ++ tailWord_1684744) baseStart_1684744 baseEnd_1684744 := by
    simpa [prefixWord, tailWord_1684744, baseEnd_1684744] using wordTrace_append hprefix tailTrace_1684744
  have hstable : (prefixWord ++ tailWord_1684744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684744).length < 2 ^ (prefixWord ++ tailWord_1684744).sum := by decide
  have hdescent : baseEnd_1684744 < baseStart_1684744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684817 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 6, 3]
def baseStart_1684817 : Nat := 118140960795 + 1684817 * 2 ^ 59
def prefixEnd_1684817 : Nat := 4983230072969 + 3 ^ 40 * 1684817 * 2
def baseEnd_1684817 : Nat := 576747290577493252959449

theorem tailTrace_1684817 : CollatzResearch.WordTrace tailWord_1684817 prefixEnd_1684817 576747290577493252959449 := by
  unfold tailWord_1684817
  simp only [CollatzResearch.WordTrace]
  refine ⟨61450324337203227680252705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40966882891468818453501803 61450324337203227680252705)
  ·
    refine ⟨46087743252902420760189529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61450324337203227680252705 46087743252902420760189529)
    ·
      refine ⟨34565807439676815570142147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46087743252902420760189529 34565807439676815570142147)
      ·
        refine ⟨51848711159515223355213221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34565807439676815570142147 51848711159515223355213221)
        ·
          refine ⟨9721633342409104379102479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51848711159515223355213221 9721633342409104379102479)
          ·
            refine ⟨14582450013613656568653719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9721633342409104379102479 14582450013613656568653719)
            ·
              refine ⟨21873675020420484852980579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14582450013613656568653719 21873675020420484852980579)
              ·
                refine ⟨32810512530630727279470869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21873675020420484852980579 32810512530630727279470869)
                ·
                  refine ⟨1537992774873315341225197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32810512530630727279470869 1537992774873315341225197)
                  ·
                    refine ⟨576747290577493252959449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1537992774873315341225197 576747290577493252959449)
                    ·
                      rfl

theorem cell22_1684817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_1684817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684817 prefixEnd_1684817 := by exact prefixLift 1684817
  have htrace : WordTrace (prefixWord ++ tailWord_1684817) baseStart_1684817 baseEnd_1684817 := by
    simpa [prefixWord, tailWord_1684817, baseEnd_1684817] using wordTrace_append hprefix tailTrace_1684817
  have hstable : (prefixWord ++ tailWord_1684817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684817).length < 2 ^ (prefixWord ++ tailWord_1684817).sum := by decide
  have hdescent : baseEnd_1684817 < baseStart_1684817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684832 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 4, 4]
def baseStart_1684832 : Nat := 118140960795 + 1684832 * 2 ^ 59
def prefixEnd_1684832 : Nat := 4983230072969 + 3 ^ 40 * 1684832 * 2
def baseEnd_1684832 : Nat := 576752425384038213834403

theorem tailTrace_1684832 : CollatzResearch.WordTrace tailWord_1684832 prefixEnd_1684832 576752425384038213834403 := by
  unfold tailWord_1684832
  simp only [CollatzResearch.WordTrace]
  refine ⟨30725435716074442621024375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40967247621432590161365833 30725435716074442621024375)
  ·
    refine ⟨46088153574111663931536563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30725435716074442621024375 46088153574111663931536563)
    ·
      refine ⟨69132230361167495897304845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46088153574111663931536563 69132230361167495897304845)
      ·
        refine ⟨25924586385437810961489317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69132230361167495897304845 25924586385437810961489317)
        ·
          refine ⟨4860859947269589555279247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25924586385437810961489317 4860859947269589555279247)
          ·
            refine ⟨7291289920904384332918871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860859947269589555279247 7291289920904384332918871)
            ·
              refine ⟨10936934881356576499378307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291289920904384332918871 10936934881356576499378307)
              ·
                refine ⟨16405402322034864749067461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10936934881356576499378307 16405402322034864749067461)
                ·
                  refine ⟨3076012935381537140450149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16405402322034864749067461 3076012935381537140450149)
                  ·
                    refine ⟨576752425384038213834403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3076012935381537140450149 576752425384038213834403)
                    ·
                      rfl

theorem cell22_1684832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_1684832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684832 prefixEnd_1684832 := by exact prefixLift 1684832
  have htrace : WordTrace (prefixWord ++ tailWord_1684832) baseStart_1684832 baseEnd_1684832 := by
    simpa [prefixWord, tailWord_1684832, baseEnd_1684832] using wordTrace_append hprefix tailTrace_1684832
  have hstable : (prefixWord ++ tailWord_1684832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684832).length < 2 ^ (prefixWord ++ tailWord_1684832).sum := by decide
  have hdescent : baseEnd_1684832 < baseStart_1684832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684834 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1684834 : Nat := 118140960795 + 1684834 * 2 ^ 59
def prefixEnd_1684834 : Nat := 4983230072969 + 3 ^ 40 * 1684834 * 2
def baseEnd_1684834 : Nat := 576753110024910875284397

theorem tailTrace_1684834 : CollatzResearch.WordTrace tailWord_1684834 prefixEnd_1684834 576753110024910875284397 := by
  unfold tailWord_1684834
  simp only [CollatzResearch.WordTrace]
  refine ⟨15362736094535409895905389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40967296252094426389081037 15362736094535409895905389)
  ·
    refine ⟨5761026035450778710964521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15362736094535409895905389 5761026035450778710964521)
    ·
      refine ⟨4320769526588084033223391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5761026035450778710964521 4320769526588084033223391)
      ·
        refine ⟨6481154289882126049835087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4320769526588084033223391 6481154289882126049835087)
        ·
          refine ⟨9721731434823189074752631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6481154289882126049835087 9721731434823189074752631)
          ·
            refine ⟨14582597152234783612128947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9721731434823189074752631 14582597152234783612128947)
            ·
              refine ⟨21873895728352175418193421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14582597152234783612128947 21873895728352175418193421)
              ·
                refine ⟨8202710898132065781822533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21873895728352175418193421 8202710898132065781822533)
                ·
                  refine ⟨1538008293399762334091725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8202710898132065781822533 1538008293399762334091725)
                  ·
                    refine ⟨576753110024910875284397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1538008293399762334091725 576753110024910875284397)
                    ·
                      rfl

theorem cell22_1684834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1684834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684834 prefixEnd_1684834 := by exact prefixLift 1684834
  have htrace : WordTrace (prefixWord ++ tailWord_1684834) baseStart_1684834 baseEnd_1684834 := by
    simpa [prefixWord, tailWord_1684834, baseEnd_1684834] using wordTrace_append hprefix tailTrace_1684834
  have hstable : (prefixWord ++ tailWord_1684834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684834).length < 2 ^ (prefixWord ++ tailWord_1684834).sum := by decide
  have hdescent : baseEnd_1684834 < baseStart_1684834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684836 : List Nat := [2, 3, 1, 1, 3, 3, 3, 2, 4]
def baseStart_1684836 : Nat := 118140960795 + 1684836 * 2 ^ 59
def prefixEnd_1684836 : Nat := 4983230072969 + 3 ^ 40 * 1684836 * 2
def baseEnd_1684836 : Nat := 192251264888594512244797

theorem tailTrace_1684836 : CollatzResearch.WordTrace tailWord_1684836 prefixEnd_1684836 192251264888594512244797 := by
  unfold tailWord_1684836
  simp only [CollatzResearch.WordTrace]
  refine ⟨30725508662067196962597181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40967344882756262616796241 30725508662067196962597181)
  ·
    refine ⟨11522065748275198860973943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30725508662067196962597181 11522065748275198860973943)
    ·
      refine ⟨17283098622412798291460915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11522065748275198860973943 17283098622412798291460915)
      ·
        refine ⟨25924647933619197437191373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17283098622412798291460915 25924647933619197437191373)
        ·
          refine ⟨9721742975107199038946765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25924647933619197437191373 9721742975107199038946765)
          ·
            refine ⟨3645653615665199639605037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9721742975107199038946765 3645653615665199639605037)
            ·
              refine ⟨1367120105874449864851889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3645653615665199639605037 1367120105874449864851889)
              ·
                refine ⟨1025340079405837398638917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1367120105874449864851889 1025340079405837398638917)
                ·
                  refine ⟨192251264888594512244797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1025340079405837398638917 192251264888594512244797)
                  ·
                    rfl

theorem cell22_1684836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_1684836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684836 prefixEnd_1684836 := by exact prefixLift 1684836
  have htrace : WordTrace (prefixWord ++ tailWord_1684836) baseStart_1684836 baseEnd_1684836 := by
    simpa [prefixWord, tailWord_1684836, baseEnd_1684836] using wordTrace_append hprefix tailTrace_1684836
  have hstable : (prefixWord ++ tailWord_1684836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684836).length < 2 ^ (prefixWord ++ tailWord_1684836).sum := by decide
  have hdescent : baseEnd_1684836 < baseStart_1684836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684866 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1684866 : Nat := 118140960795 + 1684866 * 2 ^ 59
def prefixEnd_1684866 : Nat := 4983230072969 + 3 ^ 40 * 1684866 * 2
def baseEnd_1684866 : Nat := 576764064278873458484299

theorem tailTrace_1684866 : CollatzResearch.WordTrace tailWord_1684866 prefixEnd_1684866 576764064278873458484299 := by
  unfold tailWord_1684866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15363027878506427262196613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40968074342683806032524301 15363027878506427262196613)
  ·
    refine ⟨2880567727219955111661865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15363027878506427262196613 2880567727219955111661865)
    ·
      refine ⟨2160425795414966333746399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2880567727219955111661865 2160425795414966333746399)
      ·
        refine ⟨3240638693122449500619599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2160425795414966333746399 3240638693122449500619599)
        ·
          refine ⟨4860958039683674250929399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240638693122449500619599 4860958039683674250929399)
          ·
            refine ⟨7291437059525511376394099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860958039683674250929399 7291437059525511376394099)
            ·
              refine ⟨10937155589288267064591149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291437059525511376394099 10937155589288267064591149)
              ·
                refine ⟨4101433345983100149221681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10937155589288267064591149 4101433345983100149221681)
                ·
                  refine ⟨3076075009487325111916261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4101433345983100149221681 3076075009487325111916261)
                  ·
                    refine ⟨576764064278873458484299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3076075009487325111916261 576764064278873458484299)
                    ·
                      rfl

theorem cell22_1684866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1684866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684866 prefixEnd_1684866 := by exact prefixLift 1684866
  have htrace : WordTrace (prefixWord ++ tailWord_1684866) baseStart_1684866 baseEnd_1684866 := by
    simpa [prefixWord, tailWord_1684866, baseEnd_1684866] using wordTrace_append hprefix tailTrace_1684866
  have hstable : (prefixWord ++ tailWord_1684866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684866).length < 2 ^ (prefixWord ++ tailWord_1684866).sum := by decide
  have hdescent : baseEnd_1684866 < baseStart_1684866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684896 : List Nat := [2, 1, 1, 4, 1, 2, 3, 4, 1, 3]
def baseStart_1684896 : Nat := 118140960795 + 1684896 * 2 ^ 59
def prefixEnd_1684896 : Nat := 4983230072969 + 3 ^ 40 * 1684896 * 2
def baseEnd_1684896 : Nat := 576774333891963380234207

theorem tailTrace_1684896 : CollatzResearch.WordTrace tailWord_1684896 prefixEnd_1684896 576774333891963380234207 := by
  unfold tailWord_1684896
  simp only [CollatzResearch.WordTrace]
  refine ⟨30726602851958512086189271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40968803802611349448252361 30726602851958512086189271)
  ·
    refine ⟨46089904277937768129283907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30726602851958512086189271 46089904277937768129283907)
    ·
      refine ⟨69134856416906652193925861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46089904277937768129283907 69134856416906652193925861)
      ·
        refine ⟨12962785578169997286361099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69134856416906652193925861 12962785578169997286361099)
        ·
          refine ⟨19444178367254995929541649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12962785578169997286361099 19444178367254995929541649)
          ·
            refine ⟨14583133775441246947156237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19444178367254995929541649 14583133775441246947156237)
            ·
              refine ⟨5468675165790467605183589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14583133775441246947156237 5468675165790467605183589)
              ·
                refine ⟨1025376593585712675971923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5468675165790467605183589 1025376593585712675971923)
                ·
                  refine ⟨1538064890378569013957885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025376593585712675971923 1538064890378569013957885)
                  ·
                    refine ⟨576774333891963380234207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1538064890378569013957885 576774333891963380234207)
                    ·
                      rfl

theorem cell22_1684896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 1, 3].length) (baseStart_1684896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684896 prefixEnd_1684896 := by exact prefixLift 1684896
  have htrace : WordTrace (prefixWord ++ tailWord_1684896) baseStart_1684896 baseEnd_1684896 := by
    simpa [prefixWord, tailWord_1684896, baseEnd_1684896] using wordTrace_append hprefix tailTrace_1684896
  have hstable : (prefixWord ++ tailWord_1684896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684896).length < 2 ^ (prefixWord ++ tailWord_1684896).sum := by decide
  have hdescent : baseEnd_1684896 < baseStart_1684896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684952 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_1684952 : Nat := 118140960795 + 1684952 * 2 ^ 59
def prefixEnd_1684952 : Nat := 4983230072969 + 3 ^ 40 * 1684952 * 2
def baseEnd_1684952 : Nat := 576793503836397900834035

theorem tailTrace_1684952 : CollatzResearch.WordTrace tailWord_1684952 prefixEnd_1684952 576793503836397900834035 := by
  unfold tailWord_1684952
  simp only [CollatzResearch.WordTrace]
  refine ⟨30727624095857072868208555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40970165461142763824278073 30727624095857072868208555)
  ·
    refine ⟨46091436143785609302312833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30727624095857072868208555 46091436143785609302312833)
    ·
      refine ⟨34568577107839206976734625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46091436143785609302312833 34568577107839206976734625)
      ·
        refine ⟨25926432830879405232550969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34568577107839206976734625 25926432830879405232550969)
        ·
          refine ⟨19444824623159553924413227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25926432830879405232550969 19444824623159553924413227)
          ·
            refine ⟨29167236934739330886619841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19444824623159553924413227 29167236934739330886619841)
            ·
              refine ⟨21875427701054498164964881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29167236934739330886619841 21875427701054498164964881)
              ·
                refine ⟨16406570775790873623723661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21875427701054498164964881 16406570775790873623723661)
                ·
                  refine ⟨6152464040921577608896373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16406570775790873623723661 6152464040921577608896373)
                  ·
                    refine ⟨576793503836397900834035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6152464040921577608896373 576793503836397900834035)
                    ·
                      rfl

theorem cell22_1684952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_1684952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684952 prefixEnd_1684952 := by exact prefixLift 1684952
  have htrace : WordTrace (prefixWord ++ tailWord_1684952) baseStart_1684952 baseEnd_1684952 := by
    simpa [prefixWord, tailWord_1684952, baseEnd_1684952] using wordTrace_append hprefix tailTrace_1684952
  have hstable : (prefixWord ++ tailWord_1684952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684952).length < 2 ^ (prefixWord ++ tailWord_1684952).sum := by decide
  have hdescent : baseEnd_1684952 < baseStart_1684952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684954 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_1684954 : Nat := 118140960795 + 1684954 * 2 ^ 59
def prefixEnd_1684954 : Nat := 4983230072969 + 3 ^ 40 * 1684954 * 2
def baseEnd_1684954 : Nat := 192264729492423520761343

theorem tailTrace_1684954 : CollatzResearch.WordTrace tailWord_1684954 prefixEnd_1684954 192264729492423520761343 := by
  unfold tailWord_1684954
  simp only [CollatzResearch.WordTrace]
  refine ⟨15363830284426725019497479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40970214091804600051993277 15363830284426725019497479)
  ·
    refine ⟨23045745426640087529246219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15363830284426725019497479 23045745426640087529246219)
    ·
      refine ⟨34568618139960131293869329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23045745426640087529246219 34568618139960131293869329)
      ·
        refine ⟨25926463604970098470401997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34568618139960131293869329 25926463604970098470401997)
        ·
          refine ⟨9722423851863786926400749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25926463604970098470401997 9722423851863786926400749)
          ·
            refine ⟨3645908944448920097400281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9722423851863786926400749 3645908944448920097400281)
            ·
              refine ⟨2734431708336690073050211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645908944448920097400281 2734431708336690073050211)
              ·
                refine ⟨4101647562505035109575317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734431708336690073050211 4101647562505035109575317)
                ·
                  refine ⟨192264729492423520761343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4101647562505035109575317 192264729492423520761343)
                  ·
                    rfl

theorem cell22_1684954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_1684954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684954 prefixEnd_1684954 := by exact prefixLift 1684954
  have htrace : WordTrace (prefixWord ++ tailWord_1684954) baseStart_1684954 baseEnd_1684954 := by
    simpa [prefixWord, tailWord_1684954, baseEnd_1684954] using wordTrace_append hprefix tailTrace_1684954
  have hstable : (prefixWord ++ tailWord_1684954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684954).length < 2 ^ (prefixWord ++ tailWord_1684954).sum := by decide
  have hdescent : baseEnd_1684954 < baseStart_1684954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684973 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_1684973 : Nat := 118140960795 + 1684973 * 2 ^ 59
def prefixEnd_1684973 : Nat := 4983230072969 + 3 ^ 40 * 1684973 * 2
def baseEnd_1684973 : Nat := 576800692565560846058971

theorem tailTrace_1684973 : CollatzResearch.WordTrace tailWord_1684973 prefixEnd_1684973 576800692565560846058971 := by
  unfold tailWord_1684973
  simp only [CollatzResearch.WordTrace]
  refine ⟨61456014124638066322931573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40970676083092044215287715 61456014124638066322931573)
  ·
    refine ⟨5761501324184818717774835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61456014124638066322931573 5761501324184818717774835)
    ·
      refine ⟨8642251986277228076662253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5761501324184818717774835 8642251986277228076662253)
      ·
        refine ⟨3240844494853960528748345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8642251986277228076662253 3240844494853960528748345)
        ·
          refine ⟨2430633371140470396561259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3240844494853960528748345 2430633371140470396561259)
          ·
            refine ⟨3645950056710705594841889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430633371140470396561259 3645950056710705594841889)
            ·
              refine ⟨2734462542533029196131417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645950056710705594841889 2734462542533029196131417)
              ·
                refine ⟨2050846906899771897098563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2734462542533029196131417 2050846906899771897098563)
                ·
                  refine ⟨3076270360349657845647845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050846906899771897098563 3076270360349657845647845)
                  ·
                    refine ⟨576800692565560846058971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3076270360349657845647845 576800692565560846058971)
                    ·
                      rfl

theorem cell22_1684973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_1684973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684973 prefixEnd_1684973 := by exact prefixLift 1684973
  have htrace : WordTrace (prefixWord ++ tailWord_1684973) baseStart_1684973 baseEnd_1684973 := by
    simpa [prefixWord, tailWord_1684973, baseEnd_1684973] using wordTrace_append hprefix tailTrace_1684973
  have hstable : (prefixWord ++ tailWord_1684973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684973).length < 2 ^ (prefixWord ++ tailWord_1684973).sum := by decide
  have hdescent : baseEnd_1684973 < baseStart_1684973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1684999 : List Nat := [1, 1, 4, 3, 2, 3, 8]
def baseStart_1684999 : Nat := 118140960795 + 1684999 * 2 ^ 59
def prefixEnd_1684999 : Nat := 4983230072969 + 3 ^ 40 * 1684999 * 2
def baseEnd_1684999 : Nat := 21363318255440942404033

theorem tailTrace_1684999 : CollatzResearch.WordTrace tailWord_1684999 prefixEnd_1684999 21363318255440942404033 := by
  unfold tailWord_1684999
  simp only [CollatzResearch.WordTrace]
  refine ⟨61456962422543872763378051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40971308281695915175585367 61456962422543872763378051)
  ·
    refine ⟨92185443633815809145067077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61456962422543872763378051 92185443633815809145067077)
    ·
      refine ⟨17284770681340464214700077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92185443633815809145067077 17284770681340464214700077)
      ·
        refine ⟨6481789005502674080512529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17284770681340464214700077 6481789005502674080512529)
        ·
          refine ⟨4861341754127005560384397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6481789005502674080512529 4861341754127005560384397)
          ·
            refine ⟨1823003157797627085144149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4861341754127005560384397 1823003157797627085144149)
            ·
              refine ⟨21363318255440942404033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1823003157797627085144149 21363318255440942404033)
              ·
                rfl

theorem cell22_1684999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 8].length) (baseStart_1684999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1684999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1684999 prefixEnd_1684999 := by exact prefixLift 1684999
  have htrace : WordTrace (prefixWord ++ tailWord_1684999) baseStart_1684999 baseEnd_1684999 := by
    simpa [prefixWord, tailWord_1684999, baseEnd_1684999] using wordTrace_append hprefix tailTrace_1684999
  have hstable : (prefixWord ++ tailWord_1684999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1684999).length < 2 ^ (prefixWord ++ tailWord_1684999).sum := by decide
  have hdescent : baseEnd_1684999 < baseStart_1684999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1684999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685005 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1685005 : Nat := 118140960795 + 1685005 * 2 ^ 59
def prefixEnd_1685005 : Nat := 4983230072969 + 3 ^ 40 * 1685005 * 2
def baseEnd_1685005 : Nat := 192270548939841143086291

theorem tailTrace_1685005 : CollatzResearch.WordTrace tailWord_1685005 prefixEnd_1685005 192270548939841143086291 := by
  unfold tailWord_1685005
  simp only [CollatzResearch.WordTrace]
  refine ⟨61457181260522135788096469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40971454173681423858730979 61457181260522135788096469)
  ·
    refine ⟨1440402685793487557533511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 61457181260522135788096469 1440402685793487557533511)
    ·
      refine ⟨2160604028690231336300267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1440402685793487557533511 2160604028690231336300267)
      ·
        refine ⟨3240906043035347004450401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2160604028690231336300267 3240906043035347004450401)
        ·
          refine ⟨2430679532276510253337801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3240906043035347004450401 2430679532276510253337801)
          ·
            refine ⟨1823009649207382690003351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2430679532276510253337801 1823009649207382690003351)
            ·
              refine ⟨2734514473811074035005027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823009649207382690003351 2734514473811074035005027)
              ·
                refine ⟨4101771710716611052507541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734514473811074035005027 4101771710716611052507541)
                ·
                  refine ⟨192270548939841143086291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4101771710716611052507541 192270548939841143086291)
                  ·
                    rfl

theorem cell22_1685005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1685005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685005 prefixEnd_1685005 := by exact prefixLift 1685005
  have htrace : WordTrace (prefixWord ++ tailWord_1685005) baseStart_1685005 baseEnd_1685005 := by
    simpa [prefixWord, tailWord_1685005, baseEnd_1685005] using wordTrace_append hprefix tailTrace_1685005
  have hstable : (prefixWord ++ tailWord_1685005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685005).length < 2 ^ (prefixWord ++ tailWord_1685005).sum := by decide
  have hdescent : baseEnd_1685005 < baseStart_1685005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685089 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 6]
def baseStart_1685089 : Nat := 118140960795 + 1685089 * 2 ^ 59
def prefixEnd_1685089 : Nat := 4983230072969 + 3 ^ 40 * 1685089 * 2
def baseEnd_1685089 : Nat := 192280133912058403386205

theorem tailTrace_1685089 : CollatzResearch.WordTrace tailWord_1685089 prefixEnd_1685089 192280133912058403386205 := by
  unfold tailWord_1685089
  simp only [CollatzResearch.WordTrace]
  refine ⟨61460244992217818134154321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40973496661478545422769547 61460244992217818134154321)
  ·
    refine ⟨46095183744163363600615741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61460244992217818134154321 46095183744163363600615741)
    ·
      refine ⟨17285693904061261350230903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46095183744163363600615741 17285693904061261350230903)
      ·
        refine ⟨25928540856091892025346355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17285693904061261350230903 25928540856091892025346355)
        ·
          refine ⟨38892811284137838038019533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25928540856091892025346355 38892811284137838038019533)
          ·
            refine ⟨14584804231551689264257325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38892811284137838038019533 14584804231551689264257325)
            ·
              refine ⟨5469301586831883474096497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14584804231551689264257325 5469301586831883474096497)
              ·
                refine ⟨4101976190123912605572373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5469301586831883474096497 4101976190123912605572373)
                ·
                  refine ⟨192280133912058403386205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4101976190123912605572373 192280133912058403386205)
                  ·
                    rfl

theorem cell22_1685089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_1685089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685089 prefixEnd_1685089 := by exact prefixLift 1685089
  have htrace : WordTrace (prefixWord ++ tailWord_1685089) baseStart_1685089 baseEnd_1685089 := by
    simpa [prefixWord, tailWord_1685089, baseEnd_1685089] using wordTrace_append hprefix tailTrace_1685089
  have hstable : (prefixWord ++ tailWord_1685089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685089).length < 2 ^ (prefixWord ++ tailWord_1685089).sum := by decide
  have hdescent : baseEnd_1685089 < baseStart_1685089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685149 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1685149 : Nat := 118140960795 + 1685149 * 2 ^ 59
def prefixEnd_1685149 : Nat := 4983230072969 + 3 ^ 40 * 1685149 * 2
def baseEnd_1685149 : Nat := 576860940962355053658431

theorem tailTrace_1685149 : CollatzResearch.WordTrace tailWord_1685149 prefixEnd_1685149 576860940962355053658431 := by
  unfold tailWord_1685149
  simp only [CollatzResearch.WordTrace]
  refine ⟨61462433372000448381338501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40974955581333632254225667 61462433372000448381338501)
  ·
    refine ⟨11524206257250084071500969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61462433372000448381338501 11524206257250084071500969)
    ·
      refine ⟨8643154692937563053625727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11524206257250084071500969 8643154692937563053625727)
      ·
        refine ⟨12964732039406344580438591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8643154692937563053625727 12964732039406344580438591)
        ·
          refine ⟨19447098059109516870657887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12964732039406344580438591 19447098059109516870657887)
          ·
            refine ⟨29170647088664275305986831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19447098059109516870657887 29170647088664275305986831)
            ·
              refine ⟨43755970632996412958980247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29170647088664275305986831 43755970632996412958980247)
              ·
                refine ⟨65633955949494619438470371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43755970632996412958980247 65633955949494619438470371)
                ·
                  refine ⟨98450933924241929157705557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65633955949494619438470371 98450933924241929157705557)
                  ·
                    refine ⟨576860940962355053658431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 98450933924241929157705557 576860940962355053658431)
                    ·
                      rfl

theorem cell22_1685149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1685149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685149 prefixEnd_1685149 := by exact prefixLift 1685149
  have htrace : WordTrace (prefixWord ++ tailWord_1685149) baseStart_1685149 baseEnd_1685149 := by
    simpa [prefixWord, tailWord_1685149, baseEnd_1685149] using wordTrace_append hprefix tailTrace_1685149
  have hstable : (prefixWord ++ tailWord_1685149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685149).length < 2 ^ (prefixWord ++ tailWord_1685149).sum := by decide
  have hdescent : baseEnd_1685149 < baseStart_1685149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685376 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 8]
def baseStart_1685376 : Nat := 118140960795 + 1685376 * 2 ^ 59
def prefixEnd_1685376 : Nat := 4983230072969 + 3 ^ 40 * 1685376 * 2
def baseEnd_1685376 : Nat := 192312882567134042744245

theorem tailTrace_1685376 : CollatzResearch.WordTrace tailWord_1685376 prefixEnd_1685376 192312882567134042744245 := by
  unfold tailWord_1685376
  simp only [CollatzResearch.WordTrace]
  refine ⟨30735356371089033074925991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40980475161452044099901321 30735356371089033074925991)
  ·
    refine ⟨46103034556633549612388987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30735356371089033074925991 46103034556633549612388987)
    ·
      refine ⟨69154551834950324418583481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46103034556633549612388987 69154551834950324418583481)
      ·
        refine ⟨51865913876212743313937611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69154551834950324418583481 51865913876212743313937611)
        ·
          refine ⟨77798870814319114970906417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51865913876212743313937611 77798870814319114970906417)
          ·
            refine ⟨58349153110739336228179813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77798870814319114970906417 58349153110739336228179813)
            ·
              refine ⟨10940466208263625542783715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58349153110739336228179813 10940466208263625542783715)
              ·
                refine ⟨16410699312395438314175573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10940466208263625542783715 16410699312395438314175573)
                ·
                  refine ⟨192312882567134042744245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16410699312395438314175573 192312882567134042744245)
                  ·
                    rfl

theorem cell22_1685376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_1685376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685376 prefixEnd_1685376 := by exact prefixLift 1685376
  have htrace : WordTrace (prefixWord ++ tailWord_1685376) baseStart_1685376 baseEnd_1685376 := by
    simpa [prefixWord, tailWord_1685376, baseEnd_1685376] using wordTrace_append hprefix tailTrace_1685376
  have hstable : (prefixWord ++ tailWord_1685376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685376).length < 2 ^ (prefixWord ++ tailWord_1685376).sum := by decide
  have hdescent : baseEnd_1685376 < baseStart_1685376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685425 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 1, 5]
def baseStart_1685425 : Nat := 118140960795 + 1685425 * 2 ^ 59
def prefixEnd_1685425 : Nat := 4983230072969 + 3 ^ 40 * 1685425 * 2
def baseEnd_1685425 : Nat := 576955421402782333757585

theorem tailTrace_1685425 : CollatzResearch.WordTrace tailWord_1685425 prefixEnd_1685425 576955421402782333757585 := by
  unfold tailWord_1685425
  simp only [CollatzResearch.WordTrace]
  refine ⟨61472499919000547518385729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40981666612667031678923819 61472499919000547518385729)
  ·
    refine ⟨46104374939250410638789297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61472499919000547518385729 46104374939250410638789297)
    ·
      refine ⟨34578281204437807979091973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46104374939250410638789297 34578281204437807979091973)
      ·
        refine ⟨6483427725832088996079745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34578281204437807979091973 6483427725832088996079745)
        ·
          refine ⟨4862570794374066747059809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6483427725832088996079745 4862570794374066747059809)
          ·
            refine ⟨3646928095780550060294857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4862570794374066747059809 3646928095780550060294857)
            ·
              refine ⟨2735196071835412545221143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3646928095780550060294857 2735196071835412545221143)
              ·
                refine ⟨4102794107753118817831715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2735196071835412545221143 4102794107753118817831715)
                ·
                  refine ⟨6154191161629678226747573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4102794107753118817831715 6154191161629678226747573)
                  ·
                    refine ⟨576955421402782333757585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6154191161629678226747573 576955421402782333757585)
                    ·
                      rfl

theorem cell22_1685425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_1685425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685425 prefixEnd_1685425 := by exact prefixLift 1685425
  have htrace : WordTrace (prefixWord ++ tailWord_1685425) baseStart_1685425 baseEnd_1685425 := by
    simpa [prefixWord, tailWord_1685425, baseEnd_1685425] using wordTrace_append hprefix tailTrace_1685425
  have hstable : (prefixWord ++ tailWord_1685425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685425).length < 2 ^ (prefixWord ++ tailWord_1685425).sum := by decide
  have hdescent : baseEnd_1685425 < baseStart_1685425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685483 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 5]
def baseStart_1685483 : Nat := 118140960795 + 1685483 * 2 ^ 59
def prefixEnd_1685483 : Nat := 4983230072969 + 3 ^ 40 * 1685483 * 2
def baseEnd_1685483 : Nat := 192325091996029838602469

theorem tailTrace_1685483 : CollatzResearch.WordTrace tailWord_1685483 prefixEnd_1685483 192325091996029838602469 := by
  unfold tailWord_1685483
  simp only [CollatzResearch.WordTrace]
  refine ⟨61474615352790423423997103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40983076901860282282664735 61474615352790423423997103)
  ·
    refine ⟨92211923029185635135995655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61474615352790423423997103 92211923029185635135995655)
    ·
      refine ⟨138317884543778452703993483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92211923029185635135995655 138317884543778452703993483)
      ·
        refine ⟨207476826815667679055990225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138317884543778452703993483 207476826815667679055990225)
        ·
          refine ⟨155607620111750759291992669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207476826815667679055990225 155607620111750759291992669)
          ·
            refine ⟨58352857541906534734497251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155607620111750759291992669 58352857541906534734497251)
            ·
              refine ⟨87529286312859802101745877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58352857541906534734497251 87529286312859802101745877)
              ·
                refine ⟨2051467647957651611759669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 87529286312859802101745877 2051467647957651611759669)
                ·
                  refine ⟨192325091996029838602469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2051467647957651611759669 192325091996029838602469)
                  ·
                    rfl

theorem cell22_1685483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 5].length) (baseStart_1685483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685483 prefixEnd_1685483 := by exact prefixLift 1685483
  have htrace : WordTrace (prefixWord ++ tailWord_1685483) baseStart_1685483 baseEnd_1685483 := by
    simpa [prefixWord, tailWord_1685483, baseEnd_1685483] using wordTrace_append hprefix tailTrace_1685483
  have hstable : (prefixWord ++ tailWord_1685483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685483).length < 2 ^ (prefixWord ++ tailWord_1685483).sum := by decide
  have hdescent : baseEnd_1685483 < baseStart_1685483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685513 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 7, 4]
def baseStart_1685513 : Nat := 118140960795 + 1685513 * 2 ^ 59
def prefixEnd_1685513 : Nat := 4983230072969 + 3 ^ 40 * 1685513 * 2
def baseEnd_1685513 : Nat := 576985545601179437557315

theorem tailTrace_1685513 : CollatzResearch.WordTrace tailWord_1685513 prefixEnd_1685513 576985545601179437557315 := by
  unfold tailWord_1685513
  simp only [CollatzResearch.WordTrace]
  refine ⟨61475709542681738547589193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40983806361787825698392795 61475709542681738547589193)
  ·
    refine ⟨46106782157011303910691895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61475709542681738547589193 46106782157011303910691895)
    ·
      refine ⟨69160173235516955866037843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46106782157011303910691895 69160173235516955866037843)
      ·
        refine ⟨103740259853275433799056765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69160173235516955866037843 103740259853275433799056765)
        ·
          refine ⟨38902597444978287674646287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103740259853275433799056765 38902597444978287674646287)
          ·
            refine ⟨58353896167467431511969431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38902597444978287674646287 58353896167467431511969431)
            ·
              refine ⟨87530844251201147267954147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58353896167467431511969431 87530844251201147267954147)
              ·
                refine ⟨131296266376801720901931221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87530844251201147267954147 131296266376801720901931221)
                ·
                  refine ⟨3077256243206290333639013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 131296266376801720901931221 3077256243206290333639013)
                  ·
                    refine ⟨576985545601179437557315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3077256243206290333639013 576985545601179437557315)
                    ·
                      rfl

theorem cell22_1685513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_1685513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685513 prefixEnd_1685513 := by exact prefixLift 1685513
  have htrace : WordTrace (prefixWord ++ tailWord_1685513) baseStart_1685513 baseEnd_1685513 := by
    simpa [prefixWord, tailWord_1685513, baseEnd_1685513] using wordTrace_append hprefix tailTrace_1685513
  have hstable : (prefixWord ++ tailWord_1685513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685513).length < 2 ^ (prefixWord ++ tailWord_1685513).sum := by decide
  have hdescent : baseEnd_1685513 < baseStart_1685513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685575 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 2, 4]
def baseStart_1685575 : Nat := 118140960795 + 1685575 * 2 ^ 59
def prefixEnd_1685575 : Nat := 4983230072969 + 3 ^ 40 * 1685575 * 2
def baseEnd_1685575 : Nat := 577006769468231942507125

theorem tailTrace_1685575 : CollatzResearch.WordTrace tailWord_1685575 prefixEnd_1685575 577006769468231942507125 := by
  unfold tailWord_1685575
  simp only [CollatzResearch.WordTrace]
  refine ⟨61477970868457123136346179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40985313912304748757564119 61477970868457123136346179)
  ·
    refine ⟨92216956302685684704519269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61477970868457123136346179 92216956302685684704519269)
    ·
      refine ⟨17290679306753565882097363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92216956302685684704519269 17290679306753565882097363)
      ·
        refine ⟨25936018960130348823146045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17290679306753565882097363 25936018960130348823146045)
        ·
          refine ⟨9726007110048880808679767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25936018960130348823146045 9726007110048880808679767)
          ·
            refine ⟨14589010665073321213019651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9726007110048880808679767 14589010665073321213019651)
            ·
              refine ⟨21883515997609981819529477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14589010665073321213019651 21883515997609981819529477)
              ·
                refine ⟨4103159249551871591161777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21883515997609981819529477 4103159249551871591161777)
                ·
                  refine ⟨3077369437163903693371333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4103159249551871591161777 3077369437163903693371333)
                  ·
                    refine ⟨577006769468231942507125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3077369437163903693371333 577006769468231942507125)
                    ·
                      rfl

theorem cell22_1685575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_1685575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685575 prefixEnd_1685575 := by exact prefixLift 1685575
  have htrace : WordTrace (prefixWord ++ tailWord_1685575) baseStart_1685575 baseEnd_1685575 := by
    simpa [prefixWord, tailWord_1685575, baseEnd_1685575] using wordTrace_append hprefix tailTrace_1685575
  have hstable : (prefixWord ++ tailWord_1685575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685575).length < 2 ^ (prefixWord ++ tailWord_1685575).sum := by decide
  have hdescent : baseEnd_1685575 < baseStart_1685575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685577 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 2, 3]
def baseStart_1685577 : Nat := 118140960795 + 1685577 * 2 ^ 59
def prefixEnd_1685577 : Nat := 4983230072969 + 3 ^ 40 * 1685577 * 2
def baseEnd_1685577 : Nat := 577007454109104603957119

theorem tailTrace_1685577 : CollatzResearch.WordTrace tailWord_1685577 prefixEnd_1685577 577007454109104603957119 := by
  unfold tailWord_1685577
  simp only [CollatzResearch.WordTrace]
  refine ⟨61478043814449877477918985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40985362542966584985279323 61478043814449877477918985)
  ·
    refine ⟨46108532860837408108439239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61478043814449877477918985 46108532860837408108439239)
    ·
      refine ⟨69162799291256112162658859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46108532860837408108439239 69162799291256112162658859)
      ·
        refine ⟨103744198936884168243988289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69162799291256112162658859 103744198936884168243988289)
        ·
          refine ⟨77808149202663126182991217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103744198936884168243988289 77808149202663126182991217)
          ·
            refine ⟨58356111901997344637243413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77808149202663126182991217 58356111901997344637243413)
            ·
              refine ⟨2735442745406125529870785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58356111901997344637243413 2735442745406125529870785)
              ·
                refine ⟨2051582059054594147403089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2735442745406125529870785 2051582059054594147403089)
                ·
                  refine ⟨1538686544290945610552317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2051582059054594147403089 1538686544290945610552317)
                  ·
                    refine ⟨577007454109104603957119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1538686544290945610552317 577007454109104603957119)
                    ·
                      rfl

theorem cell22_1685577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 3].length) (baseStart_1685577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685577 prefixEnd_1685577 := by exact prefixLift 1685577
  have htrace : WordTrace (prefixWord ++ tailWord_1685577) baseStart_1685577 baseEnd_1685577 := by
    simpa [prefixWord, tailWord_1685577, baseEnd_1685577] using wordTrace_append hprefix tailTrace_1685577
  have hstable : (prefixWord ++ tailWord_1685577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685577).length < 2 ^ (prefixWord ++ tailWord_1685577).sum := by decide
  have hdescent : baseEnd_1685577 < baseStart_1685577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685635 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 7]
def baseStart_1685635 : Nat := 118140960795 + 1685635 * 2 ^ 59
def prefixEnd_1685635 : Nat := 4983230072969 + 3 ^ 40 * 1685635 * 2
def baseEnd_1685635 : Nat := 192342436231470595335647

theorem tailTrace_1685635 : CollatzResearch.WordTrace tailWord_1685635 prefixEnd_1685635 192342436231470595335647 := by
  unfold tailWord_1685635
  simp only [CollatzResearch.WordTrace]
  refine ⟨61480159248239753383530359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40986772832159835589020239 61480159248239753383530359)
  ·
    refine ⟨92220238872359630075295539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61480159248239753383530359 92220238872359630075295539)
    ·
      refine ⟨138330358308539445112943309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92220238872359630075295539 138330358308539445112943309)
      ·
        refine ⟨51873884365702291917353741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138330358308539445112943309 51873884365702291917353741)
        ·
          refine ⟨19452706637138359469007653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51873884365702291917353741 19452706637138359469007653)
          ·
            refine ⟨3647382494463442400438935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19452706637138359469007653 3647382494463442400438935)
            ·
              refine ⟨5471073741695163600658403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3647382494463442400438935 5471073741695163600658403)
              ·
                refine ⟨8206610612542745400987605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471073741695163600658403 8206610612542745400987605)
                ·
                  refine ⟨192342436231470595335647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8206610612542745400987605 192342436231470595335647)
                  ·
                    rfl

theorem cell22_1685635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 7].length) (baseStart_1685635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685635 prefixEnd_1685635 := by exact prefixLift 1685635
  have htrace : WordTrace (prefixWord ++ tailWord_1685635) baseStart_1685635 baseEnd_1685635 := by
    simpa [prefixWord, tailWord_1685635, baseEnd_1685635] using wordTrace_append hprefix tailTrace_1685635
  have hstable : (prefixWord ++ tailWord_1685635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685635).length < 2 ^ (prefixWord ++ tailWord_1685635).sum := by decide
  have hdescent : baseEnd_1685635 < baseStart_1685635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685639 : List Nat := [1, 1, 4, 2, 1, 1, 4, 4, 1, 3]
def baseStart_1685639 : Nat := 118140960795 + 1685639 * 2 ^ 59
def prefixEnd_1685639 : Nat := 4983230072969 + 3 ^ 40 * 1685639 * 2
def baseEnd_1685639 : Nat := 577028677976157108906929

theorem tailTrace_1685639 : CollatzResearch.WordTrace tailWord_1685639 prefixEnd_1685639 577028677976157108906929 := by
  unfold tailWord_1685639
  simp only [CollatzResearch.WordTrace]
  refine ⟨61480305140225262066675971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40986870093483508044450647 61480305140225262066675971)
  ·
    refine ⟨92220457710337893100013957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61480305140225262066675971 92220457710337893100013957)
    ·
      refine ⟨17291335820688354956252617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92220457710337893100013957 17291335820688354956252617)
      ·
        refine ⟨12968501865516266217189463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17291335820688354956252617 12968501865516266217189463)
        ·
          refine ⟨19452752798274399325784195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12968501865516266217189463 19452752798274399325784195)
          ·
            refine ⟨29179129197411598988676293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19452752798274399325784195 29179129197411598988676293)
            ·
              refine ⟨5471086724514674810376805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29179129197411598988676293 5471086724514674810376805)
              ·
                refine ⟨1025828760846501526945651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5471086724514674810376805 1025828760846501526945651)
                ·
                  refine ⟨1538743141269752290418477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025828760846501526945651 1538743141269752290418477)
                  ·
                    refine ⟨577028677976157108906929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1538743141269752290418477 577028677976157108906929)
                    ·
                      rfl

theorem cell22_1685639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_1685639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685639 prefixEnd_1685639 := by exact prefixLift 1685639
  have htrace : WordTrace (prefixWord ++ tailWord_1685639) baseStart_1685639 baseEnd_1685639 := by
    simpa [prefixWord, tailWord_1685639, baseEnd_1685639] using wordTrace_append hprefix tailTrace_1685639
  have hstable : (prefixWord ++ tailWord_1685639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685639).length < 2 ^ (prefixWord ++ tailWord_1685639).sum := by decide
  have hdescent : baseEnd_1685639 < baseStart_1685639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685682 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_1685682 : Nat := 118140960795 + 1685682 * 2 ^ 59
def prefixEnd_1685682 : Nat := 4983230072969 + 3 ^ 40 * 1685682 * 2
def baseEnd_1685682 : Nat := 577043397754919330081797

theorem tailTrace_1685682 : CollatzResearch.WordTrace tailWord_1685682 prefixEnd_1685682 577043397754919330081797 := by
  unfold tailWord_1685682
  simp only [CollatzResearch.WordTrace]
  refine ⟨15370468369767370102622825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40987915652712986940327533 15370468369767370102622825)
  ·
    refine ⟨11527851277325527576967119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15370468369767370102622825 11527851277325527576967119)
    ·
      refine ⟨17291776915988291365450679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11527851277325527576967119 17291776915988291365450679)
      ·
        refine ⟨25937665373982437048176019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17291776915988291365450679 25937665373982437048176019)
        ·
          refine ⟨38906498060973655572264029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25937665373982437048176019 38906498060973655572264029)
          ·
            refine ⟨14589936772865120839599011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38906498060973655572264029 14589936772865120839599011)
            ·
              refine ⟨21884905159297681259398517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14589936772865120839599011 21884905159297681259398517)
              ·
                refine ⟨2051709858684157618068611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21884905159297681259398517 2051709858684157618068611)
                ·
                  refine ⟨3077564788026236427102917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051709858684157618068611 3077564788026236427102917)
                  ·
                    refine ⟨577043397754919330081797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3077564788026236427102917 577043397754919330081797)
                    ·
                      rfl

theorem cell22_1685682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_1685682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685682 prefixEnd_1685682 := by exact prefixLift 1685682
  have htrace : WordTrace (prefixWord ++ tailWord_1685682) baseStart_1685682 baseEnd_1685682 := by
    simpa [prefixWord, tailWord_1685682, baseEnd_1685682] using wordTrace_append hprefix tailTrace_1685682
  have hstable : (prefixWord ++ tailWord_1685682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685682).length < 2 ^ (prefixWord ++ tailWord_1685682).sum := by decide
  have hdescent : baseEnd_1685682 < baseStart_1685682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685746 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_1685746 : Nat := 118140960795 + 1685746 * 2 ^ 59
def prefixEnd_1685746 : Nat := 4983230072969 + 3 ^ 40 * 1685746 * 2
def baseEnd_1685746 : Nat := 577065306262844496481601

theorem tailTrace_1685746 : CollatzResearch.WordTrace tailWord_1685746 prefixEnd_1685746 577065306262844496481601 := by
  unfold tailWord_1685746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15371051937709404835205273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40989471833891746227214061 15371051937709404835205273)
  ·
    refine ⟨11528288953282053626403955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15371051937709404835205273 11528288953282053626403955)
    ·
      refine ⟨17292433429923080439605933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11528288953282053626403955 17292433429923080439605933)
      ·
        refine ⟨6484662536221155164852225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17292433429923080439605933 6484662536221155164852225)
        ·
          refine ⟨4863496902165866373639169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6484662536221155164852225 4863496902165866373639169)
          ·
            refine ⟨3647622676624399780229377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4863496902165866373639169 3647622676624399780229377)
            ·
              refine ⟨2735717007468299835172033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3647622676624399780229377 2735717007468299835172033)
              ·
                refine ⟨2051787755601224876379025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2735717007468299835172033 2051787755601224876379025)
                ·
                  refine ⟨1538840816700918657284269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2051787755601224876379025 1538840816700918657284269)
                  ·
                    refine ⟨577065306262844496481601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1538840816700918657284269 577065306262844496481601)
                    ·
                      rfl

theorem cell22_1685746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_1685746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685746 prefixEnd_1685746 := by exact prefixLift 1685746
  have htrace : WordTrace (prefixWord ++ tailWord_1685746) baseStart_1685746 baseEnd_1685746 := by
    simpa [prefixWord, tailWord_1685746, baseEnd_1685746] using wordTrace_append hprefix tailTrace_1685746
  have hstable : (prefixWord ++ tailWord_1685746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685746).length < 2 ^ (prefixWord ++ tailWord_1685746).sum := by decide
  have hdescent : baseEnd_1685746 < baseStart_1685746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685757 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_1685757 : Nat := 118140960795 + 1685757 * 2 ^ 59
def prefixEnd_1685757 : Nat := 4983230072969 + 3 ^ 40 * 1685757 * 2
def baseEnd_1685757 : Nat := 577069071787644134456567

theorem tailTrace_1685757 : CollatzResearch.WordTrace tailWord_1685757 prefixEnd_1685757 577069071787644134456567 := by
  unfold tailWord_1685757
  simp only [CollatzResearch.WordTrace]
  refine ⟨61484608953797768219471525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40989739302531845479647683 61484608953797768219471525)
  ·
    refine ⟨11528364178837081541150911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61484608953797768219471525 11528364178837081541150911)
    ·
      refine ⟨17292546268255622311726367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11528364178837081541150911 17292546268255622311726367)
      ·
        refine ⟨25938819402383433467589551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17292546268255622311726367 25938819402383433467589551)
        ·
          refine ⟨38908229103575150201384327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25938819402383433467589551 38908229103575150201384327)
          ·
            refine ⟨58362343655362725302076491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38908229103575150201384327 58362343655362725302076491)
            ·
              refine ⟨87543515483044087953114737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58362343655362725302076491 87543515483044087953114737)
              ·
                refine ⟨65657636612283065964836053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87543515483044087953114737 65657636612283065964836053)
                ·
                  refine ⟨1538850858100384358550845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 65657636612283065964836053 1538850858100384358550845)
                  ·
                    refine ⟨577069071787644134456567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1538850858100384358550845 577069071787644134456567)
                    ·
                      rfl

theorem cell22_1685757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_1685757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685757 prefixEnd_1685757 := by exact prefixLift 1685757
  have htrace : WordTrace (prefixWord ++ tailWord_1685757) baseStart_1685757 baseEnd_1685757 := by
    simpa [prefixWord, tailWord_1685757, baseEnd_1685757] using wordTrace_append hprefix tailTrace_1685757
  have hstable : (prefixWord ++ tailWord_1685757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685757).length < 2 ^ (prefixWord ++ tailWord_1685757).sum := by decide
  have hdescent : baseEnd_1685757 < baseStart_1685757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685774 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_1685774 : Nat := 118140960795 + 1685774 * 2 ^ 59
def prefixEnd_1685774 : Nat := 4983230072969 + 3 ^ 40 * 1685774 * 2
def baseEnd_1685774 : Nat := 577074891235061756781515

theorem tailTrace_1685774 : CollatzResearch.WordTrace tailWord_1685774 prefixEnd_1685774 577074891235061756781515 := by
  unfold tailWord_1685774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685653624342022515355047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40990152663157453415226917 7685653624342022515355047)
  ·
    refine ⟨11528480436513033773032571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7685653624342022515355047 11528480436513033773032571)
    ·
      refine ⟨17292720654769550659548857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11528480436513033773032571 17292720654769550659548857)
      ·
        refine ⟨12969540491077162994661643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17292720654769550659548857 12969540491077162994661643)
        ·
          refine ⟨19454310736615744491992465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12969540491077162994661643 19454310736615744491992465)
          ·
            refine ⟨14590733052461808368994349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19454310736615744491992465 14590733052461808368994349)
            ·
              refine ⟨5471524894673178138372881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14590733052461808368994349 5471524894673178138372881)
              ·
                refine ⟨4103643671004883603779661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5471524894673178138372881 4103643671004883603779661)
                ·
                  refine ⟨1538866376626831351417373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4103643671004883603779661 1538866376626831351417373)
                  ·
                    refine ⟨577074891235061756781515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1538866376626831351417373 577074891235061756781515)
                    ·
                      rfl

theorem cell22_1685774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_1685774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685774 prefixEnd_1685774 := by exact prefixLift 1685774
  have htrace : WordTrace (prefixWord ++ tailWord_1685774) baseStart_1685774 baseEnd_1685774 := by
    simpa [prefixWord, tailWord_1685774, baseEnd_1685774] using wordTrace_append hprefix tailTrace_1685774
  have hstable : (prefixWord ++ tailWord_1685774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685774).length < 2 ^ (prefixWord ++ tailWord_1685774).sum := by decide
  have hdescent : baseEnd_1685774 < baseStart_1685774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685791 : List Nat := [1, 1, 2, 4, 3, 1, 1, 5, 1, 3]
def baseStart_1685791 : Nat := 118140960795 + 1685791 * 2 ^ 59
def prefixEnd_1685791 : Nat := 4983230072969 + 3 ^ 40 * 1685791 * 2
def baseEnd_1685791 : Nat := 577080710682479379106463

theorem tailTrace_1685791 : CollatzResearch.WordTrace tailWord_1685791 prefixEnd_1685791 577080710682479379106463 := by
  unfold tailWord_1685791
  simp only [CollatzResearch.WordTrace]
  refine ⟨61485849035674592026209227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40990566023783061350806151 61485849035674592026209227)
  ·
    refine ⟨92228773553511888039313841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61485849035674592026209227 92228773553511888039313841)
    ·
      refine ⟨69171580165133916029485381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92228773553511888039313841 69171580165133916029485381)
      ·
        refine ⟨12969671280962609255528509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69171580165133916029485381 12969671280962609255528509)
        ·
          refine ⟨4863626730360978470823191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12969671280962609255528509 4863626730360978470823191)
          ·
            refine ⟨7295440095541467706234787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4863626730360978470823191 7295440095541467706234787)
            ·
              refine ⟨10943160143312201559352181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7295440095541467706234787 10943160143312201559352181)
              ·
                refine ⟨1025921263435518896189267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10943160143312201559352181 1025921263435518896189267)
                ·
                  refine ⟨1538881895153278344283901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025921263435518896189267 1538881895153278344283901)
                  ·
                    refine ⟨577080710682479379106463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1538881895153278344283901 577080710682479379106463)
                    ·
                      rfl

theorem cell22_1685791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 1, 3].length) (baseStart_1685791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685791 prefixEnd_1685791 := by exact prefixLift 1685791
  have htrace : WordTrace (prefixWord ++ tailWord_1685791) baseStart_1685791 baseEnd_1685791 := by
    simpa [prefixWord, tailWord_1685791, baseEnd_1685791] using wordTrace_append hprefix tailTrace_1685791
  have hstable : (prefixWord ++ tailWord_1685791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685791).length < 2 ^ (prefixWord ++ tailWord_1685791).sum := by decide
  have hdescent : baseEnd_1685791 < baseStart_1685791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685832 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 6]
def baseStart_1685832 : Nat := 118140960795 + 1685832 * 2 ^ 59
def prefixEnd_1685832 : Nat := 4983230072969 + 3 ^ 40 * 1685832 * 2
def baseEnd_1685832 : Nat := 192364915273456312943779

theorem tailTrace_1685832 : CollatzResearch.WordTrace tailWord_1685832 prefixEnd_1685832 192364915273456312943779 := by
  unfold tailWord_1685832
  simp only [CollatzResearch.WordTrace]
  refine ⟨30743672214263028014225875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40991562952350704018967833 30743672214263028014225875)
  ·
    refine ⟨46115508321394542021338813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30743672214263028014225875 46115508321394542021338813)
    ·
      refine ⟨17293315620522953258002055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46115508321394542021338813 17293315620522953258002055)
      ·
        refine ⟨25939973430784429887003083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17293315620522953258002055 25939973430784429887003083)
        ·
          refine ⟨38909960146176644830504625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25939973430784429887003083 38909960146176644830504625)
          ·
            refine ⟨29182470109632483622878469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38909960146176644830504625 29182470109632483622878469)
            ·
              refine ⟨5471713145556090679289713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29182470109632483622878469 5471713145556090679289713)
              ·
                refine ⟨4103784859167068009467285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5471713145556090679289713 4103784859167068009467285)
                ·
                  refine ⟨192364915273456312943779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4103784859167068009467285 192364915273456312943779)
                  ·
                    rfl

theorem cell22_1685832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_1685832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685832 prefixEnd_1685832 := by exact prefixLift 1685832
  have htrace : WordTrace (prefixWord ++ tailWord_1685832) baseStart_1685832 baseEnd_1685832 := by
    simpa [prefixWord, tailWord_1685832, baseEnd_1685832] using wordTrace_append hprefix tailTrace_1685832
  have hstable : (prefixWord ++ tailWord_1685832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685832).length < 2 ^ (prefixWord ++ tailWord_1685832).sum := by decide
  have hdescent : baseEnd_1685832 < baseStart_1685832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685847 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 3, 5]
def baseStart_1685847 : Nat := 118140960795 + 1685847 * 2 ^ 59
def prefixEnd_1685847 : Nat := 4983230072969 + 3 ^ 40 * 1685847 * 2
def baseEnd_1685847 : Nat := 577099880626913899706291

theorem tailTrace_1685847 : CollatzResearch.WordTrace tailWord_1685847 prefixEnd_1685847 577099880626913899706291 := by
  unfold tailWord_1685847
  simp only [CollatzResearch.WordTrace]
  refine ⟨61487891523471713590247795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40991927682314475726831863 61487891523471713590247795)
  ·
    refine ⟨92231837285207570385371693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61487891523471713590247795 92231837285207570385371693)
    ·
      refine ⟨34586938981952838894514385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92231837285207570385371693 34586938981952838894514385)
      ·
        refine ⟨25940204236464629170885789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34586938981952838894514385 25940204236464629170885789)
        ·
          refine ⟨9727576588674235939082171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25940204236464629170885789 9727576588674235939082171)
          ·
            refine ⟨14591364883011353908623257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9727576588674235939082171 14591364883011353908623257)
            ·
              refine ⟨10943523662258515431467443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14591364883011353908623257 10943523662258515431467443)
              ·
                refine ⟨16415285493387773147201165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10943523662258515431467443 16415285493387773147201165)
                ·
                  refine ⟨6155732060020414930200437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16415285493387773147201165 6155732060020414930200437)
                  ·
                    refine ⟨577099880626913899706291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6155732060020414930200437 577099880626913899706291)
                    ·
                      rfl

theorem cell22_1685847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_1685847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685847 prefixEnd_1685847 := by exact prefixLift 1685847
  have htrace : WordTrace (prefixWord ++ tailWord_1685847) baseStart_1685847 baseEnd_1685847 := by
    simpa [prefixWord, tailWord_1685847, baseEnd_1685847] using wordTrace_append hprefix tailTrace_1685847
  have hstable : (prefixWord ++ tailWord_1685847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685847).length < 2 ^ (prefixWord ++ tailWord_1685847).sum := by decide
  have hdescent : baseEnd_1685847 < baseStart_1685847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685866 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 6]
def baseStart_1685866 : Nat := 118140960795 + 1685866 * 2 ^ 59
def prefixEnd_1685866 : Nat := 4983230072969 + 3 ^ 40 * 1685866 * 2
def baseEnd_1685866 : Nat := 192368794905068061160411

theorem tailTrace_1685866 : CollatzResearch.WordTrace tailWord_1685866 prefixEnd_1685866 192368794905068061160411 := by
  unfold tailWord_1685866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15372146127600719958797363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40992389673601919890126301 15372146127600719958797363)
  ·
    refine ⟨23058219191401079938196045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15372146127600719958797363 23058219191401079938196045)
    ·
      refine ⟨8646832196775404976823517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23058219191401079938196045 8646832196775404976823517)
      ·
        refine ⟨3242562073790776866308819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8646832196775404976823517 3242562073790776866308819)
        ·
          refine ⟨4863843110686165299463229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242562073790776866308819 4863843110686165299463229)
          ·
            refine ⟨1823941166507311987298711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4863843110686165299463229 1823941166507311987298711)
            ·
              refine ⟨2735911749760967980948067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823941166507311987298711 2735911749760967980948067)
              ·
                refine ⟨4103867624641451971422101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2735911749760967980948067 4103867624641451971422101)
                ·
                  refine ⟨192368794905068061160411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4103867624641451971422101 192368794905068061160411)
                  ·
                    rfl

theorem cell22_1685866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_1685866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685866 prefixEnd_1685866 := by exact prefixLift 1685866
  have htrace : WordTrace (prefixWord ++ tailWord_1685866) baseStart_1685866 baseEnd_1685866 := by
    simpa [prefixWord, tailWord_1685866, baseEnd_1685866] using wordTrace_append hprefix tailTrace_1685866
  have hstable : (prefixWord ++ tailWord_1685866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685866).length < 2 ^ (prefixWord ++ tailWord_1685866).sum := by decide
  have hdescent : baseEnd_1685866 < baseStart_1685866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685967 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 10]
def baseStart_1685967 : Nat := 118140960795 + 1685967 * 2 ^ 59
def prefixEnd_1685967 : Nat := 4983230072969 + 3 ^ 40 * 1685967 * 2
def baseEnd_1685967 : Nat := 192380319693091195568641

theorem tailTrace_1685967 : CollatzResearch.WordTrace tailWord_1685967 prefixEnd_1685967 192380319693091195568641 := by
  unfold tailWord_1685967
  simp only [CollatzResearch.WordTrace]
  refine ⟨61492268283036974084616155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40994845522024649389744103 61492268283036974084616155)
  ·
    refine ⟨92238402424555461126924233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61492268283036974084616155 92238402424555461126924233)
    ·
      refine ⟨69178801818416595845193175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92238402424555461126924233 69178801818416595845193175)
      ·
        refine ⟨103768202727624893767789763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69178801818416595845193175 103768202727624893767789763)
        ·
          refine ⟨155652304091437340651684645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103768202727624893767789763 155652304091437340651684645)
          ·
            refine ⟨29184807017144501372190871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155652304091437340651684645 29184807017144501372190871)
            ·
              refine ⟨43777210525716752058286307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29184807017144501372190871 43777210525716752058286307)
              ·
                refine ⟨65665815788575128087429461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43777210525716752058286307 65665815788575128087429461)
                ·
                  refine ⟨192380319693091195568641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 65665815788575128087429461 192380319693091195568641)
                  ·
                    rfl

theorem cell22_1685967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 10].length) (baseStart_1685967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685967 prefixEnd_1685967 := by exact prefixLift 1685967
  have htrace : WordTrace (prefixWord ++ tailWord_1685967) baseStart_1685967 baseEnd_1685967 := by
    simpa [prefixWord, tailWord_1685967, baseEnd_1685967] using wordTrace_append hprefix tailTrace_1685967
  have hstable : (prefixWord ++ tailWord_1685967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685967).length < 2 ^ (prefixWord ++ tailWord_1685967).sum := by decide
  have hdescent : baseEnd_1685967 < baseStart_1685967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685984 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 6]
def baseStart_1685984 : Nat := 118140960795 + 1685984 * 2 ^ 59
def prefixEnd_1685984 : Nat := 4983230072969 + 3 ^ 40 * 1685984 * 2
def baseEnd_1685984 : Nat := 192382259508897069676957

theorem tailTrace_1685984 : CollatzResearch.WordTrace tailWord_1685984 prefixEnd_1685984 192382259508897069676957 := by
  unfold tailWord_1685984
  simp only [CollatzResearch.WordTrace]
  refine ⟨30746444161987692993992503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40995258882650257325323337 30746444161987692993992503)
  ·
    refine ⟨46119666242981539490988755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30746444161987692993992503 46119666242981539490988755)
    ·
      refine ⟨69179499364472309236483133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46119666242981539490988755 69179499364472309236483133)
      ·
        refine ⟨25942312261677115963681175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69179499364472309236483133 25942312261677115963681175)
        ·
          refine ⟨38913468392515673945521763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25942312261677115963681175 38913468392515673945521763)
          ·
            refine ⟨58370202588773510918282645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38913468392515673945521763 58370202588773510918282645)
            ·
              refine ⟨2736103246348758324294499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58370202588773510918282645 2736103246348758324294499)
              ·
                refine ⟨4104154869523137486441749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2736103246348758324294499 4104154869523137486441749)
                ·
                  refine ⟨192382259508897069676957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4104154869523137486441749 192382259508897069676957)
                  ·
                    rfl

theorem cell22_1685984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_1685984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1685984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1685984 prefixEnd_1685984 := by exact prefixLift 1685984
  have htrace : WordTrace (prefixWord ++ tailWord_1685984) baseStart_1685984 baseEnd_1685984 := by
    simpa [prefixWord, tailWord_1685984, baseEnd_1685984] using wordTrace_append hprefix tailTrace_1685984
  have hstable : (prefixWord ++ tailWord_1685984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685984).length < 2 ^ (prefixWord ++ tailWord_1685984).sum := by decide
  have hdescent : baseEnd_1685984 < baseStart_1685984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686084 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1686084 : Nat := 118140960795 + 1686084 * 2 ^ 59
def prefixEnd_1686084 : Nat := 4983230072969 + 3 ^ 40 * 1686084 * 2
def baseEnd_1686084 : Nat := 577181010570324281530565

theorem tailTrace_1686084 : CollatzResearch.WordTrace tailWord_1686084 prefixEnd_1686084 577181010570324281530565 := by
  unfold tailWord_1686084
  simp only [CollatzResearch.WordTrace]
  refine ⟨30748267811806551533312653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40997690415742068711083537 30748267811806551533312653)
  ·
    refine ⟨11530600429427456824992245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30748267811806551533312653 11530600429427456824992245)
    ·
      refine ⟨1080993790258824077343023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11530600429427456824992245 1080993790258824077343023)
      ·
        refine ⟨1621490685388236116014535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080993790258824077343023 1621490685388236116014535)
        ·
          refine ⟨2432236028082354174021803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621490685388236116014535 2432236028082354174021803)
          ·
            refine ⟨3648354042123531261032705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432236028082354174021803 3648354042123531261032705)
            ·
              refine ⟨2736265531592648445774529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3648354042123531261032705 2736265531592648445774529)
              ·
                refine ⟨2052199148694486334330897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2736265531592648445774529 2052199148694486334330897)
                ·
                  refine ⟨1539149361520864750748173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2052199148694486334330897 1539149361520864750748173)
                  ·
                    refine ⟨577181010570324281530565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1539149361520864750748173 577181010570324281530565)
                    ·
                      rfl

theorem cell22_1686084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1686084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686084 prefixEnd_1686084 := by exact prefixLift 1686084
  have htrace : WordTrace (prefixWord ++ tailWord_1686084) baseStart_1686084 baseEnd_1686084 := by
    simpa [prefixWord, tailWord_1686084, baseEnd_1686084] using wordTrace_append hprefix tailTrace_1686084
  have hstable : (prefixWord ++ tailWord_1686084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686084).length < 2 ^ (prefixWord ++ tailWord_1686084).sum := by decide
  have hdescent : baseEnd_1686084 < baseStart_1686084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686095 : List Nat := [1, 1, 2, 1, 1, 2, 8, 2, 1, 3]
def baseStart_1686095 : Nat := 118140960795 + 1686095 * 2 ^ 59
def prefixEnd_1686095 : Nat := 4983230072969 + 3 ^ 40 * 1686095 * 2
def baseEnd_1686095 : Nat := 577184776095123919505531

theorem tailTrace_1686095 : CollatzResearch.WordTrace tailWord_1686095 prefixEnd_1686095 577184776095123919505531 := by
  unfold tailWord_1686095
  simp only [CollatzResearch.WordTrace]
  refine ⟨61496936826573251945275739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40997957884382167963517159 61496936826573251945275739)
  ·
    refine ⟨92245405239859877917913609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61496936826573251945275739 92245405239859877917913609)
    ·
      refine ⟨69184053929894908438435207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92245405239859877917913609 69184053929894908438435207)
      ·
        refine ⟨103776080894842362657652811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69184053929894908438435207 103776080894842362657652811)
        ·
          refine ⟨155664121342263543986479217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103776080894842362657652811 155664121342263543986479217)
          ·
            refine ⟨116748091006697657989859413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155664121342263543986479217 116748091006697657989859413)
            ·
              refine ⟨1368141691484738179568665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 116748091006697657989859413 1368141691484738179568665)
              ·
                refine ⟨1026106268613553634676499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368141691484738179568665 1026106268613553634676499)
                ·
                  refine ⟨1539159402920330452014749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026106268613553634676499 1539159402920330452014749)
                  ·
                    refine ⟨577184776095123919505531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1539159402920330452014749 577184776095123919505531)
                    ·
                      rfl

theorem cell22_1686095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 1, 3].length) (baseStart_1686095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686095 prefixEnd_1686095 := by exact prefixLift 1686095
  have htrace : WordTrace (prefixWord ++ tailWord_1686095) baseStart_1686095 baseEnd_1686095 := by
    simpa [prefixWord, tailWord_1686095, baseEnd_1686095] using wordTrace_append hprefix tailTrace_1686095
  have hstable : (prefixWord ++ tailWord_1686095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686095).length < 2 ^ (prefixWord ++ tailWord_1686095).sum := by decide
  have hdescent : baseEnd_1686095 < baseStart_1686095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686121 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 1, 4]
def baseStart_1686121 : Nat := 118140960795 + 1686121 * 2 ^ 59
def prefixEnd_1686121 : Nat := 4983230072969 + 3 ^ 40 * 1686121 * 2
def baseEnd_1686121 : Nat := 577193676426468518355451

theorem tailTrace_1686121 : CollatzResearch.WordTrace tailWord_1686121 prefixEnd_1686121 577193676426468518355451 := by
  unfold tailWord_1686121
  simp only [CollatzResearch.WordTrace]
  refine ⟨61497885124479058385722217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40998590082986038923814811 61497885124479058385722217)
  ·
    refine ⟨46123413843359293789291663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61497885124479058385722217 46123413843359293789291663)
    ·
      refine ⟨69185120765038940683937495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46123413843359293789291663 69185120765038940683937495)
      ·
        refine ⟨103777681147558411025906243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69185120765038940683937495 103777681147558411025906243)
        ·
          refine ⟨155666521721337616538859365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103777681147558411025906243 155666521721337616538859365)
          ·
            refine ⟨29187472822750803101036131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155666521721337616538859365 29187472822750803101036131)
            ·
              refine ⟨43781209234126204651554197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29187472822750803101036131 43781209234126204651554197)
              ·
                refine ⟨2052244182849665843041603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43781209234126204651554197 2052244182849665843041603)
                ·
                  refine ⟨3078366274274498764562405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052244182849665843041603 3078366274274498764562405)
                  ·
                    refine ⟨577193676426468518355451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3078366274274498764562405 577193676426468518355451)
                    ·
                      rfl

theorem cell22_1686121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_1686121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686121 prefixEnd_1686121 := by exact prefixLift 1686121
  have htrace : WordTrace (prefixWord ++ tailWord_1686121) baseStart_1686121 baseEnd_1686121 := by
    simpa [prefixWord, tailWord_1686121, baseEnd_1686121] using wordTrace_append hprefix tailTrace_1686121
  have hstable : (prefixWord ++ tailWord_1686121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686121).length < 2 ^ (prefixWord ++ tailWord_1686121).sum := by decide
  have hdescent : baseEnd_1686121 < baseStart_1686121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686271 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 6]
def baseStart_1686271 : Nat := 118140960795 + 1686271 * 2 ^ 59
def prefixEnd_1686271 : Nat := 4983230072969 + 3 ^ 40 * 1686271 * 2
def baseEnd_1686271 : Nat := 192415008163972709034997

theorem tailTrace_1686271 : CollatzResearch.WordTrace tailWord_1686271 prefixEnd_1686271 192415008163972709034997 := by
  unfold tailWord_1686271
  simp only [CollatzResearch.WordTrace]
  refine ⟨61503356073935634003682667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41002237382623756002455111 61503356073935634003682667)
  ·
    refine ⟨92255034110903451005524001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61503356073935634003682667 92255034110903451005524001)
    ·
      refine ⟨69191275583177588254143001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92255034110903451005524001 69191275583177588254143001)
      ·
        refine ⟨51893456687383191190607251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69191275583177588254143001 51893456687383191190607251)
        ·
          refine ⟨77840185031074786785910877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51893456687383191190607251 77840185031074786785910877)
          ·
            refine ⟨29190069386653045044716579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77840185031074786785910877 29190069386653045044716579)
            ·
              refine ⟨43785104079979567567074869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29190069386653045044716579 43785104079979567567074869)
              ·
                refine ⟨4104853507498084459413269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43785104079979567567074869 4104853507498084459413269)
                ·
                  refine ⟨192415008163972709034997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4104853507498084459413269 192415008163972709034997)
                  ·
                    rfl

theorem cell22_1686271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 6].length) (baseStart_1686271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686271 prefixEnd_1686271 := by exact prefixLift 1686271
  have htrace : WordTrace (prefixWord ++ tailWord_1686271) baseStart_1686271 baseEnd_1686271 := by
    simpa [prefixWord, tailWord_1686271, baseEnd_1686271] using wordTrace_append hprefix tailTrace_1686271
  have hstable : (prefixWord ++ tailWord_1686271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686271).length < 2 ^ (prefixWord ++ tailWord_1686271).sum := by decide
  have hdescent : baseEnd_1686271 < baseStart_1686271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686303 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 1, 5]
def baseStart_1686303 : Nat := 118140960795 + 1686303 * 2 ^ 59
def prefixEnd_1686303 : Nat := 4983230072969 + 3 ^ 40 * 1686303 * 2
def baseEnd_1686303 : Nat := 577255978745880710304893

theorem tailTrace_1686303 : CollatzResearch.WordTrace tailWord_1686303 prefixEnd_1686303 577255978745880710304893 := by
  unfold tailWord_1686303
  simp only [CollatzResearch.WordTrace]
  refine ⟨61504523209819703468847563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41003015473213135645898375 61504523209819703468847563)
  ·
    refine ⟨92256784814729555203271345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61504523209819703468847563 92256784814729555203271345)
    ·
      refine ⟨69192588611047166402453509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92256784814729555203271345 69192588611047166402453509)
      ·
        refine ⟨12973610364571343700460033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69192588611047166402453509 12973610364571343700460033)
        ·
          refine ⟨9730207773428507775345025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12973610364571343700460033 9730207773428507775345025)
          ·
            refine ⟨7297655830071380831508769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9730207773428507775345025 7297655830071380831508769)
            ·
              refine ⟨5473241872553535623631577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7297655830071380831508769 5473241872553535623631577)
              ·
                refine ⟨4104931404415151717723683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5473241872553535623631577 4104931404415151717723683)
                ·
                  refine ⟨6157397106622727576585525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104931404415151717723683 6157397106622727576585525)
                  ·
                    refine ⟨577255978745880710304893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6157397106622727576585525 577255978745880710304893)
                    ·
                      rfl

theorem cell22_1686303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_1686303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1686303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1686303 prefixEnd_1686303 := by exact prefixLift 1686303
  have htrace : WordTrace (prefixWord ++ tailWord_1686303) baseStart_1686303 baseEnd_1686303 := by
    simpa [prefixWord, tailWord_1686303, baseEnd_1686303] using wordTrace_append hprefix tailTrace_1686303
  have hstable : (prefixWord ++ tailWord_1686303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686303).length < 2 ^ (prefixWord ++ tailWord_1686303).sum := by decide
  have hdescent : baseEnd_1686303 < baseStart_1686303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
